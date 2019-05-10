(ns replete.repl
  (:refer-clojure :exclude [resolve eval])
  (:require-macros [cljs.env.macros :refer [ensure with-compiler-env]]
                   [cljs.analyzer.macros :refer [no-warn]]
                   [replete.repl :refer [with-err-str]])
  (:require [cljs.js :as cljs]
            [cljs.pprint :refer [pprint]]
            [cljs.tagged-literals :as tags]
            [cljs.tools.reader :as r]
            [cljs.analyzer :as ana]
            [cljs.env :as env]
            [cljs.repl :as repl]
            [tailrecursion.cljson :refer [cljson->clj]]
            [cljsjs.parinfer]
            [lazy-map.core :refer-macros [lazy-map]]
            [replete.pprint :as pprint]
            [replete.priv-repl :as priv]
            [replete.repl-resources :refer [special-doc-map repl-special-doc-map]]))

;; These fns or data definitions are part of the existing public interface
(def ^:retain-public-interfaces app-env priv/app-env)
(def ^:retain-public-interfaces current-ns priv/current-ns)
(def ^:retain-public-interfaces st priv/st)
(def ^:retain-public-interfaces map-keys priv/map-keys)
(def ^:retain-public-interfaces user-interface-idiom-ipad? priv/user-interface-idiom-ipad?)
(def ^:retain-public-interfaces repl-read-string priv/repl-read-string)
(def ^:retain-public-interfaces calc-x-line priv/calc-x-line)
(def ^:retain-public-interfaces first-non-space-pos-after priv/first-non-space-pos-after)
(def ^:retain-public-interfaces load-core-analysis-caches priv/load-core-analysis-caches)
(def ^:retain-public-interfaces ns-form? priv/ns-form?)
(def ^:retain-public-interfaces reflow priv/reflow)
(def ^:retain-public-interfaces extension->lang priv/extension->lang)
(def ^:retain-public-interfaces load-and-callback! priv/load-and-callback!)
(def ^:retain-public-interfaces do-load-goog priv/do-load-goog)
(def ^:retain-public-interfaces load priv/load)
(def ^:retain-public-interfaces load-core-source-maps! priv/load-core-source-maps!)
(def ^:retain-public-interfaces unmunge-core-fn priv/unmunge-core-fn)
(def ^:retain-public-interfaces mapped-stacktrace-str priv/mapped-stacktrace-str)
(def ^:retain-public-interfaces print-error priv/print-error)


;; TODO check the meaning of ^:export with @Mike
;; These fns are marked for export in the existing public interface
;; I'm not sure what it means so I'm keeping it here pending advice

(defn ^:export setup-cljs-user []
  (js/eval "goog.provide('cljs.user')")
  (js/eval "goog.require('cljs.core')"))

(defn ^:export init-app-env [app-env]
  (set! *print-namespace-maps* true)
  (load-core-analysis-caches true)
  (reset! priv/app-env (assoc (map-keys keyword (cljs.core/js->clj app-env))
                                 :checked-arrays :warn)))

(defn ^:export format [text pos enter-pressed?]
  (let [formatted-text (:text (js->clj
                                ((if enter-pressed?
                                   js/parinfer.parenMode
                                   js/parinfer.indentMode)
                                  text (clj->js (priv/calc-x-line text pos 0)))
                                :keywordize-keys true))
        formatted-pos  (if enter-pressed?
                         (priv/first-non-space-pos-after formatted-text pos)
                         pos)]
    #js [formatted-text formatted-pos]))

(defn ^:export set-width [width]
  (swap! priv/app-env assoc :width width))

(defn ^:export all-vars []
  (->> (priv/all-ns)
       (mapcat #(map first (get-in @st [::ana/namespaces % :defs])))
       (map name)
       into-array))

(defn ^:export chivorcam-referred []
  (boolean (get-in @st [::ana/namespaces @priv/current-ns :use-macros 'defmacfn])))

(defn- dir*
  [nsname]
  (let [ns (priv/resolve-ns nsname)]
    (print
      (with-out-str
        (run! prn
              (distinct (sort (concat
                                (priv/public-syms ns)
                                (priv/public-syms (priv/add-macros-suffix ns))))))))))

(defn- print-doc
  [m]
  (print
    (with-out-str
      (repl/print-doc (update m :doc (if (user-interface-idiom-ipad?)
                                       identity
                                       reflow))))))

(defn- doc*
  [sym]
  (if-let [special-sym ('{&       fn
                          catch   try
                          finally try} sym)]
    (doc* special-sym)
    (cond

      (special-doc-map sym)
      (print-doc (priv/special-doc sym))

      (repl-special-doc-map sym)
      (print-doc (priv/repl-special-doc sym))

      (priv/get-namespace sym)
      (print-doc
        (select-keys (priv/get-namespace sym) [:name :doc]))

      (priv/get-var (priv/get-aenv) sym)
      (print-doc
        (let [var (priv/get-var (priv/get-aenv) sym)
              var (assoc var :forms (-> var :meta :forms second)
                             :arglists (-> var :meta :arglists second))
              m   (select-keys var
                               [:ns :name :doc :forms :arglists :macro :url])
              m   (update m :doc priv/undo-reader-conditional-whitespace-docstring)]
          (cond-> (update-in m [:name] name)
                  (:protocol-symbol var)
                  (assoc :protocol true
                         :methods
                         (->> (get-in var [:protocol-info :methods])
                              (map (fn [[fname sigs]]
                                     [fname {:doc      (:doc
                                                         (priv/get-var (priv/get-aenv)
                                                                  (symbol (str (:ns var)) (str fname))))
                                             :arglists (seq sigs)}]))
                              (into {})))))))))

(defn- find-doc*
  [re-string-or-pattern]
  (print
    (with-out-str
      (let [re       (re-pattern re-string-or-pattern)
            sym-docs (sort-by first
                              (mapcat (fn [ns]
                                        (map (juxt first (comp :doc second))
                                             (get-in @st [::ana/namespaces ns :defs])))
                                      (priv/all-ns)))]
        (doseq [[sym doc] sym-docs
                :when (and doc
                           (name sym)
                           (or (re-find re doc)
                               (re-find re (name sym))))]
          (doc* sym))))))

(defn- source*
  [sym]
  (println (or (priv/fetch-source (priv/get-var (priv/get-aenv) sym))
               "Source not found")))

(defn- pst*
  ([]
   (pst* '*e))
  ([expr]
   (try (cljs/eval st
                   expr
                   (priv/make-base-eval-opts)
                   (fn [{:keys [value]}]
                     (when value
                       (print-error value true))))
        (catch js/Error e (prn :caught e)))))

(defn ^:export read-eval-print
  ([source]
   (read-eval-print source true))
  ([source expression?]
   (priv/reset-show-indicator!)
   (binding [ana/*cljs-warning-handlers* (if expression?
                                           [priv/warning-handler]
                                           [ana/default-warning-handler])
             ana/*cljs-ns* @current-ns
             env/*compiler* st
             *ns* (create-ns @current-ns)
             r/*data-readers* tags/*cljs-data-readers*
             r/resolve-symbol ana/resolve-symbol
             r/*alias-map* (priv/current-alias-map)]
     (try
       (let [expression-form (and expression? (priv/repl-read-string source))]
         (if (priv/repl-special? expression-form)
           (let [special-form (first expression-form)
                 argument (second expression-form)]
             (case special-form
               in-ns (priv/process-in-ns argument)
               dir (dir* argument)
               apropos (let [value (priv/apropos* argument)]
                         (prn value)
                         (priv/process-1-2-3 expression-form value))
               doc (doc* argument)
               find-doc (find-doc* argument)
               source (source* argument)
               pst (if argument
                     (pst* argument)
                     (pst*)))
             (when-not (#{'apropos} special-form)
               (prn nil)))
           (cljs/eval-str
             st
             source
             (if expression? source "File")
             (merge
               {:ns             @current-ns
                :load           load
                :eval           cljs/js-eval
                :source-map     false
                :verbose        (:verbose @app-env)}
               (when (:checked-arrays @app-env)
                 {:checked-arrays (:checked-arrays @app-env)})
               (when expression?
                 {:context       :expr
                  :def-emits-var true}))
             (fn [{:keys [ns value error] :as ret}]
               (if expression?
                 (if-not error
                   (do
                     (let [out-str (with-out-str (pprint/pprint value {:width (or (:width @app-env)
                                                                                  35)
                                                                       :ns    ns}))
                           out-str (subs out-str 0 (dec (count out-str)))]
                       (print out-str))
                     (priv/process-1-2-3 expression-form value)
                     (when (priv/def-form? expression-form)
                       (let [{:keys [ns name]} (meta value)]
                         (swap! st assoc-in [::ana/namespaces ns :defs name ::repl-entered-source] source)))
                     (reset! current-ns ns)
                     nil)
                   (do
                     (set! *e error))))
               (when error
                 (print-error error))))))
       (catch :default e
         (print-error e))))))

