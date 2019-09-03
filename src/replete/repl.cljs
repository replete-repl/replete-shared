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
            [tailrecursion.cljson :refer [cljson->clj]]
            [cljsjs.parinfer]
            [lazy-map.core :refer-macros [lazy-map]]
            [replete.pprint :as pprint]
            [replete.priv-repl :as pr]
            [replete.repl-resources :refer [special-doc-map repl-special-doc-map]]))

(defn- run-sync!
  "Like cljs.js/run-async!, but with the expectation that cb will be called
  synchronously within proc. When callbacks are done synchronously, run-async!
  ends up growing the stack as coll is processed, while this implementation
  employs recur."
  [proc coll break? cb]
  (loop [coll coll]
    (if (seq coll)
      (let [cb-val (atom nil)]
        (proc (first coll) #(reset! cb-val %))
        (if (break? @cb-val)
          (cb @cb-val)
          (recur (rest coll))))
      (cb nil))))

; Monkey-patch cljs.js/run-async! to instead be our more stack-efficient run-sync!
(set! cljs/run-async! run-sync!)

(defn ^:export setup-cljs-user []
  (js/eval "goog.provide('cljs.user')")
  (js/eval "goog.require('cljs.core')"))

(defn ^:export init-app-env [app-env]
  (set! *print-namespace-maps* true)
  (pr/load-core-analysis-caches true)
  (reset! pr/app-env (assoc (pr/map-keys keyword (cljs.core/js->clj app-env))
                                 :checked-arrays :warn)))

(defn ^:export format [text pos enter-pressed?]
  (let [formatted-text (:text (js->clj
                                ((if enter-pressed?
                                   js/parinfer.parenMode
                                   js/parinfer.indentMode)
                                  text (clj->js (pr/calc-x-line text pos 0)))
                                :keywordize-keys true))
        formatted-pos  (if enter-pressed?
                         (pr/first-non-space-pos-after formatted-text pos)
                         pos)]
    #js [formatted-text formatted-pos]))

(defn ^:export set-width [width]
  (swap! pr/app-env assoc :width width))

(defn ^:export all-vars []
  (->> (pr/all-ns)
       (mapcat #(map first (get-in @pr/st [::ana/namespaces % :defs])))
       (map name)
       into-array))

(defn ^:export chivorcam-referred []
  (boolean (get-in @pr/st [::ana/namespaces @pr/current-ns :use-macros 'defmacfn])))

(defn- pst*
  ([]
   (pst* '*e))
  ([expr]
   (try (cljs/eval pr/st
                   expr
                   (pr/make-base-eval-opts)
                   (fn [{:keys [value]}]
                     (when value
                       (pr/print-error value true))))
        (catch js/Error e (prn :caught e)))))

(defn ^:export read-eval-print
  ([source]
   (read-eval-print source true))
  ([source expression?]
   (pr/reset-show-indicator!)
   (binding [ana/*cljs-warning-handlers* (if expression?
                                           [pr/warning-handler]
                                           [ana/default-warning-handler])
             ana/*cljs-ns* @pr/current-ns
             env/*compiler* pr/st
             *ns* (create-ns @pr/current-ns)
             r/*data-readers* tags/*cljs-data-readers*
             r/resolve-symbol ana/resolve-symbol
             r/*alias-map* (pr/current-alias-map)]
     (try
       (let [expression-form (and expression? (pr/repl-read-string source))]
         (if (pr/repl-special? expression-form)
           (let [special-form (first expression-form)
                 argument (second expression-form)]
             (case special-form
               in-ns (pr/process-in-ns argument)
               dir (pr/dir* argument)
               apropos (let [value (pr/apropos* argument)]
                         (prn value)
                         (pr/process-1-2-3 expression-form value))
               doc (pr/doc* argument)
               find-doc (pr/find-doc* argument)
               source (pr/source* argument)
               pst (if argument
                     (pst* argument)
                     (pst*)))
             (when-not (#{'apropos} special-form)
               (prn nil)))
           (cljs/eval-str
             pr/st
             source
             (if expression? source "File")
             (merge
               {:ns         @pr/current-ns
                :load       pr/load
                :eval       cljs/js-eval
                :source-map false
                :verbose    (:verbose @pr/app-env)}
               (when (:checked-arrays @pr/app-env)
                 {:checked-arrays (:checked-arrays @pr/app-env)})
               (when expression?
                 {:context       :expr
                  :def-emits-var true}))
             (fn [{:keys [ns value error]}]
               (if expression?
                 (if-not error
                   (do
                     (let [out-str (with-out-str (pprint/pprint value {:width (or (:width @pr/app-env)
                                                                                  35)
                                                                       :ns    ns}))
                           out-str (subs out-str 0 (dec (count out-str)))]
                       (print out-str))
                     (pr/process-1-2-3 expression-form value)
                     (when (pr/def-form? expression-form)
                       (let [{:keys [ns name]} (meta value)]
                         (swap! pr/st assoc-in [::ana/namespaces ns :defs name ::pr/repl-entered-source] source)))
                     (reset! pr/current-ns ns)
                     nil)
                   (do
                     (set! *e error))))
               (when error
                 (pr/print-error error))))))
       (catch :default e
         (pr/print-error e))))))

