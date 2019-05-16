(ns replete.prepl
  (:refer-clojure :exclude [resolve eval])
  (:require-macros [cljs.env.macros :refer [ensure with-compiler-env]]
                   [cljs.analyzer.macros :refer [no-warn]]
                   [replete.repl :refer [with-err-str]])
  (:require [replete.priv-repl :as priv]
            [clojure.string :as string]
            [cljs.repl :as repl]
            [cljs.js :as cljs]
            [cljs.analyzer :as ana]
            [cljs.env :as env]
            [cljs.tools.reader :as r]
            [cljs.tagged-literals :as tags]
            [replete.repl-resources :refer [special-doc-map repl-special-doc-map]]))

(defn- skip-load?
  [{:keys [name macros]}]
  (or (= name 'cljsjs.parinfer)
      (= name 'cljs.core)
      (= name 'cljs.env)
      (= name 'cljs.test.check)
      (= name 'cljs.test.check.clojure-test)
      (= name 'cljs.test.check.generators)
      (= name 'cljs.test.check.properties)
      (= name 'replete.repl)
      (and (= name 'cljs.compiler.macros) macros)
      (and (= name 'cljs.repl) macros)
      (and (= name 'cljs.js) macros)
      (and (= name 'cljs.reader) macros)
      (and (= name 'cljs.spec.alpha.macros) macros)
      (and (= name 'clojure.template) macros)
      (and (= name 'tailrecursion.cljson) macros)
      (and (= name 'lazy-map.core) macros)))

(defn- hack-macros
  [{:keys [name macros] :as full}]
  (cond
    (= name 'cljs.tools.reader.reader-types)
    (merge full {:extensions [".cljs" ".js"]})

    (= name 'cljs.stacktrace)
    (merge full {:extensions [".js" ".cljc"]})

    (= name 'cljs.analyzer.macros)
    (merge full {:extensions [".clj" ".cljc"]})

    (or (= name 'cljs.tools.reader.reader-types)
        (= name 'cljs.pprint)
        (= name 'cljs.spec.alpha)
        (= name 'cljs.spec.gen.alpha)
        (= name 'cljs.spec.test.alpha)
        (= name 'cljs.test))
    (merge full {:extensions
                 (if macros [".cljc"]
                            [".cljs" ".cljc" ".js"])})

    (or (= name 'clojure.test.check)
        (= name 'clojure.test.check.generators)
        (= name 'clojure.test.check.properties)
        (= name 'clojure.test.check.clojure-test)
        (= name 'cljs.analyzer)
        (= name 'cljs.analyzer.api)
        (= name 'cljs.tagged-literals))
    (merge full {:extensions [".cljc"]})

    :else
    (merge full {:extensions
                 (if macros
                   [".clj" ".cljc"]
                   [".cljs" ".cljc" ".js"])})))

(defn load [{:keys [name path] :as full} cb]
  (cond
    (skip-load? full)
    (cb {:lang :js :source ""})

    (re-matches #"^goog/.*" path)
    (priv/do-load-goog name cb)

    :else
    (loop [{:keys [name macros path extensions]} (hack-macros full)]
      (if extensions
        (when-not (priv/load-and-callback! name path (first extensions) macros cb)
          (recur (next extensions)))
        (cb nil)))))

(defn- process-in-ns
  [argument]
  (let [result-data (atom {})]
    (cljs/eval
      priv/st
      argument
      (priv/make-base-eval-opts)
      (fn [result]
        (if (:error result)
          (reset! result-data {:tag :err
                               :val (:error result)})
          (let [ns-name (:value result)]
            (if-not (symbol? ns-name)
              (reset! result-data {:tag :err
                                   :val "Argument to in-ns must be a symbol."})
              (if (some (partial = ns-name) (priv/known-namespaces))
                (do (reset! priv/current-ns ns-name)
                    (reset! result-data {:tag :ret
                                         :val ns-name}))
                (let [ns-form `(~'ns ~ns-name)]
                  (cljs/eval
                    priv/st
                    ns-form
                    (priv/make-base-eval-opts)
                    (fn [{e :error}]
                      (if e
                        (reset! result-data {:tag :err
                                             :val e})
                        (do (reset! priv/current-ns ns-name)
                            (reset! result-data {:tag :ret
                                                 :val ns-name}))))))))))))
    (merge @result-data {:ns @priv/current-ns})))

(defn- string-find-doc*
  [re-string-or-pattern]
  (let [re (re-pattern re-string-or-pattern)
        sym-docs (sort-by first
                          (mapcat (fn [ns]
                                    (map (juxt first (comp :doc second))
                                         (get-in @priv/st [::ana/namespaces ns :defs])))
                                  (priv/all-ns)))]
    (string/join (for [[sym doc] sym-docs
                       :when (and doc
                                  (name sym)
                                  (or (re-find re doc)
                                      (re-find re (name sym))))]
                   (priv/doc* sym priv/string-doc)))))

(defn- string-error
  ([error]
   (string-error error false))
  ([error include-stacktrace?]
   (if include-stacktrace?
     (let [error (or (.-cause error) error)]
       (str (.-message error) \newline (.-stack error)))
     (let [error (cond-> error
                         (-> (ex-data (ex-cause error)) (contains? :clojure.error/phase))
                         ex-cause)]
       (repl/error->str error)))))

(defn- string-pst*
  ([]
   (string-pst* '*e))
  ([expr]
   (try (cljs/eval priv/st
                   expr
                   (priv/make-base-eval-opts)
                   (fn [{:keys [value]}]
                     (when value
                       {:tag :err
                        :val (string-error value true)})))
        (catch js/Error e {:tag :err
                           :clojure.error/phase :execution
                           :val (str :caught e)}))))

(defn ^:export read-eval
  ([source]
   (read-eval source true))
  ([source expression?]
   (let [result {:tag :ret :form source :ns @priv/current-ns}]
     (binding [ana/*cljs-warning-handlers* (if expression?
                                             [priv/warning-handler]
                                             [ana/default-warning-handler])
               ana/*cljs-ns* @priv/current-ns
               env/*compiler* priv/st
               *ns* (create-ns @priv/current-ns)
               r/*data-readers* tags/*cljs-data-readers*
               r/resolve-symbol ana/resolve-symbol
               r/*alias-map* (priv/current-alias-map)]
       (try
         (let [expression-form (and expression? (priv/repl-read-string source))]
           (if (priv/repl-special? expression-form)
             (let [special-form (first expression-form)
                   argument (second expression-form)]
               (case special-form
                 in-ns (merge result (process-in-ns argument))
                 dir (merge result {:val (priv/string-dir argument)})
                 apropos (let [value (priv/apropos* argument)]
                           (priv/process-1-2-3 expression-form value)
                           (merge result {:val value}))
                 doc (merge result {:val (priv/doc* argument priv/string-doc)})
                 find-doc (merge result {:val (priv/string-find-doc argument)})
                 source (merge result {:val (priv/string-source argument)})
                 pst (merge result (if argument
                                     (string-pst* argument)
                                     (string-pst*)))))
             (let [eval-result (atom result)]
               (cljs/eval-str
                 priv/st
                 source
                 (if expression? source "File")             ;; Later
                 (merge
                   {:ns         @priv/current-ns
                    :load       priv/load
                    :eval       cljs/js-eval
                    :source-map false
                    :verbose    (:verbose @priv/app-env)}
                   (when (:checked-arrays @priv/app-env)
                     {:checked-arrays (:checked-arrays @priv/app-env)})
                   (when expression?
                     {:context       :expr
                      :def-emits-var true}))
                 (fn [{:keys [ns value error]}]
                   (if expression?
                     (when-not error
                       (priv/process-1-2-3 expression-form value)
                       (when (priv/def-form? expression-form)
                         (let [{:keys [ns name]} (meta value)]
                           (swap! priv/st assoc-in [::ana/namespaces ns
                                                  :defs name
                                                  ::repl-entered-source] source)))
                       (reset! priv/current-ns ns)
                       (reset! eval-result (merge result {:val value}))))
                   (when error
                     (set! *e error)
                     (reset! eval-result (merge result
                                                {:tag :err
                                                 :clojure.error/phase :execution
                                                 :val error})))))
               @eval-result)))
         (catch :default e
           (merge result {:tag :err
                          :clojure.error/phase :read-source
                          :val e})))))))
