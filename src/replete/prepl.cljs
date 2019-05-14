(ns replete.prepl
  (:refer-clojure :exclude [resolve eval])
  (:require-macros [cljs.env.macros :refer [ensure with-compiler-env]]
                   [cljs.analyzer.macros :refer [no-warn]]
                   [replete.repl :refer [with-err-str]])
  (:require [replete.repl :as rr]
            [clojure.string :as string]
            [cljs.repl :as repl]
            [cljs.js :as cljs]
            [clojure.string :as s]
            [cljs.analyzer :as ana]
            [cljs.env :as env]
            [cljs.tools.reader :as r]
            [cljs.tagged-literals :as tags]
            [replete.repl-resources :refer [special-doc-map repl-special-doc-map]]
            [cljs.tools.reader.reader-types :as rt]))

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

;; Represents code for which the goog JS is already loaded
(defn- skip-load-goog-js?
  [name]
  ('#{goog.object
      goog.string
      goog.string.StringBuffer
      goog.math.Long} name))

(defn- closure-index
  []
  (let [paths-to-provides
        (map (fn [[_ path provides]]
               [path (map second
                          (re-seq #"'(.*?)'" provides))])
             (re-seq #"\ngoog\.addDependency\('(.*)', \[(.*?)\].*"
                     (js/REPLETE_LOAD "goog/deps.js")))]
    (into {}
          (for [[path provides] paths-to-provides
                provide provides]
            [(symbol provide) (str "goog/" (second (re-find #"(.*)\.js$" path)))]))))

(def ^:private closure-index-mem (memoize closure-index))

(defn- do-load-goog
  [name cb]
  (if (skip-load-goog-js? name)
    (cb {:lang   :js
         :source ""})
    (if-let [goog-path (get (closure-index-mem) name)]
      (when-not (rr/load-and-callback! name goog-path ".js" false cb)
        (cb nil))
      (cb nil))))

(defn load [{:keys [name path] :as full} cb]
  (cond
    (skip-load? full)
    (cb {:lang :js :source ""})

    (re-matches #"^goog/.*" path)
    (do-load-goog name cb)

    :else
    (loop [{:keys [name macros path extensions]} (hack-macros full)]
      (if extensions
        (when-not (rr/load-and-callback! name path (first extensions) macros cb)
          (recur (next extensions)))
        (cb nil)))))

(declare make-base-eval-opts)
(declare print-error)

(defn string-error
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

(defn- known-namespaces
  []
  (keys (:cljs.analyzer/namespaces @rr/st)))

;; Sync version
(defn- prepl-process-in-ns
  [argument]
  (let [result-data (atom {})]
    (cljs/eval
      rr/st
      argument
      (make-base-eval-opts)
      (fn [result]
        (if (:error result)
          (reset! result-data {:tag :err
                               :val (:error result)})
          (let [ns-name (:value result)]
            (if-not (symbol? ns-name)
              (reset! result-data {:tag :err
                                   :val "Argument to in-ns must be a symbol."})
              (if (some (partial = ns-name) (known-namespaces))
                (do (reset! rr/current-ns ns-name)
                    (reset! result-data {:tag :ret
                                         :val ns-name}))
                (let [ns-form `(~'ns ~ns-name)]
                  (cljs/eval
                    rr/st
                    ns-form
                    (make-base-eval-opts)
                    (fn [{e :error}]
                      (if e
                        (reset! result-data {:tag :err
                                             :val e})
                        (do (reset! rr/current-ns ns-name)
                            (reset! result-data {:tag :ret
                                                 :val ns-name}))))))))))))
    (merge @result-data {:ns @rr/current-ns})))

(defn- get-namespace
  "Gets the AST for a given namespace."
  [ns]
  {:pre [(symbol? ns)]}
  (get-in @rr/st [::ana/namespaces ns]))

(defn- ns-syms
  "Returns a sequence of the symbols in a namespace."
  ([ns]
   (ns-syms ns (constantly true)))
  ([ns pred]
   {:pre [(symbol? ns)]}
   (->> (rr/get-namespace ns)
        :defs
        (filter pred)
        (map key))))

(defn- public-syms
  "Returns a sequence of the public symbols in a namespace."
  [ns]
  {:pre [(symbol? ns)]}
  (ns-syms ns (fn [[_ attrs]]
                (and (not (:private attrs))
                     (not (:anonymous attrs))))))

(defn- resolve-ns
  "Resolves a namespace symbol to a namespace by first checking to see if it
  is a namespace alias."
  [ns-sym]
  (or (get-in @rr/st [::ana/namespaces ana/*cljs-ns* :requires ns-sym])
      (get-in @rr/st [::ana/namespaces ana/*cljs-ns* :require-macros ns-sym])
      ns-sym))

(defn- add-macros-suffix
  [sym]
  (symbol (str (name sym) "$macros")))

(defn- string-dir
  ([nsname]
   (let [ns (resolve-ns nsname)]
     (with-out-str
       (run! prn
             (distinct (sort (concat
                               (public-syms ns)
                               (public-syms (add-macros-suffix ns))))))))))

(defn- all-ns
  "Returns a sequence of all namespaces."
  []
  (keys (::ana/namespaces @rr/st)))

(defn- apropos*
  [str-or-pattern]
  (let [matches? (if (instance? js/RegExp str-or-pattern)
                   #(re-find str-or-pattern (str %))
                   #(s/includes? (str %) (str str-or-pattern)))]
    (distinct (sort (mapcat (fn [ns]
                              (let [ns-name (str ns)
                                    ns-name (if (s/ends-with? ns-name "$macros")
                                              (apply str (drop-last 7 ns-name))
                                              ns-name)]
                                (map #(symbol ns-name (str %))
                                     (filter matches? (public-syms ns)))))
                            (all-ns))))))

(defn- special-doc
  [name-symbol]
  (assoc (special-doc-map name-symbol)
    :name name-symbol
    :special-form true))

(defn- repl-special-doc
  [name-symbol]
  (assoc (repl-special-doc-map name-symbol)
    :name name-symbol
    :repl-special-function true))

(defn- resolve-var
  "Given an analysis environment resolve a var. Analogous to
   clojure.core/resolve"
  [env sym]
  {:pre [(map? env) (symbol? sym)]}
  (try
    (ana/resolve-var env sym
                     (ana/confirm-var-exists-throw))
    (catch :default _
      (ana/resolve-macro-var env sym))))

(defn- get-macro-var
  [env sym macros-ns]
  {:pre [(symbol? macros-ns)]}
  (let [macros-ns-str (str macros-ns)
        base-ns-str   (subs macros-ns-str 0 (- (count macros-ns-str) 7))
        base-ns       (symbol base-ns-str)]
    (if-let [macro-var (with-compiler-env rr/st
                                          (resolve-var env (symbol macros-ns-str (name sym))))]
      (update (assoc macro-var :ns base-ns)
              :name #(symbol base-ns-str (name %))))))

(defn- all-macros-ns
  []
  (->> (all-ns)
       (filter #(s/ends-with? (str %) "$macros"))))

(defn- get-var
  [env sym]
  (let [var (or (with-compiler-env rr/st (resolve-var env sym))
                (some #(get-macro-var env sym %) (all-macros-ns)))]
    (when var
      (if (= (namespace (:name var)) (str (:ns var)))
        (update var :name #(symbol (name %)))
        var))))

(defn- get-aenv
  []
  (assoc (ana/empty-env)
    :ns (get-namespace @rr/current-ns)
    :context :expr))

(defn- undo-reader-conditional-whitespace-docstring
  "Undoes the effect that wrapping a reader conditional around
  a defn has on a docstring."
  [s]
  ;; We look for five spaces (or six, in case that the docstring
  ;; is not aligned under the first quote) after the first newline
  ;; (or two, in case the doctring has an unpadded blank line
  ;; after the first), and then replace all five (or six) spaces
  ;; after newlines with two.
  (when-not (nil? s)
    (if (re-find #"[^\n]*\n\n?      ?\S.*" s)
      (s/replace s #"\n      ?" "\n  ")
      s)))

(defn- doc*
  [sym print-doc-fn]
  (if-let [special-sym ('{&       fn
                          catch   try
                          finally try} sym)]
    (doc* special-sym print-doc-fn)
    (cond

      (special-doc-map sym)
      (print-doc-fn (special-doc sym))

      (repl-special-doc-map sym)
      (print-doc-fn (repl-special-doc sym))

      (get-namespace sym)
      (print-doc-fn
        (select-keys (get-namespace sym) [:name :doc]))

      (get-var (get-aenv) sym)
      (print-doc-fn
        (let [var (get-var (get-aenv) sym)
              var (assoc var :forms (-> var :meta :forms second)
                             :arglists (-> var :meta :arglists second))
              m (select-keys var
                             [:ns :name :doc :forms :arglists :macro :url])
              m (update m :doc undo-reader-conditional-whitespace-docstring)]
          (cond-> (update-in m [:name] name)
                  (:protocol-symbol var)
                  (assoc :protocol true
                         :methods
                         (->> (get-in var [:protocol-info :methods])
                              (map (fn [[fname sigs]]
                                     [fname {:doc      (:doc
                                                         (get-var (get-aenv)
                                                                  (symbol (str (:ns var)) (str fname))))
                                             :arglists (seq sigs)}]))
                              (into {})))))))))

(defn- string-doc
  [m]
  (with-out-str
    (repl/print-doc (update m :doc (if (rr/user-interface-idiom-ipad?)
                                     identity
                                     rr/reflow)))))

(defn- string-find-doc*
  [re-string-or-pattern]
  (let [re (re-pattern re-string-or-pattern)
        sym-docs (sort-by first
                          (mapcat (fn [ns]
                                    (map (juxt first (comp :doc second))
                                         (get-in @rr/st [::ana/namespaces ns :defs])))
                                  (all-ns)))]
    (string/join (for [[sym doc] sym-docs
                       :when (and doc
                                  (name sym)
                                  (or (re-find re doc)
                                      (re-find re (name sym))))]
                   (doc* sym string-doc)))))

(defn- get-file-source
  [filepath]
  (if (symbol? filepath)
    (let [without-extension (s/replace
                              (s/replace (name filepath) #"\." "/")
                              #"-" "_")]
      (or
        (js/REPLETE_LOAD (str without-extension ".clj"))
        (js/REPLETE_LOAD (str without-extension ".cljc"))
        (js/REPLETE_LOAD (str without-extension ".cljs"))))
    (let [file-source (js/REPLETE_LOAD filepath)]
      (or file-source
          (js/REPLETE_LOAD (s/replace filepath #"^out/" ""))
          (js/REPLETE_LOAD (s/replace filepath #"^src/" ""))))))

(defn- fetch-source
  [var]
  (or (::repl-entered-source var)
      (when-let [filepath (or (:file var) (:file (:meta var)))]
        (when-let [file-source (get-file-source filepath)]
          (let [rdr (rt/source-logging-push-back-reader file-source)]
            (dotimes [_ (dec (:line var))] (rt/read-line rdr))
            (binding [r/*alias-map* (reify ILookup (-lookup [_ k] k))]
              (-> (r/read {:read-cond :allow :features #{:cljs}} rdr)
                  meta :source)))))))

(defn- string-source
  [sym]
  (or (fetch-source (get-var (get-aenv) sym))
      "Source not found"))

(defn- string-pst*
  ([]
   (string-pst* '*e))
  ([expr]
   (try (cljs/eval rr/st
                   expr
                   (make-base-eval-opts)
                   (fn [{:keys [value]}]
                     (when value
                       {:tag :err
                        :val (string-error value true)})))
        (catch js/Error e {:tag :err
                           :val (str :caught e)}))))

;; Prepl also now gives :clojure.error/phase iff :err tag
(defn ^:export read-eval
  ([source]
   (read-eval source true))
  ([source expression?]
   (let [result {:tag :ret :form source :ns @rr/current-ns}]
     (binding [ana/*cljs-warning-handlers* (if expression?
                                             [rr/warning-handler]
                                             [ana/default-warning-handler])
               ana/*cljs-ns* @rr/current-ns
               env/*compiler* rr/st
               *ns* (create-ns @rr/current-ns)
               r/*data-readers* tags/*cljs-data-readers*
               r/resolve-symbol ana/resolve-symbol
               r/*alias-map* (rr/current-alias-map)]
       (try
         (let [expression-form (and expression? (rr/repl-read-string source))]
           (if (rr/repl-special? expression-form)
             (let [special-form (first expression-form)
                   argument (second expression-form)]
               (case special-form
                 in-ns (merge result (prepl-process-in-ns argument))
                 dir (merge result {:val (string-dir argument)})
                 apropos (let [value (apropos* argument)]
                           (rr/process-1-2-3 expression-form value)
                           (merge result {:val value}))
                 doc (merge result {:val (doc* argument string-doc)})
                 find-doc (merge result {:val (string-find-doc* argument)})
                 source (merge result {:val (string-source argument)})
                 pst (merge result (if argument
                                     (string-pst* argument)
                                     (string-pst*)))))
             (let [eval-result (atom result)]
               (cljs/eval-str
                 rr/st
                 source
                 (if expression? source "File")             ;; Later
                 (merge
                   {:ns         @rr/current-ns
                    :load       load
                    :eval       cljs/js-eval
                    :source-map false
                    :verbose    (:verbose @rr/app-env)}
                   (when (:checked-arrays @rr/app-env)
                     {:checked-arrays (:checked-arrays @rr/app-env)})
                   (when expression?
                     {:context       :expr
                      :def-emits-var true}))
                 (fn [{:keys [ns value error]}]
                   (if expression?
                     (when-not error
                       (rr/process-1-2-3 expression-form value)
                       (when (rr/def-form? expression-form)
                         (let [{:keys [ns name]} (meta value)]
                           (swap! rr/st assoc-in [::ana/namespaces ns
                                                  :defs name
                                                  ::repl-entered-source] source)))
                       (reset! rr/current-ns ns)
                       (reset! eval-result (merge result {:val value}))))
                   (when error
                     (set! *e error)
                     (reset! eval-result (merge result {:tag :err :val error})))))
               @eval-result)))
         (catch :default e
           (merge result {:tag :err :val e})))))))
