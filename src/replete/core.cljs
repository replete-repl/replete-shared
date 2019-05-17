(ns replete.core
  "Core Replete functions for use in scripts."
  (:refer-clojure :exclude [*command-line-args* resolve eval])
  (:require-macros
    [replete.core :refer [with-open]])
  (:require
    [cljs.spec.alpha :as s]
    [cljs.tools.reader :as r]
    [cljs.tools.reader.reader-types :as rt]
    [clojure.string :as string]
    [replete.priv-repl :as pr])
  (:import
    (goog Uri)                                               ; Explicitly import here for replete.io
    (goog.string StringBuffer)))

(s/def ::binding
  (s/cat :name symbol? :value any?))

(s/def ::bindings
  (s/and vector?
         #(even? (count %))
         (s/* ::binding)))

#_(s/fdef replete.core$macros/with-open
          :args (s/cat :bindings ::bindings :body (s/* any?)))

(defprotocol IClosable
  "Protocol for closing entities."
  (-close [this] "Closes this entity."))

(defprotocol IReader
  "Protocol for reading."
  (-read [this] "Returns available characters as a string or nil if EOF."))

(defprotocol IBufferedReader
  "Protocol for reading line-based content. Instances of IBufferedReader must
   also satisfy IReader."
  (-read-line [this] "Reads the next line."))

(defprotocol IPushbackReader
  "Protocol for readers that support undo. Instances of IPushbackReader must
  also satisfy IBufferedReader."
  (-unread [this s] "Pushes a string of characters back on to the stream."))

(defn- fission!
  "Breaks an atom's value into two parts. The supplied function should
  return a pair. The first element will be set to be the atom's new
  value and the second element will be returned."
  [atom f & args]
  (loop []
    (let [old @atom
          [new-in new-out] (apply f old args)]
      (if (compare-and-set! atom old new-in)
        new-out
        (recur)))))

(deftype ^:private Reader [raw-read raw-close buffer pos]

  IReader
  (-read [_]
    (if-some [buffered @buffer]
      (do
        (reset! buffer nil)
        (subs buffered @pos))
      (raw-read)))

  IBufferedReader
  (-read-line [this]
    (loop []
      (if-some [buffered @buffer]
        (if-some [n (string/index-of buffered "\n" @pos)]
          (let [rv (subs buffered @pos n)]
            (reset! pos (inc n))
            rv)
          (if-some [new-chars (raw-read)]
            (do
              (reset! buffer (str (subs buffered @pos) new-chars))
              (reset! pos 0)
              (recur))
            (do
              (reset! buffer nil)
              (let [rv (subs buffered @pos)]
                (if (= rv "")
                  nil
                  rv)))))
        (if-some [new-chars (raw-read)]
          (do
            (reset! buffer new-chars)
            (reset! pos 0)
            (recur))
          nil))))

  IPushbackReader
  (-unread [_ s]
    (swap! buffer #(str s %))
    (reset! pos 0))

  IClosable
  (-close [_]
    (raw-close)))


(deftype ^:private Writer [raw-write raw-flush raw-close]
  IWriter
  (-write [_ s]
    (raw-write s))
  (-flush [_]
    (raw-flush))

  IClosable
  (-close [_]
    (raw-close)))

(defprotocol IInputStream
  "Protocol for reading binary data."
  (-read-bytes [this] "Returns available bytes as an array of unsigned numbers or nil if EOF."))

(defprotocol IOutputStream
  "Protocol for writing binary data."
  (-write-bytes [this byte-array] "Writes byte array.")
  (-flush-bytes [this] "Flushes output."))

(deftype ^:private InputStream [raw-read-bytes raw-close]

  IInputStream
  (-read-bytes [_]
    (raw-read-bytes))

  IClosable
  (-close [_]
    (raw-close)))

(deftype ^:private OutputStream [raw-write-bytes raw-flush-bytes raw-close]
  IOutputStream
  (-write-bytes [_ byte-array]
    (raw-write-bytes byte-array))
  (-flush-bytes [_]
    (raw-flush-bytes))

  IClosable
  (-close [_]
    (raw-close)))

(defonce
  ^{:doc     "An IPushbackReader representing standard input for read operations."
    :dynamic true}
  *in*
  (let [closed (atom false)]
    (->Reader
      (fn []
        (when-not @closed
          (js/REPLETE_RAW_READ_STDIN)))
      #(reset! closed true)
      (atom nil)
      (atom 0))))

(defn- make-closeable-raw-writer
  [raw-write raw-flush]
  (let [closed (atom false)]
    (->Writer
      (fn [s]
        (when-not @closed
          (raw-write s)))
      (fn []
        (when-not @closed
          (raw-flush)))
      #(reset! closed true))))

(set! cljs.core/*out* (make-closeable-raw-writer js/REPLETE_RAW_WRITE_STDOUT js/REPLETE_RAW_FLUSH_STDOUT))

(defonce
  ^{:doc     "A cljs.core/IWriter representing standard error for print operations."
    :dynamic true}
  *err*
  (make-closeable-raw-writer js/REPLETE_RAW_WRITE_STDERR js/REPLETE_RAW_FLUSH_STDERR))

(defn read-line
  "Reads the next line from the current value of *in*"
  []
  (-read-line *in*))

(s/fdef read-line
        :args (s/cat)
        :ret string?)

(defn- adapt-pushback-reader
  [pushback-reader]
  (reify
    rt/Reader
    (read-char [this]
      (when-some [characters (-read pushback-reader)]
        (when (> (.-length characters) 1)
          (-unread pushback-reader (subs characters 1)))
        (subs characters 0 1)))
    (peek-char [this]
      (when-some [ch (rt/read-char this)]
        (-unread pushback-reader ch)
        ch))
    rt/IPushbackReader
    (unread [this ch]
      (when (some? ch)
        (-unread pushback-reader ch)))))

(defn read
  "Reads the first object from an IPushbackReader.
  Returns the object read. If EOF, throws if eof-error? is true.
  Otherwise returns sentinel. If no reader is provided, *in* will be used.
  Opts is a persistent map with valid keys:
     :read-cond - :allow to process reader conditionals, or
                  :preserve to keep all branches
     :features - persistent set of feature keywords for reader conditionals
     :eof - on eof, return value unless :eofthrow, then throw.
            if not specified, will throw"
  ([] (read *in*))
  ([reader]
   (r/read (adapt-pushback-reader reader)))
  ([opts reader]
   (r/read opts (adapt-pushback-reader reader)))
  ([reader eof-error? eof-value]
   (r/read (adapt-pushback-reader reader) eof-error? eof-value)))

(s/fdef read
        :args (s/alt :nullary (s/cat)
                     :unary (s/cat :reader #(satisfies? IPushbackReader %))
                     :binary (s/cat :opts map? :reader #(satisfies? IPushbackReader %))
                     :ternary (s/cat :reader #(satisfies? IPushbackReader %) :eof-error? boolean? :eof-value any?)))

(defn- make-string-reader
  [s]
  (let [content (volatile! s)]
    (->Reader
      (fn [] (let [return @content]
               (vreset! content nil)
               return))
      (fn [])
      (atom nil)
      (atom 0))))

(defn read-string
  "Reads one object from the string s. Optionally include reader
  options, as specified in read."
  ([s] (read (make-string-reader s)))
  ([opts s] (read opts (make-string-reader s))))

(s/fdef read-string
        :args (s/alt :unary (s/cat :s string?)
                     :binary (s/cat :opts map? :s string?)))
(defn line-seq
  "Returns the lines of text from rdr as a lazy sequence of strings. rdr must
  implement IBufferedReader."
  [rdr]
  (when-let [line (-read-line rdr)]
    (cons line (lazy-seq (line-seq rdr)))))

(s/fdef line-seq
        :args (s/cat :rdr #(instance? IBufferedReader %))
        :ret seq?)

(defonce
  ^{:dynamic true
    :private true}
  *as-file-fn*
  (fn [_]
    (throw (js/Error. "No *as-file-fn* fn set."))))

(defonce
  ^{:dynamic true
    :private true}
  *file?-fn*
  (fn [_]
    (throw (js/Error. "No *file?-fn* fn set."))))

(defn file-seq
  "A tree seq on files"
  [dir]
  (tree-seq
    (fn [f] (js/REPLETE_IS_DIRECTORY (:path f)))
    (fn [d] (map *as-file-fn*
                 (js/REPLETE_LIST_FILES (:path d))))
    (*as-file-fn* dir)))

(defn- file?
  [x]
  (*file?-fn* x))

(s/fdef file-seq
        :args (s/cat :dir (s/or :string string? :file file?))
        :ret? seq?)

(defonce
  ^{:dynamic true
    :private true}
  *reader-fn*
  (fn [_]
    (throw (js/Error. "No *reader-fn* fn set."))))

(defonce
  ^{:dynamic true
    :private true}
  *writer-fn*
  (fn [_]
    (throw (js/Error. "No *writer-fn* fn set."))))

(defn slurp
  "Opens a reader on f and reads all its contents, returning a string. See
  replete.io/reader for a complete list of supported arguments."
  [f & opts]
  (with-open [r (apply *reader-fn* f opts)]
     (let [sb (StringBuffer.)]
       (loop [s (-read r)]
         (if (nil? s)
           (.toString sb)
           (do
             (.append sb s)
             (recur (-read r))))))))

(s/fdef slurp
        :args (s/cat :f (s/or :string string?
                              :file file?
                              :uri #(instance? Uri %))
                     :opts (s/* any?))
        :ret string?)

(defn spit
  "Opposite of slurp. Opens f with writer, writes content, then closes f.
  Options passed to replete.io/writer."
  [f content & opts]
  (with-open [w (apply *writer-fn* f opts)]
             (-write w (str content))))

(s/fdef spit
        :args (s/cat :f (s/or :string string?
                              :file file?
                              :uri #(instance? Uri %))
                     :content any? :opts (s/* any?)))

(defn eval
  "Evaluates the form data structure (not text!) and returns the result."
  [form]
  (cljs.core/eval form))

(s/fdef eval
        :args (s/cat :form any?)
        :ret any?)

(defn ns-resolve
  "Returns the var to which a symbol will be resolved in the namespace, else
  nil."
  [ns sym]
  (#'pr/ns-resolve ns sym))

(s/fdef ns-resolve
        :args (s/cat :ns symbol? :sym symbol?)
        :ret (s/nilable var?))

(defn resolve
  "Returns the var to which a symbol will be resolved in the current
  namespace, else nil."
  [sym]
  (#'pr/resolve sym))

(s/fdef resolve
        :args (s/cat :sym symbol?)
        :ret (s/nilable var?))

(defn requiring-resolve
  "Resolves namespace-qualified sym per 'resolve'. If initial resolve
  fails, attempts to require sym's namespace and retries."
  [sym]
  (if (qualified-symbol? sym)
    (or (resolve sym)
        (do (eval `(require '~(-> sym namespace symbol)))
            (resolve sym)))
    (throw (js/Error. (str "Not a qualified symbol: " sym)))))

(s/fdef requiring-resolve
        :args (s/cat :sym qualified-symbol?)
        :ret (s/nilable var?))

(defn find-var
  "Returns the global var named by the namespace-qualified symbol, or
  nil if no var with that name."
  [sym]
  (when (eval `(exists? ~sym))
    (eval `(var ~sym))))

(s/fdef find-var
        :args (s/cat :sym qualified-symbol?)
        :ret (s/nilable var?))

(defn intern
  "Finds or creates a var named by the symbol name in the namespace ns (which
  can be a symbol or a namespace), setting its root binding to val if supplied.
  The namespace must exist. The var will adopt any metadata from the name
  symbol. Returns the var."
  ([ns name]
   (#'pr/intern ns name))
  ([ns name val]
   (#'pr/intern ns name val)))

(s/fdef intern
        :args (s/cat :ns (s/or :sym symbol? :ns #(instance? Namespace %))
                     :name symbol?
                     :val (s/? any?)))

(defn- transfer-ns
  [state ns]
  (-> state
      (assoc-in [:cljs.analyzer/namespaces ns]
                (get-in @@#'pr/st [:cljs.analyzer/namespaces ns]))))

(defn init-empty-state
  "An init function for use with cljs.js/empty-state which initializes the
  empty state with cljs.core analysis metadata.

  This is useful because Replete is built with :dump-core set to false.

  Usage: (cljs.js/empty-state init-empty-state)"
  [state]
  (-> state
      (transfer-ns 'cljs.core)
      (transfer-ns 'cljs.core$macros)))

(s/fdef init-empty-state
        :args (s/cat :state map?)
        :ret map?)

(defn sleep
  "Causes execution to block for the specified number of milliseconds plus the
  optionally specified number of nanoseconds.

  millis should not be negative and nanos should be in the range 0–999999"
  ([millis] (sleep millis 0))
  ([millis nanos] (js/REPLETE_SLEEP millis nanos)))

(s/fdef sleep
        :args (s/alt :unary (s/cat :millis #(and (integer? %) (not (neg? %))))
                     :binary (s/cat :millis #(and (integer? %) (not (neg? %))) :nanos #(and (integer? %) (<= 0 % 999999)))))

(defn load-reader
  "Sequentially read and evaluate the set of forms contained in the
  stream/file"
  [rdr]
  (->> (repeatedly #(read {:eof ::eof} rdr))
       (take-while #(not (keyword-identical? % ::eof)))
       (reduce #(eval %2) nil)))

(s/fdef load-reader
        :args (s/cat :rdr #(satisfies? IPushbackReader %))
        :ret any?)

(defn load-string
  "Sequentially read and evaluate the set of forms contained in the
  string"
  [s]
  (load-reader (make-string-reader s)))

(s/fdef load-string
        :args (s/cat :s string?)
        :ret any?)

;; Ensure replete.io and replete.http are loaded so that their
;; facilities are available
(#'pr/side-load-ns 'replete.http)
(#'pr/side-load-ns 'replete.io)
