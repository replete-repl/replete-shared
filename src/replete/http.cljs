(ns replete.http)

(defn get [url]
  (js/REPLETE_REQUEST url "get"))
