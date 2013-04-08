(ns acg-clj.utils
  "A medley of generally useful things which don't really fit anywhere
  else."
  (:require [clojure.core.logic :as l]
            [clojure.set :as set])
  (:use plumbing.core))

(defn mapuni
  "Just like mapcat, but does a set/union instead of concat."
  [f & colls]
  (apply set/union (apply map f colls)))


(defn mapo
  "Given `f', a binary goal encoding a function, returns a binary
  relation that encodes the function (map f %)."
  [f]
  (fn lifted-f [in out]
    (l/matche [in out]
              ([[] []])
              ([[in-h . in-t] [out-h . out-t]]
                 (f in-h out-h)
                 (lifted-f in-t out-t)))))

(l/defne ^{:doc "The alist `al' associates the key `k' with the value
  `v'."} assoco
  [al k v]
  ([[[k v] . _] _ _])
  ([[[k' v'] . ral] _ _]
     (l/!= k k')
     (assoco ral k v)))

(l/defne ^{:doc "`key' is the key in the key-value pair `key-value'."}
  keyo
  [key-value key]
  ([[key _] _]))

(defn keyso
  "`keys' is the list of keys of the alist `alist'."
  [alist keys]
  ((mapo keyo) alist keys))


(defn retrievec
  "The `hypertag' is compatible with the `pattern'. For the pattern to
  be compatible with the hypertag, the hypertag should contain all the
  key paths of the pattern and the values in the leaf nodes of the
  pattern must be members of the lists stored under the same key paths
  in the hypertag.

  E.g. (retrievec {:head {:cat [\"v\"]
                          :pers [\"1\" \"3\"]}
                   :subj {:cat [\"n\"]}}
                  {:head {:cat \"v\"
                          :pers \"1\"}})"
  [hypertag pattern]
  (let [lvar-value-pairs (atom {})
        lvarize (fn lvarize [pat]
                  (if (map? pat)
                    (map-vals lvarize pat)
                    (let [lvar (l/lvar)]
                      (swap! lvar-value-pairs assoc lvar pat)
                      lvar)))
        lvar-pattern (lvarize pattern)]
    (l/all (l/featurec hypertag lvar-pattern)
           (l/everyg (fn [[lvar val]]
                       (l/membero val lvar))
                     @lvar-value-pairs))))


(defn org
  "Conde as a function. Takes any number of goals and returns a goal
  which is their disjunction."
  ([]
     l/fail)
  ([goal & goals]
     (l/conde [goal]
              [(apply org goals)])))

(defn andg
  "All as a function. Takes any number of goals and returns a goal
  which is their conjunction."
  ([]
     l/succeed)
  ([goal & goals]
     (l/all goal
            (apply andg goals))))

(defn compg
  "Like comp, but composes binary relations that encode functions."
  ([]
     (fn [x y]
       (l/== x y)))
  ([goal & goals]
     (fn [x z]
       (l/fresh [y]
                ((apply compg goals) x y)
                (goal y z)))))
