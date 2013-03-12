(ns acg-clj.utils
  "A medley of generally useful things which don't really fit anywhere
  else."
  (:require [clojure.core.logic :as l])
  (:use plumbing.core))

;; A short hack from Kevin Downey at http://dev.clojure.org/jira/browse/LOGIC-108
(defn rfeaturec
  "Just like core.logic's featurec, but lets you use nested maps using
  unification and multiple featurec constraints."
  [m f]
  (let [new-f (reduce (fn [m [k v]] (assoc m k (l/lvar (name k)))) {} (seq f))]
    (l/all
      (l/featurec m new-f)
      (l/everyg
       (fn [[k lvar]]
         (let [v (get f k)]
           (if (map? v)
             (l/all
               (l/featurec m {k lvar})
               (rfeaturec lvar v))
             (l/== lvar v))))
       new-f))))

(defn retrievec
  "A goal/(series of constraints) that ensures that the hypertag is
  compatible with the pattern. For the pattern to be compatible with
  the hypertag, the hypertag should contain the same key paths as the
  pattern and the values in the leaf nodes of the pattern must be
  members of the lists stored under the same key paths in the
  hypertag."
  [hypertag pattern]
  (let [lvar-value-pairs (atom {})
        lvarize (fn lvarize [pat]
                  (if (map? pat)
                    (map-vals lvarize pat)
                    (let [lvar (l/lvar)]
                      (swap! lvar-value-pairs assoc lvar pat)
                      lvar)))
        lvar-pattern (lvarize pattern)]
    (l/all (rfeaturec hypertag lvar-pattern)
           (l/everyg (fn [[lvar val]]
                       (l/membero val lvar))
                     @lvar-value-pairs))))

(defn drop-constraints
  "Drops the constraint part (if present) from the results returned by
  core.logic's run(*)."
  [result]
  (if (and (seq? result) (= (second result) :-))
    (first result)
    result))

(defn org
  "Conde as a function. Takes any number of goals and returns a goal
  which is their disjunction."
  ([]
     l/fail)
  ([goal & goals]
     (l/conde [goal]
              [(apply org goals)])))

(defn andg
  "All as a function."
  ([]
     l/succeed)
  ([goal & goals]
     (l/all goal
            (apply andg goals))))

