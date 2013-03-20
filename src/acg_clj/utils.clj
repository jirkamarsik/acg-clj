(ns acg-clj.utils
  "A medley of generally useful things which don't really fit anywhere
  else."
  (:require [clojure.core.logic :as l])
  (:use plumbing.core))

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
    (l/all (l/featurec hypertag lvar-pattern)
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
  "All as a function. Takes any number of goals and returns a goal
  which is their conjunction."
  ([]
     l/succeed)
  ([goal & goals]
     (l/all goal
            (apply andg goals))))

