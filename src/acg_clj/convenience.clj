(ns acg-clj.convenience
  (:require [clojure.core.logic :as l])
  (:use acg-clj.acg
        [acg-clj.termix :only [rt]]))

(defmacro with-words
  "Expects a signature and a vector of bindings in which names are
  bound to wordforms. Binds the names to constants having the
  respective wordforms and belonging to the given signature.

  E.g. (with-words a-stx-sig [une \"une\"
                              pomme \"pomme\"
                              rouge \"rouge\"]
         (top-typeo (rt (une (rouge pomme))) q))"
  [sig word-bindings & goals]
  `(let [sig# ~sig]
     (l/fresh ~(vec (take-nth 2 word-bindings))
              (l/everyg (fn [[c# w#]]
                          (l/all (has-wordformo c# w#)
                                 (sig-lexo sig# c#)))
                        (partition 2 ~word-bindings))
              ~@goals)))

(defmacro frobo [sig out term]
  (let [gsym-string-map (atom {})
        ;; This is almost the same as lvarize in retrievec => solve
        ;; using some HOFs.
        gsymize (fn gsymize [term]
                  (cond (seq? term) (doall (map gsymize term))
                        (string? term) (let [gsym (gensym)]
                                         (swap! gsym-string-map assoc gsym term)
                                         gsym)
                        :else term))
        gsym-term (gsymize term)]
    `(with-words ~sig ~(vec (apply concat @gsym-string-map))
       (l/== ~out (rt ~gsym-term)))))
