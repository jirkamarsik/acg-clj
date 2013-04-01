(ns acg-clj.convenience
  (:require [clojure.core.logic :as l])
  (:use acg-clj.acg
        acg-clj.termix))

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

(defn term-in-sigo [sig out term]
  (let [lvar-string-map (atom {})
        ;; This is almost the same as lvarize in retrievec => solve
        ;; using some HOFs.
        lvar-term (termpostwalk (fn [t]
                                  (if (and (= (tagged-term-type t) 'const)
                                           (string? (second t)))
                                    (let [lvar (l/lvar)]
                                         (swap! lvar-string-map assoc lvar (second t))
                                         ['const lvar])
                                    t))
                                term)]
    (l/all (l/everyg (fn [[c w]]
                       (l/all (has-wordformo c w)
                              (sig-lexo sig c)))
                     (seq @lvar-string-map))
           (l/== out lvar-term))))

(defmacro rt-in-sigo [sig out term]
  `(with-sig-consts ~sig
     (term-in-sigo ~sig ~out (rt ~term))))
