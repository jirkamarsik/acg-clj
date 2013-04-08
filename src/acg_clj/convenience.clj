(ns acg-clj.convenience
  (:require [clojure.core.logic :as l])
  (:use (acg-clj acg
                 termix)))

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
                                 ((sig-lexo sig#) c#)))
                        (partition 2 ~word-bindings))
              ~@goals)))

(defn term-in-sigo
  "A useful tool for expressing terms with lexical constants by giving
  their wordforms. Given a signature `sig' and an AST of a lambda `term',
  returns a unary relation that unifies its argument with `term' where
  all string constants have been replaced by constants of `sig' having
  those wordforms."
  [sig term]
  (fn [out]
    (let [lvar-string-map (atom {})
          ;; This is almost the same as lvarize in retrievec => solve
          ;; using some HOFs.
          lvar-term (term-postwalk (fn [t]
                                     (if (and (= (tagged-term-type t) 'const)
                                              (string? (second t)))
                                       (let [lvar (l/lvar)]
                                         (swap! lvar-string-map assoc lvar (second t))
                                         ['const lvar])
                                       t))
                                   term)]
      (l/all (l/everyg (fn [[c w]]
                         (l/all (has-wordformo c w)
                                ((sig-lexo sig) c)))
                       (seq @lvar-string-map))
             (l/== out lvar-term)))))

(defmacro rt-in-sigo
  "A combination of term-in-sigo, rt and with-sig-consts for the
  ultimate comfort in typing down terms. Lets you write `term' in the
  human-readable notation, referring to lexical constants of `sig' by
  their wordforms and to the extra-lexical constants by their symbolic
  names. Returns a relation that unifies its argument with the
  matched terms.

  E.g. ((rt-in-sigo sim-sem-sig
                    (il [x] (and? (\"rouge\" x) (\"pomme\" x))))
        term))"
  [sig term]
  `(fn [out#]
     (with-sig-consts ~sig
       ((term-in-sigo ~sig (rt ~term)) out#))))


(defn drop-constraints
  "Drops the constraint part (if present) from the results returned by
  core.logic's run(*)."
  [result]
  (if (and (seq? result) (= (second result) :-))
    (first result)
    result))
