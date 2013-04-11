(ns acg-clj.acg
  "Relations implementing the notions of abstract categorial
  grammars (signatures and lexicons)."
  (:require [clojure.core.logic :as l]
            [clojure.core.logic.nominal :as n])
  (:use (acg-clj lambda
                 lexicon
                 utils)
        plumbing.core))

(defn sig-constr
  "Given `signature', returns a relation saying that `constant' is an
  extra-lexical (explicitly declared) constant of the signature."
  [signature]
  (fn [constant]
    (l/fresh [name type]
             (l/== constant {:type type
                             :id {:constant-name name}})
             (l/membero [name type] (seq (:constants signature))))))

(defn sig-lexr
  "Given `signature', returns a relation saying that `constant' is a
  lexical (induced from lexicon) constant of the signature."
  [signature]
  (fn [constant]
    (if (contains? signature :lex-typespeco)
      (l/fresh [wordform hypertag spec type]
               (l/== constant {:type type
                               :id {:lex-entry {:wordform wordform
                                                :hypertag hypertag}
                                    :spec spec}})
               (lexicono wordform hypertag)
               ((:lex-typespeco signature) wordform hypertag spec type))
      l/fail)))

(defn sigr
  "Given `signature', returns a relation saying that `constant' is a
  constant of the signature."
  [signature]
  (fn [constant]
    (l/conde [((sig-constr signature) constant)]
             [((sig-lexr signature) constant)])))

;; Define accessor relations for all the fields of the constant
;; objects.
(defaccessors {:type _
               :id [{:constant-name _}
                    {:lex-entry {:wordform _
                                 :hypertag _}
                     :spec _}]})

(defn mk-arrow-type
  "Given an arrow type constructor `arrow' and a series of
  argument/result types `arg-type & more-types', produces the type
  [arrow arg-type [arrow (first more-types) [arrow ...]]]."
  [arrow arg-type & more-types]
  (if (seq more-types)
    [arrow arg-type (apply mk-arrow-type arrow more-types)]
    arg-type))

(def -->
  "Syntactic sugar for writing down arrow types that consume a series
  of arguments.

  E.g. (--> 'NP 'NP 'S)
       ;=> [-> NP [-> NP S]]"
  (partial mk-arrow-type '->))

(def ==>
  "Same as `-->', but for the non-linear implication types.

  E.g. (==> 'E 'E 'T)
       ;=> [=> E [=> E T]]"
  (partial mk-arrow-type '=>))

(defn has-cato
  "The :hypertag of `constant' has {:head {:cat `cat'}}."
  [constant cat]
  (l/fresh [hypertag]
           (has-hypertago constant hypertag)
           (retrievec hypertag {:head {:cat cat}})))

(defn share-lex-entryo
  "`constant-a' and `constant-b' have the same :lex-entry."
  [constant-a constant-b]
  (l/fresh [lex-entry]
           (has-lex-entryo constant-a lex-entry)
           (has-lex-entryo constant-b lex-entry)))


(defn extend-lexor
  "Given a lexicon (a binary relation encoding a mapping from
  constants over the abstract signature to terms over the object
  signature), returns its homomorphic extension to terms (a binary
  relation encoding a mapping from abstract terms to object terms)."
  [lexo]
  (fn extended-lexo [abs-term obj-term]
    (l/matche [abs-term obj-term]
              ([['const abs-c] _]
                 (lexo abs-c obj-term))
              ([['var v] ['var v]])
              ([[lam abs-binder] [lam obj-binder]]
                 (l/membero lam '[llam ilam])
                 (l/fresh [abs-b obj-b]
                          (n/fresh [v]
                                   (l/== abs-binder (n/tie v abs-b))
                                   (l/== obj-binder (n/tie v obj-b))
                                   (extended-lexo abs-b obj-b))))
              ([['app abs-f abs-a] ['app obj-f obj-a]]
                 (extended-lexo abs-f obj-f)
                 (extended-lexo abs-a obj-a)))))


(defn unitypedr
  "Returns a :lex-typespeco (a relation linking a wordform, a
  hypertag, a specifier and a type), that always assigns the type
  `unitype' and a nil spec."
  [unitype]
  (fn [wordform hypertag spec type]
    (l/all (l/== type unitype)
           (l/== spec nil))))

(defn fs-matche
  "Like core.logic's matche, but instead of a vector of terms to be
  matched, expects a single term. The patterns are matched to the term
  using retrievec, unused variables are NOT automatically declared.

  Ex: (fs-matche hypertag
                 [{:head {:cat \"v\"}} (l/== out :verb)]
                 [{:head {:cat \"n\"}} (l/== out :noun)])"
  ([fs]
     l/fail)
  ([fs [pattern & goals] & clauses]
     (l/conde [(retrievec fs pattern)
               (apply andg goals)]
              [(apply fs-matche fs clauses)])))

(defn fs-assigne
  "When fs-matche is used to simply unify a target term with different
  terms according to the matched pattern, fs-assigne can be used
  directly. See the example for syntax.

  Ex: (fs-assigne hypertag             out
                  {:head {:cat \"v\"}} :verb
                  {:head {:cat \"n\"}} :noun)"
  [fs target & pattern-value-pairs]
  (apply fs-matche fs
         (for [[pattern value] (partition 2 pattern-value-pairs)]
           [pattern (l/== target value)])))

(defn ht->typer
  "Returns a :lex-typespeco that tries to match the hypertag to the
  keys of the `patterns' map as in fs-matche and fs-assigne and
  assigns the respective values of the patterns as types. The
  specifier is set as nil."
  [patterns]
  (fn [wordform hypertag spec type]
    (l/all (apply fs-assigne hypertag type (apply concat patterns))
           (l/== spec nil))))

(defmacro with-sig-consts
  "An anaphoric macro useful for writing down lexicons. It opens a
  *fresh* scope with variables for all the extra-lexical constants of
  the given signature."
  [signature & goals]
  (let [consts (keys (:constants (eval signature)))]
    `(l/fresh ~(vec consts)
              ~@(for [const consts]
                  `(l/all (has-constant-nameo ~const '~const)
                          ((sig-constr ~signature) ~const)))
              ~@goals)))

(defn const-lexiconr
  "Returns a lexicon that simply maps (extra-lexical) constants
  according to their names (keys of the `translation-map') to the
  target terms (values of the `translation-map')."
  [translation-map]
  (fn [abs-const obj-term]
    (l/fresh [abs-const-name]
             (has-constant-nameo abs-const abs-const-name)
             (l/membero [abs-const-name obj-term] (seq translation-map)))))
