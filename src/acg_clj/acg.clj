(ns acg-clj.acg
  "Relations implementing the notions of abstract categorial
  grammars (signatures and lexicons)."
  (:require [clojure.core.logic :as l]
            [clojure.core.logic.nominal :as n])
  (:use (acg-clj lambda
                 lexicon
                 utils)
        plumbing.core))

(defn sig-consto
  "Given a signature, this relation ensures that `constant' is an
  extra-lexical (explicitly declared) constant of the signature."
  [signature constant]
  (l/fresh [name type]
           (l/== constant {:type type
                           :id {:constant-name name}})
           (l/membero [name type] (seq (:constants signature)))))

(defn sig-lexo
  "Given a signature, this relation ensures that `constant' is a
  lexical (induced from lexicon) constant of the signature."
  [signature constant]
  (if (contains? signature :lex-typespeco)
    (l/fresh [wordform hypertag type spec]
             (l/== constant {:type type
                             :id {:lex-entry {:wordform wordform
                                              :hypertag hypertag}
                                  :spec spec}})
             (lexicono wordform hypertag)
             ((:lex-typespeco signature) hypertag type spec))
    l/fail))

(defn sigo
  "Given a signature, ensures that `constant' is a constant of the
  signature."
  [signature constant]
  (l/conde [(sig-consto signature constant)]
           [(sig-lexo signature constant)]))

;; Maybe generate the following "accessor" relations by some magic
;; macro from the schema below.
'{:type _
  :id [{:constant-name _}
       {:lex-entry {:wordform _
                    :hypertag _}
        :spec _}]}

(defn has-typeo
  "Accesses [:type] in a constant."
  [constant type]
  (l/fresh [id]
           (l/== constant {:type type
                           :id id})))

(defn has-ido
  "Accesses [:id] in a constant."
  [constant id]
  (l/fresh [type]
           (l/== constant {:type type
                           :id id})))

(defn has-nameo
  "Accesses [:id :constant-name] in a constant."
  [constant name]
  (l/fresh [id]
           (has-ido constant id)
           (l/== id {:constant-name name})))

(defn has-lex-entryo
  "Accesses [:id :lex-entry] in a constant."
  [constant lex-entry]
  (l/fresh [id spec]
           (has-ido constant id)
           (l/== id {:lex-entry lex-entry
                     :spec spec})))

(defn has-speco
  "Accesses [:id :spec] in a constant."
  [constant spec]
  (l/fresh [id lex-entry]
           (has-ido constant id)
           (l/== id {:lex-entry lex-entry
                     :spec spec})))

(defn has-wordformo
  "Accesses [:id :lex-entry :wordform] in a constant."
  [constant wordform]
  (l/fresh [lex-entry hypertag]
           (has-lex-entryo constant lex-entry)
           (l/== lex-entry {:wordform wordform
                            :hypertag hypertag})))

(defn has-hypertago
  "Accesses [:id :lex-entry :hypertag] in a constant."
  [constant hypertag]
  (l/fresh [lex-entry wordform]
           (has-lex-entryo constant lex-entry)
           (l/== lex-entry {:wordform wordform
                            :hypertag hypertag})))


;; MAYBE-USEFUL?
(defn has-cato
  "Ensures that the head of the hypertag of `constant' is compatible
  with the category `cat'."
  [constant cat]
  (l/fresh [hypertag cats]
           (has-hypertago constant hypertag)
           (l/featurec hypertag {:head {:cat cats}})
           (l/membero cat cats)))

(defn share-lex-entryo
  "Ensures that the two constants have the same :lex-entry."
  [constant-a constant-b]
  (l/fresh [lex-entry]
           (has-lex-entryo constant-a lex-entry)
           (has-lex-entryo constant-b lex-entry)))


(defn lexo-extend [lexo]
  "Given a lexicon (a binary relation encoding a mapping from
  constants over the abstract signature to terms over the object
  signature), returns its homomorphic extension to terms (a binary
  relation encoding a mapping from abstract terms to object terms)."
  (fn extended-lexo [abs-term obj-term]
    (l/matche [abs-term obj-term]
              ([['const abs-c] _]
                 (lexo abs-c obj-term))
              ([['var v] ['var v]])
              ([[lam abs-binder] [lam obj-binder]]
                 (l/membero lam '[llam ilam])
                 (l/fresh [v abs-b obj-b]
                          (l/== abs-binder (n/tie v abs-b))
                          (l/== obj-binder (n/tie v obj-b))
                          (extended-lexo abs-b obj-b)))
              ([['app abs-f abs-a] ['app obj-f obj-a]]
                 (extended-lexo abs-f obj-f)
                 (extended-lexo abs-a obj-a)))))


;; WARNING: Too demanding to run l/run*.
;; TODO: Find a better way to do this.
(defn sig-termo
  "Given a signature, ensures that `term' is a correctly typed lambda-term
  over the signature having type `type'."
  [signature term type]
  (let [consts (l/run* [q] (sigo signature q))]
    (typeo (for [const consts] [const :i])
           (for [const consts] [const (:type const)])
           []
           term
           type)))

;; WARNING: Same problems as sig-termo.
(defn sig-sento
  "Given a signature, ensures that `term' is a correctly typed lambda-term
  over the signature having the signature's principal type."
  [signature sentence]
  (sig-termo signature sentence (:principal-type signature)))


;; MAYBE-USEFUL?
(defn sig-findo
  "Given a signature, ensures that `constant' is a constant of the
  signature induced by a lexical entry having the wordform
  `wordform'."
  [signature wordform constant]
  (l/all (has-wordformo constant wordform)
         (sig-lexo signature constant)))

;; MAYBE-USEFUL?
(defn sig-findo'
  "Given a signature, ensures that `constant' is a constant of the
  signature having type `type' and induced by a lexical entry having
  the wordform `wordform'."
  [signature wordform constant type]
  (l/all (has-wordformo constant wordform)
         (has-typeo constant type)
         (sig-lexo signature constant)))


(defn unityper
  "Returns a :lex-typespeco (relation associating a hypertag with a
  type and specifier), that always assigns the type `unitype' and a
  nil spec."
  [unitype]
  (fn [hypertag type spec]
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

  Ex: (fs-assigne hypertag out
                  {:head {:cat \"v\"}} :verb
                  {:head {:cat \"n\"}} :noun)"
  [fs target & pattern-value-pairs]
  (apply fs-matche fs
         (for [[pattern value] (partition 2 pattern-value-pairs)]
           [pattern (l/== target value)])))

(defn ht->type-mapper
  "Returns a :lex-typespeco that tries to match the hypertag to the
  keys of the `patterns' map as in fs-matche and fs-assigne and
  assigns the respective values of the patterns as types. The
  specifier is set as nil."
  [patterns]
  (fn [hypertag type spec]
    (l/all (apply fs-assigne hypertag type (apply concat patterns))
           (l/== spec nil))))

(defmacro with-sig-consts
  "An anaphoric macro useful for writing down lexicons. It opens a
  *fresh* scope with variables for all the extra-lexical constants of
  the given signature."
  [signature & goals]
  (let [consts (keys (:constants @(resolve signature)))]
    `(l/fresh ~(vec consts)
              ~@(for [const consts]
                  `(l/all (has-nameo ~const '~const)
                          (sig-consto ~signature ~const)))
              ~@goals)))

(defn const-lexicon
  "Returns a lexicon that simply maps (extra-lexical) constants
  according to their names (keys of the `translation-map') to the
  target terms (values of the `translation-map')."
  [translation-map]
  (fn [constant translated-term]
    (l/fresh [constant-name]
             (has-nameo constant constant-name)
             (l/membero [constant-name translated-term] (seq translation-map)))))
