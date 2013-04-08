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
  "Given `signature', returns a relation saying that `constant' is an
  extra-lexical (explicitly declared) constant of the signature."
  [signature]
  (fn [constant]
    (l/fresh [name type]
             (l/== constant {:type type
                             :id {:constant-name name}})
             (l/membero [name type] (seq (:constants signature))))))

(defn sig-lexo
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

(defn sigo
  "Given `signature', returns a relation saying that `constant' is a
  constant of the signature."
  [signature]
  (fn [constant]
    (l/conde [((sig-consto signature) constant)]
             [((sig-lexo signature) constant)])))

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

(defn has-constant-nameo
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
                 (l/fresh [abs-b obj-b]
                          (n/fresh [v]
                                   (l/== abs-binder (n/tie v abs-b))
                                   (l/== obj-binder (n/tie v obj-b))
                                   (extended-lexo abs-b obj-b))))
              ([['app abs-f abs-a] ['app obj-f obj-a]]
                 (extended-lexo abs-f obj-f)
                 (extended-lexo abs-a obj-a)))))


(defn unityper
  "Returns a :lex-typespeco (relation associating a hypertag with a
  type and specifier), that always assigns the type `unitype' and a
  nil spec."
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
  (fn [wordform hypertag spec type]
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
                  `(l/all (has-constant-nameo ~const '~const)
                          ((sig-consto ~signature) ~const)))
              ~@goals)))

(defn const-lexicon
  "Returns a lexicon that simply maps (extra-lexical) constants
  according to their names (keys of the `translation-map') to the
  target terms (values of the `translation-map')."
  [translation-map]
  (fn [constant translated-term]
    (l/fresh [constant-name]
             (has-constant-nameo constant constant-name)
             (l/membero [constant-name translated-term] (seq translation-map)))))
