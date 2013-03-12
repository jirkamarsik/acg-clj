(ns acg-clj.acg
  "Relations implementing the notions of abstract categorial
  grammars (signatures and lexicons)."
  (:require [clojure.core.logic :as l])
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
  ""
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

(defn sigo [signature constant]
  (l/conde [(sig-consto signature constant)]
           [(sig-lexo signature constant)]))


'{:type _
  :id [{:constant-name _}
       {:lex-entry {:wordform _
                    :hypertag _}
        :spec _}]}

(defn has-typeo [constant type]
  (l/fresh [id]
           (l/== constant {:type type
                           :id id})))

(defn has-ido [constant id]
  (l/fresh [type]
           (l/== constant {:type type
                           :id id})))

(defn has-nameo [constant name]
  (l/fresh [id]
           (has-ido constant id)
           (l/== id {:constant-name name})))

(defn has-lex-entryo [constant lex-entry]
  (l/fresh [id spec]
           (has-ido constant id)
           (l/== id {:lex-entry lex-entry
                     :spec spec})))

(defn has-speco [constant spec]
  (l/fresh [id lex-entry]
           (has-ido constant id)
           (l/== id {:lex-entry lex-entry
                     :spec spec})))

(defn has-wordformo [constant wordform]
  (l/fresh [lex-entry hypertag]
           (has-lex-entryo constant lex-entry)
           (l/== lex-entry {:wordform wordform
                            :hypertag hypertag})))

(defn has-hypertago [constant hypertag]
  (l/fresh [lex-entry wordform]
           (has-lex-entryo constant lex-entry)
           (l/== lex-entry {:wordform wordform
                            :hypertag hypertag})))


(defn has-cato [constant cat]
  (l/fresh [hypertag cats]
           (has-hypertago constant hypertag)
           (rfeaturec hypertag {:head {:cat cats}})
           (l/membero cat cats)))


(defn share-lex-entryo [constant-a constant-b]
  (l/fresh [lex-entry]
           (has-lex-entryo constant-a)
           (has-lex-entryo constant-b)))


;; TODO: This should know the difference between constants, which need
;; to be translated, and variables, which are not translated.
(l/defne apply-lexo [lexo abs-term obj-term]
  ([_ ['var abs-v] _]
     (lexo abs-v obj-term))
  ([_ [lam [v] abs-b] [lam [v] obj-b]]
     (l/membero lam '[llam ilam])
     (apply-lexo lexo abs-b obj-b))
  ([_ ['app abs-f abs-a] ['app obj-f obj-a]]
     (apply-lexo lexo abs-f obj-f)
     (apply-lexo lexo abs-a obj-a)))


;; WARNING: Too demanding to run l/run*.
;; TODO: Find a better way to do this.
(defn sig-termo [signature term type]
  (let [consts (l/run* [q] (sigo signature q))]
    (typeo (for [const consts] [const :i])
           (for [const consts] [const (:type const)])
           []
           term
           type)))

;; WARNING: Same problems as sig-termo.
(defn sig-sento [signature sentence]
  (sig-termo signature sentence (:principal-type signature)))


(defn sig-findo [signature wordform constant type]
  (l/all (has-wordformo constant wordform)
         (has-typeo constant type)
         (sig-lexo signature constant)))

(defn sig-findo' [signature wordform constant]
  (l/all (has-wordformo constant wordform)
         (sig-lexo signature constant)))


(defn unityper [unitype]
  (fn [hypertag type spec]
    (l/all (l/== type unitype)
           (l/== spec nil))))

(defn fs-matche
  ([fs]
     l/fail)
  ([fs [pattern & goals] & clauses]
     (l/conde [(retrievec fs pattern)
               (apply andg goals)]
              [(apply fs-matche fs clauses)])))

(defn fs-assigne [fs target & pattern-value-pairs]
  (apply fs-matche fs
         (for [[pattern value] (partition 2 pattern-value-pairs)]
           [pattern (l/== target value)])))

(defn ht->type-mapper [patterns]
  (fn [hypertag type spec]
    (l/all (apply fs-assigne hypertag type (mapcat identity patterns))
           (l/== spec nil))))

(defmacro with-sig-consts [signature & goals]
  (let [consts (keys (:constants @(resolve signature)))]
    `(l/fresh ~(vec consts)
              ~@(for [const consts]
                  `(l/all (has-nameo ~const '~const)
                          (sig-consto ~signature ~const)))
              ~@goals)))

(defn translate-consts [translation-map]
  (fn [constant translated-term]
    (l/fresh [constant-name]
             (has-nameo constant constant-name)
             (l/membero [constant-name translated-term] (seq translation-map)))))
