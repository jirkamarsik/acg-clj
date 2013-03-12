(ns acg-clj.acg
  "Relations implementing the notions of abstract categorial
  grammars (signatures and lexicons). "
  (:require [clojure.core.logic :as l])
  (:use (acg-clj lambda
                 lexicon
                 utils)))

(defn sig-consto [signature name constant]
  (l/fresh [type]
           (l/membero [name type] (seq (:constants signature)))
           (l/== constant {:type type
                           :constant-name name})))

(defn sig-lexo [signature hypertag constant]
  (if (contains? signature :lex-typeo)
    (l/fresh [type]
             (hypertago hypertag)
             ((:lex-typeo signature) hypertag type)
             (l/== constant {:type type
                             :hypertag hypertag}))
    l/fail))

(defn sigo [signature constant]
  (l/conde [(l/fresh [name]
                     (sig-consto signature name constant))]
           [(l/fresh [hypertag]
                     (sig-lexo signature hypertag constant))]))


;; TODO: This should know the difference between constants, that need
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
(defn sig-termo [signature term type]
  (let [consts (l/run* [q] (sigo signature q))]
    (typeo (for [const consts] [const :i])
           (for [const consts] [const (:type const)])
           []
           term
           type)))

(defn sig-sento [signature sentence]
  (sig-termo signature sentence (:principal-type signature)))


(defn sig-findo [signature wordform constant type]
  (l/fresh [hypertag]
           (lexicono wordform hypertag)
           (sig-lexo signature hypertag constant)
           (l/featurec constant {:type type})))

(defn sig-findo' [signature wordform constant]
  (l/fresh [hypertag]
           (lexicono wordform hypertag)
           (sig-lexo signature hypertag constant)))


(defn unityped [unitype]
  (fn [hypertag type]
    (l/== type unitype)))

(defmacro fs-match [patterns]
  (let [hypertag-sym (gensym "hypertag")
        out-sym (gensym "out")
        goals (for [[pat val] patterns]
                `[(retrievec ~hypertag-sym ~pat)
                  (l/== ~out-sym ~val)])]
    `(fn [~hypertag-sym ~out-sym]
       (l/conde ~@goals))))

(defmacro with-sig-consts [signature & goals]
  (let [consts (keys (:constants @(resolve signature)))]
    `(l/fresh ~(vec consts)
              ~@(for [const consts]
                  `(sig-consto ~signature '~const ~const))
              ~@goals)))

(defn translate-consts [translation-map]
  (fn [constant translated-term]
    (l/fresh [constant-name]
             (l/featurec constant {:constant-name constant-name})
             (l/membero [constant-name translated-term] (seq translation-map)))))
