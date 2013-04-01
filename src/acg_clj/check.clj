(ns acg-clj.check
  (:require [clojure.core.logic :as l])
  (:use plumbing.core
        acg-clj.utils
        [acg-clj.termix :only [rt]]
        acg-clj.lambda
        acg-clj.acg))

(defn type-alisto [atomic-types type-al]
  (l/== type-al (map vector atomic-types (repeatedly l/lvar))))

(defn type-assigno [type-al a-type o-type]
  (l/conde [(assoco type-al a-type o-type)]
           [(l/fresh [arrow aa-type ab-type oa-type ob-type]
                     (l/membero arrow '[-> =>])
                     (l/== a-type [arrow aa-type ab-type])
                     (l/== o-type [arrow oa-type ob-type])
                     (type-assigno type-al aa-type oa-type)
                     (type-assigno type-al ab-type ob-type))]))


;; TODO: Testing functions should also check the extra-lexical constants!

(defn test-lexicon-homo? [sig lexicono test-wordforms]
  (let [test-consts (l/run* [const]
                            (l/fresh [wordform lex-image]
                                     (l/membero wordform test-wordforms)
                                     (has-wordformo const wordform)
                                     (sig-lexo sig const)
                                     (lexicono (rt const) lex-image)))
        abstract-types (l/run* [type]
                               (l/fresh [const]
                                        (l/membero const test-consts)
                                        (top-typeo (rt const) type)))
        find-atomic-types (fn find-atomic-types [type]
                            (if (sequential? type)
                              (mapcat find-atomic-types (rest type))
                              [type]))
        atomic-types (set (mapcat find-atomic-types abstract-types))]
    (let [type-al (first (l/run 1 [type-al]
                                (type-alisto atomic-types type-al)
                                (l/everyg
                                 (fn [const]
                                   (l/fresh [a-term a-type o-term o-type]
                                            (l/== a-term (rt const))
                                            (top-typeo a-term a-type)
                                            (lexicono a-term o-term)
                                            (top-typeo o-term o-type)
                                            (type-assigno type-al a-type o-type)))
                                 test-consts)))]
      (assert type-al "The lexicon is not homomorphic w.r.t. to the types.")
      type-al)))

(defn test-lexicon-fn? [sig lexicono test-wordforms]
  (let [test-consts (l/run* [const]
                            (l/fresh [wordform]
                                     (l/membero wordform test-wordforms)
                                     (has-wordformo const wordform)
                                     (sig-lexo sig const)))]
    (doseq [const test-consts]
      (let [lex-images (l/run* [lex-image]
                               (lexicono (rt const) lex-image))]
        (assert (= (count lex-images) 1)
                {:msg "The lexicon didn't assign exactly one term."
                 :count-images (count lex-images)
                 :images lex-images
                 :constant const})))
    true))
