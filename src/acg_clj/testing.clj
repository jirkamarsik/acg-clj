(ns acg-clj.testing
  "A namespace of functionality useful for testing your signature and
  lexicon definitions."
  (:require [clojure.core.logic :as l]
            [clojure.set :as set]
            [clojure.test :as test])
  (:use (acg-clj acg
                 lambda
                 utils
                 [termix :only [rt unreify-term]])
        plumbing.core))

(defn all-consts
  "Finds all the constants belonging to `signature', restricting the
  lexical ones only to those that have one of the wordforms listed in
  `wordforms'."
  [signature wordforms]
  (l/run* [const]
          (l/conde [(l/fresh [wordform]
                             (has-wordformo const wordform)
                             (l/membero wordform wordforms)
                             ((sig-lexg signature) const))]
                   [((sig-constg signature) const)])))

(defn consts-with-lex-image
  "Finds all the constants belonging to `signature' that have some
  image given by `lexicono', restricting the lexical constants only to
  the wordforms listed in `wordforms'."
  [signature lexicono wordforms]
  (l/run* [const]
          (l/fresh [lex-image]
                   (l/membero const (all-consts signature wordforms))
                   (lexicono (rt const) lex-image))))

(defn well-typed-consts
  "Finds all the constants belonging to `signature' whose image given
  by `lexicono' is well-typed, restricting the lexical constants by
  the list of wordforms `wordforms'."
  [signature lexicono wordforms]
  (l/run* [const]
          (l/fresh [lex-image lex-image-type]
                   (l/membero const (all-consts signature wordforms))
                   (lexicono (rt const) lex-image)
                   (top-typeo lex-image lex-image-type))))


(defn type-assigno
  "The homomorphic extension of the type mapping defined by the alist
  `type-al' maps the abstract type `a-type' to the object type
  `o-type'."
  [type-al a-type o-type]
  (l/conde [(assoco type-al a-type o-type)]
           [(l/fresh [arrow aa-type ab-type oa-type ob-type]
                     (l/membero arrow '[-> =>])
                     (l/== a-type [arrow aa-type ab-type])
                     (l/== o-type [arrow oa-type ob-type])
                     (type-assigno type-al aa-type oa-type)
                     (type-assigno type-al ab-type ob-type))]))

;; TODO: Maybe do this as a multimethod with a hierarchy and a
;; dispatch function for types.
(defn get-atomic-types
  "Retrieves all the atomic types occurring in the (possibly complex)
  type `type'."
  [type]
  (if (sequential? type)
    (let [[arrow argument result] type]
      (set/union (get-atomic-types argument)
                 (get-atomic-types result)))
    #{type}))

(defn find-type-homomorphisms
  "Finds all the mappings from abstract to object types whose
  homomorphic extension connects the abstract types of the constants
  `test-consts' and the object types of the terms assigned to them by
  the lexicon `lexicono'."
  [lexicono test-consts]
  (let [atomic-abstract-types (mapuni (comp get-atomic-types :type) test-consts)
        type-als (l/run* [type-al]
                         (keyso type-al (vec atomic-abstract-types))
                         (l/everyg
                          (fn [const]
                            (l/fresh [a-term a-type o-term o-type]
                                     (l/== a-term (rt const))
                                     (top-typeo a-term a-type)
                                     (lexicono a-term o-term)
                                     (top-typeo o-term o-type)
                                     (type-assigno type-al a-type o-type)))
                          test-consts))]
    (for [type-al type-als]
      (for-map [[a-type o-type] type-al]
               a-type
               o-type))))


(defn test-lexicon-fn
  "Tests whether `lexicono' assigns exactly one object term to the
  abstract constants in `test-consts'."
  [lexicono test-consts]
  (doseq [const test-consts]
    (let [lex-images (l/run* [lex-image]
                             (lexicono (rt const) lex-image))]
      (test/is (= (count lex-images) 1)
               {:msg "The lexicon assigns exactly one term to every constant."
                :const const
                :lex-images lex-images
                :count-lex-images (count lex-images)}))))

(defn test-lexicon-well-typed
  "Tests whether `lexicono' assigns well-typed object terms to the
  abstract constants in `test-consts'."
  [lexicono test-consts]
  (doseq [abs-const test-consts
          obj-term (map unreify-term
                        (l/run* [obj-term]
                                (lexicono (rt abs-const) obj-term)))]
    (let [obj-term-types (l/run* [obj-term-type]
                                 (top-typeo obj-term obj-term-type))]
      (test/is (> (count obj-term-types) 0)
               {:msg "The lexicon licenses only well-typed object terms."
                :abs-const abs-const
                :obj-term obj-term}))))

(defn test-lexicon-homomorphism
  "Tests whether the types of the object terms assigned by `lexicono'
  to the abstract constants in `test-consts' are images of a
  homomorphic extension of some mapping from the atomic abstract types
  to object types."
  [lexicono test-consts]
  (let [type-homos (find-type-homomorphisms lexicono test-consts)]
    (test/is (> (count type-homos) 0)
             {:msg "The lexicon is homomorphic w.r.t. the types."})))

(defn test-lexicon
  "Tests whether `lexicono' defines a proper lexicon from the
  signature `signature'. Restricts the tests over lexical constants
  only to the wordforms listed in `test-wordforms'."
  [signature lexicono test-wordforms]
  (test-lexicon-fn lexicono
                   (all-consts signature
                               test-wordforms))
  (test-lexicon-well-typed lexicono
                           (consts-with-lex-image signature
                                                  lexicono
                                                  test-wordforms))
  (test-lexicon-homomorphism lexicono
                             (well-typed-consts signature
                                                lexicono
                                                test-wordforms)))

(defn test-signature
  "Tests whether `signature' defines at most one constant having the
  same :id. Restricts the tests to the wordforms in `test-wordforms'."
  [signature test-wordforms]
  (let [consts (group-by :id (all-consts signature test-wordforms))]
    (doseq [[id eq-consts] consts]
      (test/is (= (count eq-consts) 1)
               {:msg "There is only one constant in the signature per :id."
                :id id
                :eq-consts eq-consts
                :num-eq-consts (count eq-consts)}))))
