(ns acg-clj.examples.toy-grammar2
  "A toy grammar of French based on our lexicon, used to drive the
  development of the toolkit.

  This is the version that uses different lexical constants for verbs
  to produce scope ambiguities."
  (:refer-clojure :exclude [->])
  (:require [clojure.core.logic :as l])
  (:use (acg-clj [acg :rename {--> ->, ==> =>}]
                 lambda
                 [termix :only [rt]]
                 utils)
        [acg-clj.examples.toy-grammar :only [l-string-sig string-sig sim-sem-sig
                                             string->l-string-lexo]]))

(def stx-sig
  "A signature for a level of syntactical description which
  distinguishes between different scope readings of verbs by using
  different constants for each reading."
  (ors (ht->typer {{:head {:cat "n"}}       'N
                   {:head {:cat "adj"
                           :order "left"}}  (-> 'N 'N)
                   {:head {:cat "adj"
                           :order "right"}} (-> 'N 'N)
                   {:head {:cat "v"
                           :trans "false"}} (-> 'NP 'S)
                   {:head {:cat "det"}}     (-> 'N 'NP)})
       (lex-sigr (fn [wordform hypertag spec type]
                   (fs-matche hypertag
                              [{:head {:cat "v"
                                       :trans "true"}}
                               (l/== type (-> 'NP 'NP 'S))
                               (l/membero spec [{:scope :subject}
                                                {:scope :object}])])))))


(def stx->string-lexo
  "A lexicon from the stx signature to the string signature.
  Responsible for determining the word order between constituents."
  (with-sig-consts string-sig
    (let [const (rt (ll [_] _))
          prefix (rt (ll [_ x] (++ _ x)))
          suffix (rt (ll [_ x] (++ x _)))
          infix (rt (ll [_ x y] (++ (++ x _) y)))]
      (lexicalizer string-sig
                   (ht-lexiconr {{:head {:cat "n"}}       const
                                 {:head {:cat "adj"
                                         :order "right"}} suffix
                                 {:head {:cat "adj"
                                         :order "left"}}  prefix
                                 {:head {:cat "det"}}     prefix
                                 {:head {:cat "v"
                                         :trans "false"}} suffix
                                 {:head {:cat "v"
                                         :trans "true"}}  infix})))))

(def stx->sim-sem-lexo
  "A lexicon from the a-stx signature to the sim-sem signature.
  Determines how the predicates of the individual constituents
  combine, implements determiners."
  (with-sig-consts sim-sem-sig
    (orr (lexicalizer sim-sem-sig
                      (orr (ht-lexiconr {{:head {:cat "n"}}
                                         ,(rt (ll [_] _))
                                         {:head {:cat "adj"}}
                                         ,(rt (ll [_ n] (il [x] (and? (_ x) (n x)))))
                                         {:head {:cat "v"
                                                 :trans "false"}}
                                         ,(rt (ll [_ S] (S (ll [x] (_ x)))))})
                           (fn [stx-constant sim-sem-term]
                             (l/fresh [hypertag]
                               (has-hypertago stx-constant hypertag)
                               (fs-matche hypertag
                                 [{:head {:cat "v"
                                          :trans "true"}}
                                  (l/fresh [spec]
                                    (has-speco stx-constant spec)
                                    (l/conde [(l/== spec {:scope :subject})
                                              (l/== sim-sem-term
                                                    ,(rt (ll [_ O S] (S (ll [x] (O (ll [y] (_ x y))))))))]
                                             [(l/== spec {:scope :object})
                                              (l/== sim-sem-term
                                                    ,(rt (ll [_ O S] (O (ll [y] (S (ll [x] (_ x y))))))))]))])))))
         (ht-lexiconr {{:head {:cat "det"
                               :det_type "indef"}}
                       ,(rt (ll [p q] (exists? (il [x] (and? (p x) (q x))))))
                       {:head {:cat "det"
                               :det_type "def"}}
                       ,(rt (ll [p q] (forall? (il [x] (imp? (p x) (q x))))))}))))
