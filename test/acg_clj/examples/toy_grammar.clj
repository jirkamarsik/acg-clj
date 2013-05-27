(ns acg-clj.examples.toy-grammar
  "A toy grammar of French based on our lexicon, used to drive the
  development of the toolkit."
  (:refer-clojure :exclude [->])
  (:require [clojure.core.logic :as l])
  (:use (acg-clj [acg :rename {--> ->, ==> =>}]
                 lambda
                 [termix :only [rt]]
                 utils)))

(def l-string-sig
  "A signature of lambda-encoded strings. A string is a function of type
  '[-> Sigma Sigma]. String concatenation is performed by function
  composition."
  (unitypedr (-> 'Sigma 'Sigma)))

(def string-sig
  "A signature of the algebra of strings with a binary concatenation
  operator."
  (ors (nonlex-sigr {'++ (-> 'Str 'Str 'Str)})
       (unitypedr 'Str)))

(def ua-stx-sig
  "A signature of syntactic descriptions. On this level, scope
  ambiguities should not become syntactic ambiguities."
  (ht->typer {{:head {:cat "n"}}       'N
              {:head {:cat "adj"
                      :order "left"}}  (-> 'N 'N)
              {:head {:cat "adj"
                      :order "right"}} (-> 'N 'N)
              {:head {:cat "det"}}     (-> 'N 'NP)
              {:head {:cat "v"
                      :trans "false"}} (-> 'NP 'S)
              {:head {:cat "v"
                      :trans "true"}}  (-> 'NP 'NP 'S)}))

(def sim-sem-sig
  "A signature for simple semantic representations. Contains the usual
  logical furniture and predicates for the lexical items."
  (ors (nonlex-sigr {'and?    (-> 'T 'T 'T)
                     'or?     (-> 'T 'T 'T)
                     'not?    (-> 'T 'T)
                     'imp?    (-> 'T 'T 'T)
                     'top     'T
                     'bottom  'T
                     'forall? (-> (=> 'E 'T) 'T)
                     'exists? (-> (=> 'E 'T) 'T)})
       (ht->typer {{:head {:cat "n"}}       (=> 'E 'T)
                   {:head {:cat "adj"}}     (-> 'E 'T)
                   {:head {:cat "v"
                           :trans "false"}} (-> 'E 'T)
                   {:head {:cat "v"
                           :trans "true"}}  (-> 'E 'E 'T)})))

(def a-stx-sig
  "A signature for a level of syntactical description which
  distinguishes between different scopes of verb readings by
  type-raising quantified noun phrases."
  (ht->typer {{:head {:cat "n"}}       'N
              {:head {:cat "adj"
                      :order "left"}}  (-> 'N 'N)
              {:head {:cat "adj"
                      :order "right"}} (-> 'N 'N)
              {:head {:cat "v"
                      :trans "false"}} (-> 'NP 'S)
              {:head {:cat "v"
                      :trans "true"}}  (-> 'NP 'NP 'S)
              {:head {:cat "det"}}     (-> 'N (-> 'NP 'S) 'S)}))


(def string->l-string-lexo
  "A lexicon from the string signature to the l-string signature.
  Basically just implements the string concatenation operator using
  function composotion."
  (orr (nonlex-lexiconr {'++ (rt (ll [x y t] (x (y t))))})
       (lexicalizer l-string-sig (const-lexiconr (rt (ll [_] _))))))

(def ua-stx->string-lexo
  "A lexicon from the ua-stx signature to the string signature.
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

(def a-stx->ua-stx-lexo
  "A lexicon from the a-stx signature to the ua-stx signature.
  `Undoes` the type-raising of quantified noun phrases."
  (lexicalizer ua-stx-sig
               (ht-lexiconr {{:head {:cat "n"}}
                             ,(rt (ll [_] _))
                             {:head {:cat "adj"}}
                             ,(rt (ll [_] _))
                             {:head {:cat "v"}}
                             ,(rt (ll [_] _))
                             {:head {:cat "det"}}
                             ,(rt (ll [_ x R] (R (_ x))))})))

(def a-stx->sim-sem-lexo
  "A lexicon from the a-stx signature to the sim-sem signature.
  Determines how the predicates of the individual constituents
  combine, implements determiners."
  (with-sig-consts sim-sem-sig
    (orr (lexicalizer sim-sem-sig
                      (ht-lexiconr {{:head {:cat "n"}}
                                    ,(rt (ll [_] _))
                                    {:head {:cat "adj"}}
                                    ,(rt (ll [_ n] (il [x] (and? (_ x) (n x)))))
                                    {:head {:cat "v"}}
                                    ,(rt (ll [_] _))}))
         (ht-lexiconr {{:head {:cat "det"
                               :det_type "indef"}}
                       ,(rt (ll [p q] (exists? (il [x] (and? (p x) (q x))))))
                       {:head {:cat "det"
                               :det_type "def"}}
                       ,(rt (ll [p q] (forall? (il [x] (imp? (p x) (q x))))))}))))
