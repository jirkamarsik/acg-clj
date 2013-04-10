(ns acg-clj.examples.toy-grammar
  "A toy grammar of French based on our lexicon, used to drive the
  development of the toolkit."
  (:require [clojure.core.logic :as l])
  (:use (acg-clj acg
                 lambda
                 [termix :only [rt]])))

(def l-string-sig
  "A signature of lambda-encoded strings. A string is a function of type
  '[-> Sigma Sigma]. String concatenation is performed by function
  composition."
  {:principal-type '[-> Sigma Sigma]
   :lex-typespeco (unitypedr '[-> Sigma Sigma])})

(def string-sig
  "A signature of the algebra of strings with a binary concatenation
  operator."
  {:principal-type 'Str
   :constants '{++ [-> Str [-> Str Str]]}
   :lex-typespeco (unitypedr 'Str)})

(def ua-stx-sig
  "A signature of syntactic descriptions. On this level, scope
  ambiguities should not become syntactic ambiguities."
  {:principal-type 'S
   :lex-typespeco (ht->typer '{{:head {:cat "n"}}       N
                               {:head {:cat "adj"
                                       :order "left"}}  [-> N N]
                               {:head {:cat "adj"
                                       :order "right"}} [-> N N]
                               {:head {:cat "det"}}     [-> N NP]
                               {:head {:cat "v"
                                       :trans "false"}} [-> NP S]
                               {:head {:cat "v"
                                       :trans "true"}}  [-> NP [-> NP S]]})})

(def sim-sem-sig
  "A signature for simple semantic representations. Contains the usual
  logical furniture and predicates for the lexical items."
  {:principal-type 'T
   :constants '{and?    [-> T [-> T T]]
                or?     [-> T [-> T T]]
                not?    [-> T T]
                imp?    [-> T [-> T T]]
                top     T
                bottom  T
                forall? [-> [=> E T] T]
                exists? [-> [=> E T] T]}
   :lex-typespeco (ht->typer '{{:head {:cat "n"}}       [=> E T]
                               {:head {:cat "adj"}}     [-> E T]
                               {:head {:cat "v"
                                       :trans "false"}} [-> E T]
                               {:head {:cat "v"
                                       :trans "true"}}  [-> E [-> E T]]})})

(def a-stx-sig
  "A signature for a level of syntactical description which
  distinguishes between different scopes of verb readings by
  type-raising quantified noun phrases."
  {:principal-type 'S
   :lex-typespeco (ht->typer '{{:head {:cat "n"}}       N
                               {:head {:cat "adj"
                                       :order "left"}}  [-> N N]
                               {:head {:cat "adj"
                                       :order "right"}} [-> N N]
                               {:head {:cat "v"
                                       :trans "false"}} [-> NP S]
                               {:head {:cat "v"
                                       :trans "true"}}  [-> NP [-> NP S]]
                               {:head {:cat "det"}}     [-> N [-> [-> NP S] S]]})})


(defn string->l-string-lexo
  "A lexicon from the string signature to the l-string signature.
  Basically just implements the string concatenation operator using
  function composotion."
  [string-constant l-string-term]
  (l/conde [(l/fresh [l-string-constant]
                     (share-lex-entryo string-constant l-string-constant)
                     ((sig-lexr l-string-sig) l-string-constant)
                     (l/== l-string-term (rt l-string-constant)))]
           [((const-lexiconr {'++ (rt (ll [x y t] (x (y t))))})
             string-constant l-string-term)]))

(defn ua-stx->string-lexo
  "A lexicon from the ua-stx signature to the string signature.
  Responsible for determining the word order between constituents."
  [ua-stx-constant string-term]
  (with-sig-consts string-sig
    (l/fresh [string-constant hypertag]
             (share-lex-entryo ua-stx-constant string-constant)
             ((sig-lexr string-sig) string-constant)
             (has-hypertago ua-stx-constant hypertag)
             (let [prefix (rt (ll [x] (++ string-constant x)))
                   suffix (rt (ll [x] (++ x string-constant)))
                   infix (rt (ll [x y] (++ (++ x string-constant) y)))]
               (fs-assigne hypertag                 string-term
                           {:head {:cat "n"}}       (rt string-constant)
                           {:head {:cat "adj"
                                   :order "right"}} suffix
                           {:head {:cat "adj"
                                   :order "left"}}  prefix
                           {:head {:cat "det"}}     prefix
                           {:head {:cat "v"
                                   :trans "false"}} suffix
                           {:head {:cat "v"
                                   :trans "true"}}  infix)))))

(defn a-stx->ua-stx-lexo
  "A lexicon from the a-stx signature to the ua-stx signature.
  `Undoes` the type-raising of quantified noun phrases."
  [a-stx-constant ua-stx-term]
  (l/fresh [ua-stx-constant hypertag]
           (share-lex-entryo a-stx-constant ua-stx-constant)
           ((sig-lexr ua-stx-sig) ua-stx-constant)
           (has-hypertago a-stx-constant hypertag)
           (fs-assigne hypertag ua-stx-term
                       {:head {:cat "n"}}
                       ,(rt ua-stx-constant)
                       {:head {:cat "adj"}}
                       ,(rt ua-stx-constant)
                       {:head {:cat "v"}}
                       ,(rt ua-stx-constant)
                       {:head {:cat "det"}}
                       ,(rt (ll [x R] (R (ua-stx-constant x)))))))

(defn a-stx->sim-sem-lexo
  "A lexicon from the a-stx signature to the sim-sem signature.
  Determines how the predicates of the individual constituents
  combine, implements determiners."
  [a-stx-constant sim-sem-term]
  (with-sig-consts sim-sem-sig
    (l/fresh [sim-sem-constant hypertag]
             (has-hypertago a-stx-constant hypertag)
             (l/conde [(share-lex-entryo a-stx-constant sim-sem-constant)
                       ((sig-lexr sim-sem-sig) sim-sem-constant)
                       (fs-assigne hypertag sim-sem-term
                                   {:head {:cat "n"}}
                                   ,(rt sim-sem-constant)
                                   {:head {:cat "adj"}}
                                   ,(rt (ll [n] (il [x] (and? (sim-sem-constant x)
                                                              (n x)))))
                                   {:head {:cat "v"}}
                                   ,(rt sim-sem-constant))]
                      [(fs-assigne hypertag sim-sem-term
                                   {:head {:cat "det"
                                           :det_type "indef"}}
                                   ,(rt (ll [p q] (exists? (il [x] (and? (p x)
                                                                         (q x))))))
                                   {:head {:cat "det"
                                           :det_type "def"}}
                                   ,(rt (ll [p q] (forall? (il [x] (imp? (p x)
                                                                         (q x)))))))]))))
