(ns acg-clj.toy-grammar
  "A toy grammar of French based on our lexicon, used to drive the
  development of the toolkit."
  (:require [clojure.core.logic :as l])
  (:use acg-clj.acg
        [acg-clj.termix :only [rt ptn ptnt ptnst]]))

(def l-string-sig
  "A signature of lambda-encoded strings. A string is a function of type
  '[-> Sigma Sigma]. String concatenation is performed by function
  composition."
  {:principal-type '[-> Sigma Sigma]
   :lex-typeo (unityped '[-> Sigma Sigma])})

(def string-sig
  "A signature of the algebra of strings with a binary concatenation
  operator."
  {:principal-type 'Str
   :constants '{++ [-> Str [-> Str Str]]}
   :lex-typeo (unityped 'Str)})

(def ua-stx-sig
  "A signature of syntactic descriptions. On this level, the so-called
  scope ambiguities are not reflected by ambiguities in the
  syntax (\"unambiguous syntax\")."
  {:principal-type 'S
   :lex-typeo (fs-match {{:head {:cat "n"}}       'N
                         {:head {:cat "adj"}}     '[-> N N]
                         {:head {:cat "det"}}     '[-> N NP]
                         {:head {:cat "v"
                                 :trans "false"}} '[-> NP S]})})

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
   :lex-typeo (fs-match {{:head {:cat "n"}}       '[-> E T]
                         {:head {:cat "adj"}}     '[-> E T]
                         {:head {:cat "v"
                                 :trans "false"}} '[-> E T]})})

(def a-stx-sig
  "A signature for a level of syntactical description which
  distinguishes between scopes of constituents, making it feasible for
  producing semantic representations via a lexicon (\"ambiguous
  syntax\")"
  {:principal-type 'S
   :lex-typeo (fs-match {{:head {:cat "n"}}       'N
                         {:head {:cat "adj"}}     '[-> N N]
                         {:head {:cat "v"
                                 :trans "false"}} '[-> NP S]
                         {:head {:cat "det"}}     '[-> N NP]})})


(defn string->l-string-lexo
  "A lexicon from the string signature to the l-string signature.
  Basically just implements the string concatenation operator using
  function composotion."
  [string-constant l-string-term]
  (l/conde [(l/fresh [hypertag l-string-constant]
                     (l/featurec string-constant {:hypertag hypertag})
                     (sig-lexo l-string-sig hypertag l-string-constant)
                     (l/== l-string-term (rt l-string-constant)))]
           [((translate-consts {'++ (rt (ll [x y t] (x (y t))))})
             string-constant l-string-term)]))

(defn ua-stx->string-lexo
  "A lexicon from the ua-stx signature to the string signature.
  Responsible for determining the word order between constituents."
  [ua-stx-constant string-term]
  (with-sig-consts string-sig
    (l/fresh [hypertag string-constant]
             (l/featurec ua-stx-constant {:hypertag hypertag})
             (sig-lexo string-sig hypertag string-constant)
             (let [prefix (rt (ll [x] (++ string-constant x)))
                   suffix (rt (ll [x] (++ x string-constant)))]
               ((fs-match {{:head {:cat "n"}}       (rt string-constant)
                           {:head {:cat "adj"
                                   :order "right"}} suffix
                           {:head {:cat "adj"
                                   :order "left"}}  prefix
                           {:head {:cat "det"}}     prefix
                           {:head {:cat "v"
                                   :trans "false"}} suffix})
                hypertag string-term)))))

(defn a-stx->ua-stx-lexo
  "A lexicon from the a-stx signature to the ua-stx signature. For
  now, it is just an identity function."
  [a-stx-constant ua-stx-term]
  (l/fresh [hypertag ua-stx-constant]
           (l/featurec a-stx-constant {:hypertag hypertag})
           (sig-lexo ua-stx-sig hypertag ua-stx-constant)
           ((fs-match {{:head {:cat "n"}}       (rt ua-stx-constant)
                       {:head {:cat "adj"}}     (rt ua-stx-constant)
                       {:head {:cat "v"
                               :trans "false"}} (rt ua-stx-constant)
                       {:head {:cat "det"}}     (rt ua-stx-constant)})
            hypertag ua-stx-term)))

(defn a-stx->sim-sem-lexo
  "A lexicon from the a-stx signature to the sim-sem signature.
  Determines how the predicates of the individual constituents
  combine, implements determiners."
  [a-stx-constant sim-sem-term]
  (with-sig-consts sim-sem-sig
    (l/fresh [hypertag sim-sem-constant]
             (l/featurec a-stx-constant {:hypertag hypertag})
             (l/conde [(sig-lexo sim-sem-sig hypertag sim-sem-constant)
                       ((fs-match {{:head {:cat "n"}}
                                   ,(rt sim-sem-constant)
                                   {:head {:cat "adj"}}
                                   ,(rt (ll [n] (il [x] (and? (sim-sem-constant x)
                                                              (n x)))))
                                   {:head {:cat "v"
                                           :trans "false"}}
                                   ,(rt (ll [S]
                                            (S (ll [x] (sim-sem-constant x)))))})
                        hypertag sim-sem-term)]
                      [((fs-match {{:head {:cat "det"
                                           :det_type "indef"}}
                                   ,(rt (ll [p q] (exists? (il [x] (and? (p x)
                                                                         (q x))))))})
                        hypertag sim-sem-term)]))))
