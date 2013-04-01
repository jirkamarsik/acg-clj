(ns acg-clj.toy-grammar2
  "A toy grammar of French based on our lexicon, used to drive the
  development of the toolkit.

  This is the version that uses different lexical constants for verbs
  to produce scope ambiguities."
  (:require [clojure.core.logic :as l])
  (:use acg-clj.acg
        acg-clj.check
        acg-clj.convenience
        acg-clj.lambda
        [acg-clj.termix :only [rt ptn ptnt ptnst]]
        [acg-clj.toy-grammar :only [l-string-sig string-sig sim-sem-sig
                                    string->l-string-lexo]]))

(def stx-sig
  "A signature for a level of syntactical description which
  distinguishes between different scope readings of verbs by using
  different constants for each reading."
  {:principal-type 'S
   :lex-typespeco (fn [hypertag type spec]
                    (l/conde [(fs-assigne hypertag                 type
                                          {:head {:cat "n"}}       'N
                                          {:head {:cat "adj"
                                                  :order "left"}}  '[-> N N]
                                          {:head {:cat "adj"
                                                  :order "right"}} '[-> N N]
                                          {:head {:cat "v"
                                                  :trans "false"}} '[-> NP S]
                                          {:head {:cat "det"}}     '[-> N NP])
                              (l/== spec nil)]
                             [(fs-matche hypertag
                                         [{:head {:cat "v"
                                                  :trans "true"}}
                                          (l/== type '[-> NP [-> NP S]])
                                          (l/membero spec [{:scope :subject} {:scope :object}])])]))})


(defn stx->string-lexo
  "A lexicon from the stx signature to the string signature.
  Responsible for determining the word order between constituents."
  [stx-constant string-term]
  (with-sig-consts string-sig
    (l/fresh [string-constant hypertag]
             (share-lex-entryo stx-constant string-constant)
             (sig-lexo string-sig string-constant)
             (has-hypertago stx-constant hypertag)
             (let [prefix (rt (ll [x] (++ string-constant x)))
                   suffix (rt (ll [x] (++ x string-constant)))]
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
                                   :trans "true"}}  (rt (ll [x y] (++ (++ x string-constant) y))))))))

(defn stx->sim-sem-lexo
  "A lexicon from the a-stx signature to the sim-sem signature.
  Determines how the predicates of the individual constituents
  combine, implements determiners."
  [stx-constant sim-sem-term]
  (with-sig-consts sim-sem-sig
    (l/fresh [sim-sem-constant hypertag]
             (has-hypertago stx-constant hypertag)
             (l/conde [(share-lex-entryo stx-constant sim-sem-constant)
                       (sig-lexo sim-sem-sig sim-sem-constant)
                       (fs-assigne hypertag sim-sem-term
                                   {:head {:cat "n"}}
                                   ,(rt sim-sem-constant)
                                   {:head {:cat "adj"}}
                                   ,(rt (ll [n] (il [x] (and? (sim-sem-constant x)
                                                              (n x)))))
                                   {:head {:cat "v"
                                           :trans "false"}}
                                   ,(rt (ll [S] (S (ll [x] (sim-sem-constant x))))))]
                      [(share-lex-entryo stx-constant sim-sem-constant)
                       (sig-lexo sim-sem-sig sim-sem-constant)
                       (fs-matche hypertag
                                  [{:head {:cat "v"
                                           :trans "true"}}
                                   (l/fresh [spec]
                                            (has-speco stx-constant spec)
                                            (l/conde [(l/== spec {:scope :subject})
                                                      (l/== sim-sem-term ,(rt (ll [O S] (S [ll [x] (O (ll [y] (sim-sem-constant x y)))]))))]
                                                     [(l/== spec {:scope :object})
                                                      (l/== sim-sem-term ,(rt (ll [O S] (O [ll [y] (S (ll [x] (sim-sem-constant x y)))]))))]))])]
                      [(fs-assigne hypertag sim-sem-term
                                   {:head {:cat "det"
                                           :det_type "indef"}}
                                   ,(rt (ll [p q] (exists? (il [x] (and? (p x)
                                                                         (q x))))))
                                   {:head {:cat "det"
                                           :det_type "def"}}
                                   ,(rt (ll [p q] (forall? (il [x] (imp? (p x)
                                                                         (q x)))))))]))))


(let [test-wordforms ["une" "les" "dort" "mangent" "grand" "vert" "enfant"]]
  (doseq [[sig lexo] [[stx-sig stx->sim-sem-lexo]
                      [stx-sig stx->string-lexo]]]
    (test-lexicon-fn? sig (lexo-extend lexo) test-wordforms)
    (test-lexicon-homo? sig (lexo-extend lexo) test-wordforms)))
