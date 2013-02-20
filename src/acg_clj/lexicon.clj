(ns acg-clj.lexicon
  (:require [clojure.java.io :as io]
            [clojure.string :as string]
            [clojure.core.logic :as l]
            [clojure.core.logic.nominal :as n]))

(defn parse-hypertag [hypertag-text]
  (reduce (partial apply assoc-in)
          {}
          (for [assignment (string/split hypertag-text #", ")]
            (let [[fpath fval] (string/split assignment #"=")
                  fpath (map keyword (string/split fpath #"\."))
                  fval (string/split fval #"\|")]
              [fpath fval]))))

(defn read-lexicon [lex-lines]
  (apply merge-with
         concat
         (for [line lex-lines]
           (let [[wordform lemma hypertag] (string/split line #"\t")
                 hypertag (parse-hypertag hypertag)
                 hypertag (assoc-in hypertag [:head :lemma] [lemma])
                 hypertag (assoc-in hypertag [:head :wordform] [wordform])]
             {wordform [hypertag]}))))


(def lex-dump "../frig/frilex/frilex.dump")

(def sample-size 10000)

(defonce sample-lines
  (with-open [lex-rdr (io/reader lex-dump)]
    (let [lex-lines (take sample-size (line-seq lex-rdr))]
      (doall lex-lines))))

(defonce sample-lexicon
  (read-lexicon sample-lines))


#_(defonce lexicon
  (with-open [lex-rdr (io/reader lex-dump)]
    (read-lexicon (line-seq lex-rdr))))




(defn string-grammar [hypertag constant]
  (l/fresh [wordform wordforms]
           (l/== hypertag (l/partial-map {:head (l/partial-map {:wordform wordforms})}))
           (l/membero wordform wordforms)
           (l/== constant {:type 'Str
                           :value wordform})))

(defn unamb-syntax-grammar [hypertag constant]
  (let [++ {:type '[-> Str [-> Str Str]]
            :value (with-meta (fn [x]
                                (fn [y]
                                  (str x " " y)))
                     {:print-as '++})}]
    (l/fresh [string-constant cats cat]
             (string-grammar hypertag string-constant)
             (l/== hypertag (l/partial-map {:head (l/partial-map {:cat cats})}))
             (l/membero cat cats)
             (l/conde [(l/== cat "n")
                       (l/== constant {:type 'N
                                       :unamb-syntax->string string-constant})]
                      [(l/== cat "adj")
                       (l/== (l/partial-map {:head (l/partial-map {:order ["right"]})})
                             hypertag)
                       (n/fresh [x]
                                (l/== constant
                                      {:type '[-> N N]
                                       :unamb-syntax->string
                                       ['llam (n/tie x
                                                     ['app ['app ++ x]
                                                      string-constant])]}))]
                      [(l/== cat "det")
                       (l/fresh [det-type det-types]
                                (l/== (l/partial-map {:head (l/partial-map {:det_type det-types})})
                                      hypertag)
                                (l/membero det-type det-types)
                                (n/fresh [x]
                                         (l/== constant
                                               {:type '[-> N NP]
                                                :unamb-syntax->string
                                                ['llam (n/tie x
                                                              ['app ['app ++ string-constant]
                                                               x])]})))]
                      [(l/== cat "v")
                       (l/== (l/partial-map {:head (l/partial-map {:trans ["false"]})})
                             hypertag)
                       (n/fresh [x]
                                (l/== constant
                                      {:type '[-> NP S]
                                       :unamb-syntax->string
                                       ['llam (n/tie x
                                                     ['app ['app ++ x]
                                                      string-constant])]}))]))))

(defn simple-semantics-grammar [hypertag constant]
  (l/fresh [wordform wordforms cat cats]
           (l/== hypertag (l/partial-map {:head (l/partial-map {:wordform wordforms
                                                                :cat cats})}))
           (l/membero wordform wordforms)
           (l/membero cat cats)
           (l/conde [(l/== cat "n")
                     (l/project [wordform]
                                (l/== constant {:type '[-> E T]
                                                :value (with-meta (fn [arg] ; TODO: Shake and bake the function metadata.
                                                                    (println "Testing if" arg "is a" wordform "."))
                                                         {:print-as (symbol wordform)})}))]
                    [(l/== cat "adj")
                     (l/project [wordform]
                                (l/== constant {:type '[-> E T]
                                                :value (with-meta (fn [arg] ; TODO: Same as above.
                                                                    (println "Testing if" arg "was done in a" wordform "way."))
                                                         {:print-as (symbol wordform)})}))]
                    [(l/== cat "v")
                     (l/== hypertag (l/partial-map {:head (l/partial-map {:trans ["false"]})}))
                     (l/project [wordform]
                                (l/== constant {:type '[-> E T]
                                                :value (with-meta (fn [arg] ; TODO: Some more shake and bake.
                                                                    (println "Testing if "arg "was doing" wordform "."))
                                                         {:print-as (symbol wordform)})}))])))

(defn amb-syntax-grammar [hypertag constant]
  (let [and {:type '[-> T [-> T T]]
             :value (with-meta (fn [x]
                                 (fn [y]
                                   (and x y)))
                      {:print-as 'and})}
        or {:type '[-> T [-> T T]]
            :value (with-meta (fn [x]
                                (fn [y]
                                  (or x y)))
                     {:print-as 'or})}
        not {:type '[-> T T]
             :value (with-meta not
                      {:print-as 'not})}
        imp {:type '[-> T [-> T T]]
             :value (with-meta (fn [x]
                                 (fn [y]
                                   (or (not x) y)))
                      {:print-as 'imp})}
        top {:type 'T
             :value true}
        bot {:type 'T
             :value false}
        forall {:type '[-> [=> E T] T]
                :value (with-meta (fn [pred]
                                    (println "Checking that" pred "holds for everything."))
                         {:print-as 'forall})}
        exists {:type '[-> [=> E T] T]
                :value (with-meta (fn [pred]
                                    (println "Checking that" pred "holds for something."))
                         {:print-as 'exists})}]
    (l/fresh [unamb-syntax-constant simple-semantics-constant cat cats]
             (unamb-syntax-grammar hypertag unamb-syntax-constant)
             (l/== hypertag (l/partial-map {:head (l/partial-map {:cat cats})}))
             (l/membero cat cats)
             (l/conde [(l/== cat "n")
                       (simple-semantics-grammar hypertag simple-semantics-constant)
                       (l/== constant {:type 'N
                                       :amb-syntax->unamb-syntax unamb-syntax-constant
                                       :amb-syntax->simple-semantics simple-semantics-constant})]
                      [(l/== cat "adj")
                       (simple-semantics-grammar hypertag simple-semantics-constant)
                       (l/== constant {:type '[-> N N]
                                       :amb-syntax->unamb-syntax unamb-syntax-constant
                                       :amb-syntax->simple-semantics simple-semantics-constant})]
                      [(l/== cat "v")
                       (l/== (l/partial-map {:head (l/partial-map {:trans ["false"]})})
                             hypertag)
                       (simple-semantics-grammar hypertag simple-semantics-constant)
                       (n/fresh [S x]
                                (l/== constant {:type '[-> NP S]
                                                :amb-syntax->unamb-syntax unamb-syntax-constant
                                                :amb-syntax->simple-semantics ['llam (n/tie S ['app S ['llam (n/tie x ['app simple-semantics-constant x])]])]}))]
                      [(l/== cat "det")
                       (l/fresh [det-type det-types]
                                (l/== hypertag (l/partial-map {:head (l/partial-map {:det_type det-types})}))
                                (l/membero det-type det-types)
                                (l/conde [(l/== det-type "indef")
                                          (n/fresh [p q x]
                                                   (l/== constant {:type '[-> N NP]
                                                                   :amb-syntax->unamb-syntax unamb-syntax-constant
                                                                   :amb-syntax->simple-semantics ['llam (n/tie p ['llam (n/tie q ['app exists ['ilam (n/tie x
                                                                                                                                                            ['app ['app and ['app p x]] ['app q x]])]])])]}))]))]))))
