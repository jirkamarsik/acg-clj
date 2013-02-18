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


(defn syntax<->string [hypertag out]
  (l/fresh [cats cat wordforms wordform]
           (l/== hypertag (l/partial-map {:head (l/partial-map {:cat cats
                                                                :wordform wordforms})}))
           (l/membero cat cats)
           (l/membero wordform wordforms)
           (l/conde [(l/== cat "n")
                     (l/== out {:type 'N
                                :syntax->string {:type 'Str
                                                 :value wordform}})]
                    [(l/== cat "adj")
                     (l/== (l/partial-map {:head (l/partial-map {:order ["right"]})})
                           hypertag)
                     (n/fresh [x]
                              (l/== out
                                    {:type '[-> N N]
                                     :syntax->string
                                     ['llam (n/tie x
                                                   ['app ['app '+ x]
                                                    {:type 'Str
                                                     :value wordform}])]}))]
                    [(l/== cat "det")
                     (n/fresh [x]
                              (l/== out
                                    {:type '[-> N NP]
                                     :syntax->string
                                     ['llam (n/tie x
                                                   ['app ['app '+ {:type 'Str
                                                                   :value wordform}]
                                                    x])]}))]
                    [(l/== cat "v")
                     (l/== (l/partial-map {:head (l/partial-map {:trans ["false"]})})
                           hypertag)
                     (n/fresh [x]
                              (l/== out
                                    {:type '[-> NP S]
                                     :syntax->string
                                     ['llam (n/tie x
                                                   ['app ['app '+ x]
                                                    {:type 'Str
                                                     :value wordform}])]}))])))


(defn unamb-syntax-grammar [hypertag constant]
  (l/fresh [cats cat wordforms wordform]
           (l/== hypertag (l/partial-map {:head (l/partial-map {:cat cats
                                                                :wordform wordforms})}))
           (l/membero cat cats)
           (l/membero wordform wordforms)
           (l/conde [(l/== cat "n")
                     (l/== out {:type 'N
                                :syntax->string {:type 'Str
                                                 :value wordform}})]
                    [(l/== cat "adj")
                     (l/== (l/partial-map {:head (l/partial-map {:order ["right"]})})
                           hypertag)
                     (n/fresh [x]
                              (l/== out
                                    {:type '[-> N N]
                                     :syntax->string
                                     ['llam (n/tie x
                                                   ['app ['app '+ x]
                                                    {:type 'Str
                                                     :value wordform}])]}))]
                    [(l/== cat "det")
                     (n/fresh [x]
                              (l/== out
                                    {:type '[-> N NP]
                                     :syntax->string
                                     ['llam (n/tie x
                                                   ['app ['app '+ {:type 'Str
                                                                   :value wordform}]
                                                    x])]}))]
                    [(l/== cat "v")
                     (l/== (l/partial-map {:head (l/partial-map {:trans ["false"]})})
                           hypertag)
                     (n/fresh [x]
                              (l/== out
                                    {:type '[-> NP S]
                                     :syntax->string
                                     ['llam (n/tie x
                                                   ['app ['app '+ x]
                                                    {:type 'Str
                                                     :value wordform}])]}))])))






(defn string-grammar [hypertag constant]
  (l/fresh [wordform wordforms]
           (l/== hypertag (l/partial-map {:head (l/partial-map {:wordform wordforms})}))
           (l/membero wordform wordforms)
           (l/== constant {:type 'Str
                           :value wordform})))