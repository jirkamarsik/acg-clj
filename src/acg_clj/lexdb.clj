(ns acg-clj.lexdb
  "Code needed to load in the lexical database produced by a Lexicomp
  dump and to provide a relational interface to its contents."
  (:require [clojure.java.io :as io]
            [clojure.string :as string]
            [clojure.core.logic :as l]
            [monads.core :refer :all]
            [monads.util :refer [sequence-m msum fold-m]]
            [monads.list :as list])
  (:use plumbing.core)
  (:use (acg-clj utils)))

(defn parse-hypertag
  "Translates a representation of a hypertag used in Lexicomp's dump
  files into a nested map."
  [hypertag-text]
  (reduce (partial apply assoc-in)
          {}
          (for [assignment (string/split hypertag-text #", ")]
            (let [[fpath fval] (string/split assignment #"=")
                  fpath (map keyword (string/split fpath #"\."))
                  fval (string/split fval #"\|")]
              [fpath fval]))))

(defn read-lexdb
  "Given the lines of a Lexicomp dump file, produces a lexical
  database in the form of a map from wordforms to vectors of possible
  hypertags (enriched with head.lemma)."
  [lex-lines]
  (persistent!
   (reduce (fn [lex [wordform hypertag]]
             (assoc! lex wordform (conj (get lex wordform []) hypertag)))
           (transient {})
           (for [line lex-lines]
             (let [[wordform lemma hypertag] (string/split line #"\t")
                   hypertag (parse-hypertag hypertag)
                   hypertag (assoc-in hypertag [:head :lemma] [lemma])]
               [wordform hypertag])))))

(def lex-dump
  "Path to the Lexicomp dump file from which we will read our
  lexical database."
  "../frig/frilex/frilex.dump")

(defonce ^{:doc "Our lexical database, a map from wordforms to vectors
  of possible hypertags."} lexdb
  (with-open [lex-rdr (io/reader lex-dump)]
    (read-lexdb (line-seq lex-rdr))))


(defn membero!
  "Just like core.logic's membero, but assumes its second argument `l'
  is a fully grounded collection. In return, succeeding K times only
  takes time proportional to K, not to the size of the (potentially
  infinite) collection `l'."
  [x l]
  (if (seq l)
    (l/conde [(l/== x (first l))]
             [(membero! x (rest l))])
    l/fail))


(defn opt-feat?
  "Tests whether `key' is an optional feature (ends with '?')."
  [key]
  (.endsWith (name key) "?"))

(defn remove-question-mark
  "Strips away the last character of a keyword."
  [key]
  (let [n (name key)]
    (keyword (namespace key) (.substring n 0 (dec (count n))))))

(defn conj-me-maybe
  "Conjes the `[k v]' pair into the `hypertag'... or not, depending
  on whether `k' is optional (?). Returns a monadic value."
  [hypertag [k v]]
  (if (opt-feat? k)
    (mplus (return (conj hypertag [(remove-question-mark k) v]))
           (return hypertag))
    (return (conj hypertag [k v]))))

(defn factor-opt-feats
  "Turns every optional feature in `hypertag' into either a mandatory
  feature or no feature. Returns a monadic value."
  [hypertag]
  (if (map? hypertag)
    (>>= (fold-m conj-me-maybe {} hypertag)
         (partial map-vals-m factor-opt-feats))
    (return hypertag)))

(defn factor-alt-values
  "Turns every list of possible feature values in `hypertag' into one of
  the possible values. Returns a monadic value."
  [hypertag]
  (cond (map? hypertag) (map-vals-m factor-alt-values hypertag)
        (vector? hypertag) (msum (map return hypertag))
        :else (return hypertag)))

(defn factor-hypertag
  "Given a `hypertag' with optional features and vectors of possible
  values for feature values, returns a sequence of all the hypertags with
  each feature either made mandatory or removed, with each feature having
  only one possible value."
  [hypertag]
  (run-monad list/m (reduce >>= (return hypertag)
                            [factor-opt-feats factor-alt-values])))


;; TODO: lexdbo should undo the factorization done using
;;       optional features in Frilex.
(defn lexdbo
  "The relation interface to the lexical database. Succeeds if
  `hypertag' is a valid hypertag for the wordform `wordform'. Tries to
  be as efficient as possible given the groundedness of its
  arguments."
  [wordform hypertag]
  (l/project [wordform]
             (if (string? wordform)
               (l/membero hypertag (lexdb wordform))
               (l/fresh [hypertags]
                        (membero! [wordform hypertags] lexdb)
                        (l/membero hypertag hypertags)))))
