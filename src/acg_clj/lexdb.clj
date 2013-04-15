(ns acg-clj.lexdb
  "Code needed to load in the lexical database produced by a Lexicomp
  dump and to provide a relational interface to its contents."
  (:require [clojure.java.io :as io]
            [clojure.string :as string]
            [clojure.core.logic :as l]))

(defn parse-hypertag
  "Translates a representation of a hypertag used in Lexicomp's dump
  files into a nested map."
  [hypertag-text]
  (reduce (partial apply assoc-in)
          {}
          (for [assignment (string/split hypertag-text #", ")]
            (let [[fpath fval] (string/split assignment #"=")
                  ; The following line fixes a slight inconsistency in
                  ; Lexicomp's dump file format where optional
                  ; features are marked at the end of the feature path
                  ; instead of at the name of the optional feature.
                  ; TODO: Fix in upstream!
                  fpath (string/replace fpath #"(\w+)\.(\w+)\?" "$1?.$2")
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
