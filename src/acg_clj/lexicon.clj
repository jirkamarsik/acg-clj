(ns acg-clj.lexicon
  "Code needed to load in the lexicon produced by a Lexicomp dump and
  to provide a relational interface to its contents."
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
                  fpath (map keyword (string/split fpath #"\."))
                  fval (string/split fval #"\|")]
              [fpath fval]))))

(defn read-lexicon
  "Given the lines of a Lexicomp dump file, produces a lexicon in the
  form of a map from wordforms to vectors of possible
  hypertags (enriched with head.wordform and head.lemma)."
  [lex-lines]
  (persistent!
   (reduce (fn [lex [wordform hypertag]]
             (assoc! lex wordform (conj (get lex wordform []) hypertag)))
           (transient {})
           (for [line lex-lines]
             (let [[wordform lemma hypertag] (string/split line #"\t")
                   hypertag (parse-hypertag hypertag)
                   hypertag (assoc-in hypertag [:head :lemma] [lemma])
                   hypertag (assoc-in hypertag [:head :wordform] [wordform])]
               [wordform hypertag])))))

(def lex-dump
  "Path to the Lexicomp dump file from which we will read our
  lexicon."
  "../frig/frilex/frilex.dump")

(defonce ^{:doc "Our lexicon, a map from wordforms to vectors of possible
  hypertags."} lexicon
  (with-open [lex-rdr (io/reader lex-dump)]
    (read-lexicon (line-seq lex-rdr))))


(defn membero!
  "Just like core.logic's membero, but assumes its second argument `l'
  is a fully grounded collection. In return, succeeding K times only
  takes time proportional to K, not to the size of the (potentially
  infinite) collection `l'."
  [x l]
  (if (seq l)
    (l/conde [(l/== x (first l))]
             [(membero! x (next l))])
    l/fail))

;; TODO: The lexicon should undo the factorization done using
;;       optional features in Frilex.
(defn lexicono
  "The relation interface to the lexicon. Succeeds if `hypertag' is a
  valid hypertag for the wordform `wordform'. Tries to be as efficient
  as possible given the groundedness of its arguments."
  [wordform hypertag]
  (l/project [wordform hypertag]
             (if (and (l/lvar? wordform)
                      (map? hypertag)
                      (map? (:head hypertag))
                      (coll? (:wordform (:head hypertag))))
               (l/membero wordform (:wordform (:head hypertag)))
               l/succeed)
             (l/project [wordform]
                        (if (string? wordform)
                          (l/membero hypertag (lexicon wordform))
                          (l/fresh [hypertags]
                                   (membero! [wordform hypertags] lexicon)
                                   (l/membero hypertag hypertags))))))

(defn hypertago
  "Is `hypertag' a valid hypertag in our lexicon. A shortcut for
  lexicono."
  [hypertag]
  (l/fresh [wordform]
           (lexicono wordform hypertag)))

