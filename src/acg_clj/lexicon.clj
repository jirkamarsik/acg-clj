(ns acg-clj.lexicon
  (:require [clojure.java.io :as io]
            [clojure.string :as string]
            [clojure.core.logic :as l]
            [clojure.core.logic.nominal :as n])
  (:use plumbing.core
        acg-clj.core
        [acg-clj.termix :only [rt ptn ptnt]]))

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


(defonce lexicon
  (with-open [lex-rdr (io/reader lex-dump)]
    (read-lexicon (line-seq lex-rdr))))

#_(defonce lexicon
  sample-lexicon)


(defn membero! [x l]
  (if (seq l)
    (l/conde [(l/== x (first l))]
             [(membero! x (next l))])
    l/fail))

;; TODO: The lexicon should undo the factorization done using
;;       optional features in Frilex.
(defn lexicono [wordform hypertag]
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


;; From clojure.core.logic JIRA
(defn rfeaturec [m f]
  (let [new-f (reduce (fn [m [k v]] (assoc m k (l/lvar (name k)))) {} (seq f))]
    (l/all
      (l/featurec m new-f)
      (l/everyg
       (fn [[k lvar]]
         (let [v (get f k)]
           (if (map? v)
             (l/all
               (l/featurec m {k lvar})
               (rfeaturec lvar v))
             (l/== lvar v))))
       new-f))))

(defn retrievec [hypertag pattern]
  (let [lvar-value-pairs (atom {})
        lvarize (fn lvarize [pat]
                  (if (map? pat)
                    (map-vals lvarize pat)
                    (let [lvar (l/lvar)]
                      (swap! lvar-value-pairs assoc lvar pat)
                      lvar)))
        lvar-pattern (lvarize pattern)]
    (l/all (rfeaturec hypertag lvar-pattern)
           (l/everyg (fn [[lvar val]]
                       (l/membero val lvar))
                     @lvar-value-pairs))))

(defn drop-constraints [result]
  (if (and (seq? result) (= (second result) :-))
    (first result)
    result))

(l/defne apply-lexo [lexo abs-term obj-term]
  ([_ ['var abs-v] _]
     (lexo abs-v obj-term))
  ([_ [lam [v] abs-b] [lam [v] obj-b]]
     (l/membero lam '[llam ilam])
     (apply-lexo lexo abs-b obj-b))
  ([_ ['app abs-f abs-a] ['app obj-f obj-a]]
     (apply-lexo lexo abs-f obj-f)
     (apply-lexo lexo abs-a obj-a)))

(defn hypertago [hypertag]
  (l/fresh [wordform]
           (lexicono wordform hypertag)))


(defn unityped [unitype]
  (fn [hypertag type]
    (l/== type unitype)))

(defmacro fs-match [patterns]
  (let [hypertag-sym (gensym "hypertag")
        out-sym (gensym "out")
        goals (for [[pat val] patterns]
                `[(retrievec ~hypertag-sym ~pat)
                  (l/== ~out-sym ~val)])]
    `(fn [~hypertag-sym ~out-sym]
       (l/conde ~@goals))))

(defn sig-consto [signature name constant]
  (l/fresh [type]
           (l/membero [name type] (seq (:constants signature)))
           (l/== constant {:type type
                           :constant-name name})))

(defn sig-lexo [signature hypertag constant]
  (if (contains? signature :lex-typeo)
    (l/fresh [type]
             (hypertago hypertag)
             ((:lex-typeo signature) hypertag type)
             (l/== constant {:type type
                             :hypertag hypertag}))
    l/fail))

(defn sigo [signature constant]
  (l/conde [(l/fresh [name]
                     (sig-consto signature name constant))]
           [(l/fresh [hypertag]
                     (sig-lexo signature hypertag constant))]))

;; WARNING: Too demanding to run l/run*.
(defn sig-termo [signature term type]
  (let [consts (l/run* [q] (sigo signature q))]
    (typeo (for [const consts] [const :i])
           (for [const consts] [const (:type const)])
           []
           term
           type)))

(defn sig-sento [signature sentence]
  (sig-termo signature sentence (:principal-type signature)))

(defmacro with-sig-consts [signature & goals]
  (let [consts (keys (:constants @(resolve signature)))]
    `(l/fresh ~(vec consts)
              ~@(for [const consts]
                  `(sig-consto ~signature '~const ~const))
              ~@goals)))

(defn translate-consts [translation-map]
  (fn [constant translated-term]
    (l/fresh [constant-name]
             (l/featurec constant {:constant-name constant-name})
             (l/membero [constant-name translated-term] (seq translation-map)))))






(defn sig-findo [signature wordform constant type]
  (l/fresh [hypertag]
           (lexicono wordform hypertag)
           (sig-lexo signature hypertag constant)
           (l/featurec constant {:type type})))

(defn sig-findo' [signature wordform constant]
  (l/fresh [hypertag]
           (lexicono wordform hypertag)
           (sig-lexo signature hypertag constant)))

