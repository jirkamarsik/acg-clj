(ns acg-clj.lexicon
  (:require [clojure.java.io :as io]
            [clojure.string :as string]
            [clojure.core.logic :as l]
            [clojure.core.logic.nominal :as n])
  (:use plumbing.core
        acg-clj.core))

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

(defmulti read-term (fn [term env]
                       (if (sequential? term)
                         (if ('#{ll il} (first term))
                           :lam
                           :app)
                         :var)))

(defmethod read-term :lam [[lam [v & vs :as vars] body] env]
  (if (empty? vars)
    (read-term body env)
    (let [new-env (assoc env v v)
          emitted-lam ('{ll llam, il ilam} lam)]
      [emitted-lam [v] (read-term (list lam vs body) new-env)])))

(defmethod read-term :app [term env]
  (reduce (fn [f a]
            ['app f a])
          (map #(read-term % env) term)))

(defmethod read-term :var [term env]
  (let [maybe-resolved (and (symbol? term) (resolve term))
        term (cond (contains? env term) (get env term)
                   (var? maybe-resolved) (deref maybe-resolved)
                   (class? maybe-resolved) maybe-resolved
                   :else term)]
    ['var term]))

(defmacro rt [term]
  (let [local-env (into {} (for [s (keys &env)]
                             [(list 'quote s) s]))]
    `(read-term '~term ~local-env)))

(def present-term-hierarchy (-> (make-hierarchy)
                              (derive 'llam 'lam)
                              (derive 'ilam 'lam)))

(defmulti present-term first :hierarchy #'present-term-hierarchy)

(defmethod present-term 'app [[app f a]]
  (if (= (first f) 'app)
    (concat (present-term f) (list (present-term a)))
    (list (present-term f) (present-term a))))

(defmethod present-term 'lam [[lam [v] body]]
  (let [written-lam ('{llam ll, ilam il} lam)
        p-body (present-term body)]
    (if (= (first body) lam)
      (let [[_ inner-vars p-body] p-body
            vars (vec (cons v inner-vars))]
        (list written-lam vars p-body))
      (list written-lam [v] p-body))))

(defmethod present-term 'var [[var v]]
  (if (map? v)
    (cond (contains? v :hypertag) (first (get-in v [:hypertag :head :wordform]))
          (contains? v :constant-name) (:constant-name v)
          :else v)
    v))

(def pt present-term)

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




(def l-string-sig
  {:principal-type '[-> Sigma Sigma]
   :lex-typeo (unityped '[-> Sigma Sigma])})

(def string-sig
  {:principal-type 'Str
   :constants '{++ [-> Str [-> Str Str]]}
   :lex-typeo (unityped 'Str)})

(def ua-stx-sig
  {:principal-type 'S
   :lex-typeo (fs-match {{:head {:cat "n"}}       'N
                         {:head {:cat "adj"}}     '[-> N N]
                         {:head {:cat "det"}}     '[-> N NP]
                         {:head {:cat "v"
                                 :trans "false"}} '[-> NP S]})})

(def sim-sem-sig
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
  {:principal-type 'S
   :lex-typeo (fs-match {{:head {:cat "n"}}       'N
                         {:head {:cat "adj"}}     '[-> N N]
                         {:head {:cat "v"
                                 :trans "false"}} '[-> NP S]
                         {:head {:cat "det"}}     '[-> N NP]})})



(defn string->l-string-lexo [string-constant l-string-term]
  (l/conde [(l/fresh [hypertag l-string-constant]
                     (l/featurec string-constant {:hypertag hypertag})
                     (sig-lexo l-string-sig hypertag l-string-constant)
                     (l/== l-string-term (rt l-string-constant)))]
           [((translate-consts {'++ (rt (ll [x y t] (x (y t))))})
             string-constant l-string-term)]))

(defn ua-stx->string-lexo [ua-stx-constant string-term]
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

(defn a-stx->ua-stx-lexo [a-stx-constant ua-stx-term]
  (l/fresh [hypertag ua-stx-constant]
           (l/featurec a-stx-constant {:hypertag hypertag})
           (sig-lexo ua-stx-sig hypertag ua-stx-constant)
           ((fs-match {{:head {:cat "n"}}       (rt ua-stx-constant)
                       {:head {:cat "adj"}}     (rt ua-stx-constant)
                       {:head {:cat "v"
                               :trans "false"}} (rt ua-stx-constant)
                       {:head {:cat "det"}}     (rt ua-stx-constant)})
            hypertag ua-stx-term)))

(defn a-stx->sim-sem-lexo [a-stx-constant sim-sem-term]
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



(defn sig-findo [signature wordform constant type]
  (l/fresh [hypertag]
           (lexicono wordform hypertag)
           (sig-lexo signature hypertag constant)
           (l/featurec constant {:type type})))

(defn sig-findo' [signature wordform constant]
  (l/fresh [hypertag]
           (lexicono wordform hypertag)
           (sig-lexo signature hypertag constant)))

