(ns acg-clj.lexicon
  (:require [clojure.java.io :as io]
            [clojure.string :as string]
            [clojure.core.logic :as l]
            [clojure.core.logic.nominal :as n])
  (:use plumbing.core))

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

(defonce lexicon
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
                         :const)))

(defmethod read-term :lam [[lam [v & vs :as vars] body] env]
  (if (empty? vars)
    (read-term body env)
    (let [new-nom (n/nom (l/lvar v))
          new-env (assoc env v new-nom)
          emitted-lam ('{ll llam, il ilam} lam)]
      [emitted-lam (n/tie new-nom 
                          (read-term (list lam vs body) new-env))])))

(defmethod read-term :app [term env]
  (reduce (fn [f a]
            ['app f a])
          (map #(read-term % env) term)))

(defmethod read-term :const [term env]
  (let [maybe-resolved (and (symbol? term) (resolve term))]
    (cond (contains? env term) (get env term)
          (var? maybe-resolved) (deref maybe-resolved)
          (class? maybe-resolved) maybe-resolved
          :else term)))

(defmacro rt [term]
  (let [local-env (into {} (for [s (keys &env)]
                             [(list 'quote s) s]))]
    `(read-term '~term ~local-env)))

(defn term-type [term]
  (when (sequential? term)
    (first term)))

(def print-term-hierarchy (-> (make-hierarchy)
                              (derive 'llam 'lam)
                              (derive 'ilam 'lam)))

(defmulti print-term (some-fn term-type class)
  :hierarchy #'print-term-hierarchy)

(defmethod print-term :default [term]
  (if (and (map? term) (contains? term :print-as))
    (get term :print-as)
    term))

(defmethod print-term clojure.core.logic.nominal.Nom [nom]
  (.oname (.lvar nom)))

(defmethod print-term 'app [[app f a]]
  (if (= (term-type f) 'app)
    (concat (print-term f) (list (print-term a)))
    (list (print-term f) (print-term a))))

(defmethod print-term 'lam [[lam tie]]
  (let [written-lam ('{llam ll, ilam il} lam)
        bound-nom (.binding-nom tie)
        bound-sym (if (symbol? bound-nom)
                    bound-nom                    ; reified terms
                    (.oname (.lvar bound-nom)))  ; non-reified terms
        body (print-term (.body tie))]
    (if (and (sequential? body) (= (first body) written-lam))
      (let [[_ inner-bound-syms body] body
            bound-syms (vec (cons bound-sym inner-bound-syms))]
        (list written-lam bound-syms body))
      (list written-lam [bound-sym] body))))

(def pt print-term)


(defn apply-lex [lex-name term]
    (cond (and (map? term) (contains? term lex-name)) (get term lex-name)
          (vector? term) (vec (map (partial apply-lex lex-name) term))
          (n/tie? term)
          ,(clojure.core.logic.nominal.Tie. (.binding-nom term)
                                            (apply-lex lex-name (.body term))
                                            (._meta term))
          :else term))


(defn hypertago [hypertag]
  (l/fresh [wordform]
           (lexicono wordform hypertag)))


(defn print-as-wordform [hypertag print-as]
  (lexicono print-as hypertag))




(def lambda-string-principal-type '[-> Sigma Sigma])

(defn lambda-string-typeo [hypertag type]
  (l/== type '[-> Sigma Sigma]))

(def lambda-string-printo print-as-wordform)

(defn lambda-string-sigo [hypertag constant]
  (l/fresh [type print-as]
           (hypertago hypertag)
           (lambda-string-typeo hypertag type)
           (lambda-string-printo hypertag print-as)
           (l/== constant {:type type
                           :print-as print-as})))



(def string-principal-type 'Str)

(def str-++ {:type '[-> Str [-> Str Str]]
             :print-as '++
             :string->lambda-string (rt (ll [x y]
                                       (ll [t]
                                           (x (y t)))))})

(defn string-consto [constant]
  (l/membero constant [str-++]))

(defn string-typeo [hypertag type]
  (l/== type 'Str))

(def string-printo print-as-wordform)

(defn string->lambda-string-lexo [hypertag string-constant lambda-string-term]
  (l/fresh [lambda-string-constant]
           (lambda-string-sigo hypertag lambda-string-term)))

(def string->lambda-string (partial apply-lex :string->lambda-string))

(defn string-sigo [hypertag constant]
  (l/conde [(l/fresh [type print-as string->lambda-string]
                     (hypertago hypertag)
                     (string-typeo hypertag type)
                     (string-printo hypertag print-as)
                     (string->lambda-string-lexo hypertag constant string->lambda-string)
                     (l/== constant {:type type
                                     :print-as print-as
                                     :string->lambda-string string->lambda-string}))]
           [(l/== hypertag nil)
            (string-consto constant)]))


(def unamb-syntax-principal-type 'S)

(defn unamb-syntax-typeo [hypertag type]
  (l/conde [(retrievec hypertag {:head {:cat "n"}})
            (l/== type 'N)]
           [(retrievec hypertag {:head {:cat "adj"}})
            (l/== type '[-> N N])]
           [(retrievec hypertag {:head {:cat "det"}})
            (l/== type '[-> N NP])]
           [(retrievec hypertag {:head {:cat "v"
                                        :trans "false"}})
            (l/== type '[-> NP S])]))

(def unamb-syntax-printo print-as-wordform)

(defn unamb-syntax->string-lexo [hypertag unamb-syntax-constant string-term]
  (l/fresh [string-constant]
           (string-sigo hypertag string-constant)
           (let [prefix (rt (ll [x] (str-++ string-constant x)))
                 suffix (rt (ll [x] (str-++ x string-constant)))]
             (l/conde [(retrievec hypertag {:head {:cat "n"}})
                       (l/== string-term string-constant)]
                      [(retrievec hypertag {:head {:cat "adj"
                                                   :order "right"}})
                       (l/== string-term suffix)]
                      [(retrievec hypertag {:head {:cat "adj"
                                                   :order "left"}})
                       (l/== string-term prefix)]
                      [(retrievec hypertag {:head {:cat "det"}})
                       (l/== string-term prefix)]
                      [(retrievec hypertag {:head {:cat "v"
                                                   :trans "false"}})
                       (l/== string-term suffix)]))))

(def unamb-syntax->string (partial apply-lex :unamb-syntax->string))

(defn unamb-syntax-sigo [hypertag constant]
  (l/fresh [type print-as unamb-syntax->string]
           (hypertago hypertag)
           (unamb-syntax-typeo hypertag type)
           (unamb-syntax-printo hypertag print-as)
           (unamb-syntax->string-lexo hypertag constant unamb-syntax->string)
           (l/== constant {:type type
                           :unamb-syntax->string unamb-syntax->string
                           :print-as print-as})))


(def simple-semantics-principal-type 'T)

(def sem-and? {:type '[-> T [-> T T]]
               :print-as 'and?})
(def sem-or? {:type '[-> T [-> T T]]
              :print-as 'or?})
(def sem-not? {:type '[-> T T]
               :print-as 'not?})
(def sem-imp? {:type '[-> T [-> T T]]
               :print-as 'imp?})
(def sem-top {:type 'T
              :print-as true})
(def sem-bot {:type 'T
              :print-as false})
(def sem-forall? {:type '[-> [=> E T] T]
                  :print-as 'forall?})
(def sem-exists? {:type '[-> [=> E T] T]
                  :print-as 'exists?})

(defn simple-semantics-consto [constant]
  (l/membero constant [sem-and? sem-or? sem-not? sem-imp?
                       sem-top sem-bot sem-forall? sem-exists?]))

(defn simple-semantics-typeo [hypertag type]
  (l/conde [(retrievec hypertag {:head {:cat "n"}})
            (l/== type '[-> E T])]
           [(retrievec hypertag {:head {:cat "adj"}})
            (l/== type '[-> E T])]
           [(retrievec hypertag {:head {:cat "v"
                                        :trans "false"}})
            (l/== type '[-> E T])]))

(def simple-semantics-printo print-as-wordform)

(defn simple-semantics-sigo [hypertag constant]
  (l/conde [(l/fresh [type print-as]
                     (hypertago hypertag)
                     (simple-semantics-typeo hypertag type)
                     (simple-semantics-printo hypertag print-as)
                     (l/== constant {:type type
                                     :print-as print-as}))]
           [(l/== hypertag nil)
            (simple-semantics-consto constant)]))



(defn amb-syntax-typeo [hypertag type]
  (l/conde [(retrievec hypertag {:head {:cat "n"}})
            (l/== type 'N)]
           [(retrievec hypertag {:head {:cat "adj"}})
            (l/== type '[-> N N])]
           [(retrievec hypertag {:head {:cat "v"
                                        :trans "false"}})
            (l/== type '[-> NP S])]
           [(retrievec hypertag {:head {:cat "det"}})
            (l/== type '[-> N NP])]))

(def amb-syntax-printo print-as-wordform)

(defn amb-syntax->unamb-syntax-lexo [hypertag amb-syntax-constant unamb-syntax-term]
  (l/fresh [unamb-syntax-constant]
           (unamb-syntax-sigo hypertag unamb-syntax-constant)
           (l/conde [(retrievec hypertag {:head {:cat "n"}})
                     (l/== unamb-syntax-term unamb-syntax-constant)]
                    [(retrievec hypertag {:head {:cat "adj"}})
                     (l/== unamb-syntax-term unamb-syntax-constant)]
                    [(retrievec hypertag {:head {:cat "v"
                                                 :trans "false"}})
                     (l/== unamb-syntax-term unamb-syntax-constant)]
                    [(retrievec hypertag {:head {:cat "det"}})
                     (l/== unamb-syntax-term unamb-syntax-constant)])))

(def amb-syntax->unamb-syntax (partial apply-lex :amb-syntax->unamb-syntax))

(defn amb-syntax->simple-semantics-lexo [hypertag amb-syntax-constant simple-semantics-term]
  (l/fresh [simple-semantics-constant]
           (l/conde [(simple-semantics-sigo hypertag simple-semantics-constant)
                     (l/conde [(retrievec hypertag {:head {:cat "n"}})
                               (l/== simple-semantics-term simple-semantics-constant)]
                              [(retrievec hypertag {:head {:cat "adj"}})
                               (l/== simple-semantics-term (rt (ll [n] (il [x] (sem-and? (simple-semantics-constant x) (n x))))))]
                              [(retrievec hypertag {:head {:cat "v"
                                                           :trans "false"}})
                               (l/== simple-semantics-term (rt (ll [S] (S (ll [x] (simple-semantics-constant x))))))])]
                    [(retrievec hypertag {:head {:cat "det"
                                                 :det_type "indef"}})
                     (l/== simple-semantics-term (rt (ll [p q] (sem-exists? (il [x] (sem-and? (p x) (q x)))))))])))

(def amb-syntax->simple-semantics (partial apply-lex :amb-syntax->simple-semantics))

(defn amb-syntax-sigo [hypertag constant]
  (l/fresh [type print-as amb-syntax->unamb-syntax amb-syntax->simple-semantics]
           (hypertago hypertag)
           (amb-syntax-typeo hypertag type)
           (amb-syntax-printo hypertag print-as)
           (amb-syntax->unamb-syntax-lexo hypertag constant amb-syntax->unamb-syntax)
           (amb-syntax->simple-semantics-lexo hypertag constant amb-syntax->simple-semantics)
           (l/== constant {:type type
                           :print-as print-as
                           :amb-syntax->unamb-syntax amb-syntax->unamb-syntax
                           :amb-syntax->simple-semantics amb-syntax->simple-semantics})))



(comment 
  (binding [n/*reify-noms* false]
    (def un-tag (nth (lexicon "un") 1))
    (def homme-tag (first (lexicon "homme")))
    (def vieux-tag (nth (lexicon "vieux") 1))
    (def vive-tag (nth (lexicon "vive") 2))
    (def un-abstract (first (l/run 1 [q] (amb-syntax-grammar un-tag q))))
    (def homme-abstract (first (l/run 1 [q] (amb-syntax-grammar homme-tag q))))
    (def vieux-abstract (first (l/run 1 [q] (amb-syntax-grammar vieux-tag q))))
    (def vive-abstract (first (l/run 1 [q] (amb-syntax-grammar vive-tag q))))
    (def sentence-abstract ['app vive-abstract ['app un-abstract ['app vieux-abstract homme-abstract]]])))
