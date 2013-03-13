(ns acg-clj.termix
  "Functionality for working with lambda-terms, namely the conversion from
  a Lisp-style human-readable notation and a more AST-like tagged
  representation and back."
  (:use plumbing.core))

(def natural->tagged
  "The mapping from the special form names in the natural notation to
  their more verbose counterparts in the tagged representation."
  '{ll llam
    il ilam})

(def tagged->natural
  "The mapping from the special form names in the tagged representation
  of terms to their counterparts in the natural notation."
  (for-map [[natural tagged] natural->tagged]
    tagged
    natural))

(def term-type-hiero
  "The ontology of tag types in the tagged representation."
  (-> (make-hierarchy)
      (derive 'llam 'lam)
      (derive 'ilam 'lam)
      (derive 'var 'ref)
      (derive 'const 'ref)))

(defn natural-term-type
  "Determines the type (tag) of a natural term."
  [term]
  (if (sequential? term)
    (let [op (first term)]
      (get natural->tagged op 'app))
    'ref))

(defn tagged-term-type
  "Returns the tag of the given tagged term."
  [term]
  (first term))


(defmulti read-term'
  "Converts a term in its natural notation to its tagged
  representation. `env' is a map whose keys are variables in the scope
  of the term."
  (fn [env term]
    (natural-term-type term))
  :hierarchy #'term-type-hiero)

(defn read-term
  "Converts a term in its natural notation to its tagged representation."
  [term]
  (read-term' {} term))

(defmethod read-term' 'lam [env [lam [v & vs :as vars] body]]
  (if (empty? vars)
    (read-term' env body)
    [(natural->tagged lam) [v] (read-term' (assoc env v v)
                                           (list lam vs body))]))

(defmethod read-term' 'app [env term]
  (reduce (fn [f a]
            ['app f a])
          (map (partial read-term' env) term)))

(defmethod read-term' 'ref [env ref]
  (if (contains? env ref)
    ['var ref]
    ['const ref]))


(defn ^:dynamic *present-const-fn*
  "A customizable dynamic var holding a function that will be used by
  present-term to provide a human-readable value of constants."
  [c]
  c)

(defmulti present-term
  "Maps terms in their tagged representation to the more
  human-readable natural notation. Calls *present-const-fn* (identity
  by default) on the constants to determine their human-readable
  form."
  #'tagged-term-type
  :hierarchy #'term-type-hiero)

(defmethod present-term 'app [[app f a]]
  (if (= (tagged-term-type f) 'app)
    (concat (present-term f) (list (present-term a)))
    (list (present-term f) (present-term a))))

(defmethod present-term 'lam [[lam [v] body]]
  (let [natural-lam (tagged->natural lam)
        p-body (present-term body)]
    (if (= (tagged-term-type body) lam)
      (let [[_ inner-vars inner-body] p-body
            vars (vec (cons v inner-vars))]
        (list natural-lam vars inner-body))
      (list natural-lam [v] p-body))))

(defmethod present-term 'var [[var v]]
  v)

(defmethod present-term 'const [[const c]]
  (*present-const-fn* c))

(defn pt
  "An alias for present-term."
  [term]
  (present-term term))


(defn present-const-by-name
  "A function for presenting constants produced by acg-clj using their
  name/wordform."
  [c]
  (let [wordform (get-in c [:id :lex-entry :wordform])
        constant-name (get-in c [:id :constant-name])]
    (cond (not (nil? wordform)) wordform
          (not (nil? constant-name)) constant-name
          :else c)))

(defn present-const-also-by-spec
  "Expects a function that presents a constant and creates a new one
  that attaches the [:id :spec], if any."
  [present-const-fn]
  (fn [c]
    (let [spec (get-in c [:id :spec])]
      (if (not (nil? spec))
       (str (present-const-fn c) "(" spec ")")
       (present-const-fn c)))))

(defn present-const-also-by-type
  "Expects a function that already knows how to present a constant and
  produces a new presentation function that also includes type
  information."
  [present-const-fn]
  (fn [c]
    (if (and (map? c) (contains? c :type))
      [(present-const-fn c) :> (:type c)]
      (present-const-fn c))))

(defn ptn
  "A shortcut for calling pt with present-const-by-name."
  [term]
  (binding [*present-const-fn* present-const-by-name]
    (pt term)))

(defn ptnt
  "A shortcut for calling pt with present-const-by-name and
  also-by-type."
  [term]
  (binding [*present-const-fn* (-> present-const-by-name
                                   present-const-also-by-type)]
    (pt term)))

(defn ptnst
  "A shortcut for calling pt with present-const-by-name, also-by-spec
  and also-by-type."
  [term]
  (binding [*present-const-fn* (-> present-const-by-name
                                   present-const-also-by-spec
                                   present-const-also-by-type)]
    (pt term)))

(defmulti magic-quote-term-fn
  "The implementation of the magic-quote-term macro."
  #'natural-term-type
  :hierarchy #'term-type-hiero)

(defmethod magic-quote-term-fn 'lam [[lam vars body]]
  `(list '~lam '~vars
         (let ~(vec (interleave vars
                                (map (fn [v] `'~v) vars)))
           ~(magic-quote-term-fn body))))

(defmethod magic-quote-term-fn 'app [term]
  (if (= (first term) 'quote)
    `'~(second term)
   `(list ~@(map magic-quote-term-fn term))))

(defmethod magic-quote-term-fn 'ref [ref]
  ref)

(defmacro magic-quote-term
  "A utility for quoting terms written in natural notation. Open
  variables will be left to be resolved in the local scope."
  [term]
  (magic-quote-term-fn term))

(defmacro rt
  "A shortcut for read-term that use magic-quote-term on its
  argument. Any open variables in the term should resolve to terms
  written in the natural notation."
  [term]
  `(read-term (magic-quote-term ~term)))

