(ns acg-clj.utils
  "A medley of generally useful things which don't really fit anywhere
  else."
  (:require [clojure.core.logic :as l]
            [clojure.set :as set]
            [monads.core :refer :all]
            [monads.util :refer [sequence-m]])
  (:use plumbing.core))

(defn mapuni
  "Just like mapcat, but does a set/union instead of concat."
  [f & colls]
  (apply set/union (apply map f colls)))


(defn mapr
  "Given `f', a binary goal encoding a function, returns a binary
  relation that encodes the function (map f %)."
  [f]
  (fn lifted-f [in out]
    (l/matche [in out]
              ([[] []])
              ([[in-h . in-t] [out-h . out-t]]
                 (f in-h out-h)
                 (lifted-f in-t out-t)))))

(l/defne ^{:doc "The alist `al' associates the key `k' with the value
  `v'."} assoco
  [al k v]
  ([[[k v] . _] _ _])
  ([[[k' v'] . ral] _ _]
     (l/!= k k')
     (assoco ral k v)))

(l/defne ^{:doc "`key' is the key in the key-value pair `key-value'."}
  keyo
  [key-value key]
  ([[key _] _]))

(defn keyso
  "`keys' is the list of keys of the alist `alist'."
  [alist keys]
  ((mapr keyo) alist keys))


(defn retrievec
  "The `hypertag' is compatible with the `pattern'. For the pattern to
  be compatible with the hypertag, the hypertag should contain all the
  key paths of the pattern and the values in the leaf nodes of the
  pattern must be members of the lists stored under the same key paths
  in the hypertag.

  E.g. (retrievec {:head {:cat [\"v\"]
                          :pers [\"1\" \"3\"]}
                   :subj {:cat [\"n\"]}}
                  {:head {:cat \"v\"
                          :pers \"1\"}})"
  [hypertag pattern]
  (let [lvar-value-pairs (atom {})
        lvarize (fn lvarize [pat]
                  (if (map? pat)
                    (map-vals lvarize pat)
                    (let [lvar (l/lvar)]
                      (swap! lvar-value-pairs assoc lvar pat)
                      lvar)))
        lvar-pattern (lvarize pattern)]
    (l/all (l/featurec hypertag lvar-pattern)
           (l/everyg (fn [[lvar val]]
                       (l/membero val lvar))
                     @lvar-value-pairs))))


(defn org
  "Conde as a function. Takes any number of goals and returns a goal
  which is their disjunction."
  ([]
     l/fail)
  ([goal & goals]
     (l/conde [goal]
              [(apply org goals)])))

(defn andg
  "All as a function. Takes any number of goals and returns a goal
  which is their conjunction."
  ([]
     l/succeed)
  ([goal & goals]
     (l/all goal
            (apply andg goals))))

(defn compg
  "Like comp, but composes binary relations that encode functions."
  ([]
     (fn [x y]
       (l/== x y)))
  ([goal & goals]
     (fn [x z]
       (l/fresh [y]
                ((apply compg goals) x y)
                (goal y z)))))


(defn accessor-name-for-key
  "Returns the name of the accessor relation for accessing the field
  stored under the keyword `key'.

  E.g. :type -> has-typeo"
  [key]
  (symbol (str "has-" (name key) "o")))

(defn accessor-def
  "Constructs the definition of an accessor relation. `key-path' is a
  stack of keywords describing the path taken from the root of the
  object model to the field being retrieved. `all-keys' is a
  collection of all the keys defined in the object found at the
  `key-path' (including the top of `key-path', but also possibly other
  keys).

  E.g. (accessor-def [:id :spec] [:spec :lex-entry]) ->
       (defn has-speco
         \"Accesses [:id :spec] in a constant.\"
         [constant spec]
         (l/fresh [id lex-entry]
                  (has-ido constant id)
                  (l/== id {:spec spec
                            :lex-entry lex-entry})))"
  [key-path all-keys]
  (let [symbolize (fn [keyword] (symbol (name keyword)))
        key (peek key-path)
        ancestors (pop key-path)
        parent (peek ancestors)]
    `(defn ~(accessor-name-for-key key)
       ~(str "Accesses " key-path " in a constant.")
       [~'constant ~(symbolize key)]
       ~(if (seq ancestors)
          `(l/fresh ~(into [(symbolize parent)]
                           (map symbolize (remove #{key} all-keys)))
                    (~(accessor-name-for-key parent)
                     ~'constant ~(symbolize parent))
                    (l/== ~(symbolize parent)
                          ~(for-map [k all-keys] k (symbolize k))))
          `(l/fresh ~(vec (map symbolize (remove #{key} all-keys)))
                    (l/== ~'constant
                          ~(for-map [k all-keys] k (symbolize k))))))))

(defn accessor-defs
  "Constructs a sequence of accessor relation definitions. `schema'
  describes the shape of the object model, `key-path' is a stack of
  field names on the path from the root of the top of the object model
  to the level of `schema'. If you are calling this function from
  outside, `key-path' should probably be [].

  For more information on the `schema', see `defaccessors'."
  [key-path schema]
  (cond (sequential? schema)
        ,(mapcat (partial accessor-defs key-path) schema)
        (map? schema)
        ,(apply concat (for [[key subschema] schema]
                         (cons (accessor-def (conj key-path key) (keys schema))
                               (accessor-defs (conj key-path key) subschema))))))

(defmacro defaccessors
  "Defines accessor relations for retrieving values in a nested object
  model.

  E.g. (defaccessors {:type _
                      :id [{:lex-entry {:wordform _
                                        :hypertag _}
                            :spec _}
                           {:constant-name _}]})

  Maps represent nested objects, vectors represent
  alternatives (union), anything else is ignored.

  This will define binary relations like has-ido, has-speco and
  has-constant-nameo, which state that some object `%1' that
  corresponds to this schema has the value `%2' in the field mentioned
  by the relation's name."
  [schema]
  `(do ~@(accessor-defs [] schema)))

(defn map-m
  "Applies a function over collections, just like `map'. The function
  `f' should return monadic computations, which will all be bound
  sequentially to produce a computation which yields the sequence of
  values (mapM :: (a -> M b) -> [a] -> M [b] in Haskell)"
  [f & colls]
  (sequence-m (apply map f colls)))

(defn map-vals-m
  "`map-vals-m' is to `map-vals' what `map-m' is to `map'."
  [f m]
  (>>= (map-m (fn [[key value]]
                (>>= (f value)
                     (fn [value'] (return [key value']))))
              m)
       (fn [kvps]
         (return (into {} kvps)))))
