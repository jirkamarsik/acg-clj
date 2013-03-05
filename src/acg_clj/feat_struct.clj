(ns acg-clj.feat-struct
  (:require [clojure.core.logic :as l]
            [clojure.set :as s])
  (:use plumbing.core))

(defprotocol FeatStruct
  (closed? [x]))

(defn feat-struct? [x]
  (instance? acg_clj.feat_struct.FeatStruct x))

(defrecord ClosedFS []
  FeatStruct
  (closed? [x]
    true))

(defrecord OpenFS []
  FeatStruct
  (closed? [x]
    false))

(defn fs [m]
  (if (map? m)
    (map->OpenFS (map-vals fs m))
    m))

(defn close [fs]
  (map->ClosedFS fs))

(defn cfs [m]
  (close (fs m)))

(defn unify-with-fs* [u v s]
  (let [optional? (fn [key]
                    (.endsWith (name key) "?"))
        fname (fn [key]
                (if (optional? key)
                  (let [key-name (name key)]
                    (keyword (.substring key-name 0 (dec (count key-name)))))
                  key))
        fs-find (fn [fs key]
                  (or (find fs key) (find fs (keyword (str (name key) "?")))))
        fs-get (comp val fs-find)
        too-much? (fn [fs1 fs2]
                    (and (closed? fs2)
                         (some #(not (fs-find fs2 %))
                               (remove optional? (keys fs1)))))
        missing? (fn [fs1 fs2]
                   (and (closed? fs2)
                        (some #(not (fs-find fs1 %))
                              (remove optional? (keys fs2)))))]
    (when-not (or (too-much? u v) (too-much? v u) (missing? u v) (missing? v u))
      (let [common-keys (apply s/intersection (map (fn [ks]
                                                     (set (map fname ks)))
                                                   [(keys u) (keys v)]))]
        (loop [ks common-keys s s]
          (if (seq ks)
            (let [k (first ks)]
             (when-let [s (l/unify s (fs-get u k) (fs-get v k))]
               (recur (next ks) s)))
            s))))))

(extend-type acg_clj.feat_struct.FeatStruct
  l/IUnifyTerms
  (unify-terms [u v s]
    (when (and (feat-struct? u) (feat-struct? v) (map? u) (map? v))
      (unify-with-fs* u v s)))

  ;; Without this, we cannot do (l/run 1 [q]
  ;;                                   (l/== q (fs {:a {:b 3}}))
  l/IUninitialized
  (-uninitialized [_] (OpenFS.)))

(defn unify-fso [fs1 fs2 out-fs]
  )


(defrecord HyperTag [head]
  FeatStruct
  (closed? [x]
    false))

(defn ht [m]
  (map->HyperTag m))
