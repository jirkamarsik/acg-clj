(ns acg-clj.lambda
  "Lambda calculus foundations (type inference, reduction)."
  (:require [clojure.core.logic :as l]))

(l/defne ^{:doc "A relation ensuring that the list `l' can be formed
  by merging the lists `l1' and `l2'. When merging two lists, any of
  the two heads can be the head of the new list."} mergeo
  [l1 l2 l]
  ([[] l2 l2])
  ([[h1 . t1] [] [h1 . t1]])
  ([[h1 . t1] [h2 . t2] [h1 . t]]
     (mergeo t1 l2 t))
  ([[h1 . t1] [h2 . t2] [h2 . t]]
     (mergeo l1 t2 t)))

(l/defne ^{:doc "A relation ensuring that the alist `c' associates the
  value `tx' to the key `x'."} lookupo
  [c x tx]
  ([[[x tx] . _] _ _])
  ([[[y ty] . rc] _ _]
     (l/!= x y)
     (lookupo rc x tx)))

;; TODO: Should ensure consistency of `c' with `ic' and `lc'.
(l/defne ^{:doc "A relation ensuring that the lambda term `x' (in its
  tagged representation) has type `t', given the contexts `ic' and
  `lc' for variables provided by intuitionistic and linear
  intuitionistic lambdas, where `c' is an alist from variable names to the
  keywords :i and :l which disambiguates which variable refers to a
  variable in the intuitionistic or linear context."} typeo
  [c ic lc x t]
  ([_ _ [] ['const {:type t :id _}] _])
  ([_ _ _ ['var v] _]
     (l/conde [(l/== lc [])
               (lookupo ic v t)
               (lookupo c v :i)]
              [(l/== lc [[v t]])
               (lookupo c v :l)]))
  ([_ _ _ [lam [v] b] [arrow vt bt]]
     (l/fresh [nic nlc nc]
              (l/conde [(l/== lam 'llam)
                        (l/== arrow '->)
                        (l/conso [v vt] lc nlc)
                        (l/== ic nic)
                        (l/conso [v :l] c nc)]
                       [(l/== lam 'ilam)
                        (l/== arrow '=>)
                        (l/== lc nlc)
                        (l/conso [v vt] ic nic)
                        (l/conso [v :i] c nc)])
              (typeo nc nic nlc b bt)))
  ([_ _ _ ['app f a] _]
     (l/fresh [at]
              (l/conde [(l/fresh [lcf lca]
                                 (typeo c ic lcf f ['-> at t])
                                 (typeo c ic lca a at)
                                 (mergeo lcf lca lc))]
                       [(typeo c ic lc f ['=> at t])
                        (typeo c ic [] a at)]))))

(defn top-typeo
  ""
  [x t]
  (typeo [] [] [] x t))
