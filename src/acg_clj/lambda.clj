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
  ([_ _ _ [ref v] _]
     (l/membero ref ['var 'const])      ; It would be nice to treat
                                        ; these two cases differently.
     (l/conde [(lookupo c v :i)
               (lookupo ic v t)
               (l/== lc [])]
              [(lookupo c v :l)
               (l/== lc [[v t]])]))
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
     (l/fresh [lcf lca ft at]
              (l/conde [(l/== ft ['-> at t])
                        (mergeo lcf lca lc)]
                       [(l/== ft ['=> at t])
                        (l/== lcf lc)
                        (l/== lca [])])
              (typeo c ic lcf f ft)
              (typeo c ic lca a at))))

