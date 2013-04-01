(ns acg-clj.lambda
  "Lambda calculus foundations (type inference, reduction)."
  (:require [clojure.core.logic :as l]
            [clojure.core.logic.nominal :as n])
  (:use acg-clj.utils))

;; This implementation does not put hash constraints on the values of
;; the context, but it can cause an occurs check stack overflow.
#_(l/defne not-in-envo [name env]
  ([_ []])
  ([_ [[other-name _] . rest-env]]
     (n/hash name other-name)
     (not-in-envo name rest-env)))

(defn not-in-envo [name env]
  (n/hash name env))

(defn env-lookupo [env x t]
  (l/membero [x t] env))

(defn env-addo [e-in x t e-out]
  (l/all #_(envo e-in)
         (env-not-ino e-in x)
         (l/conso [x t] e-in e-out)
         #_(envo e-out)))

(l/defne ^{:doc "A relation ensuring that the list `l' can be formed
  by merging the lists `l1' and `l2'. When merging two lists, any of
  the two heads can be the head of the new list."} env-mergeo
  [e1 e2 e]
  ([[] e2 e2])
  ([[h1 . t1] [] [h1 . t1]])
  ([[[h1-n h1-t] . t1] [h2 . t2] [[h1-n h1-t] . t]]
     (not-in-envo h1-n e2)
     (env-mergeo t1 e2 t))
  ([[h1 . t1] [[h2-n h2-t] . t2] [[h2-n h2-t] . t]]
     (not-in-envo h2-n e1)
     (env-mergeo e1 t2 t)))

(l/defne ^{:doc "A relation ensuring that the lambda term `x' (in its
  tagged representation) has type `t', given the contexts `ic' and
  `lc' for variables provided by intuitionistic and linear
  intuitionistic lambdas, respectively."} typeo
  [ic lc x t]
  ([_ [] ['const {:type t :id _}] _])
  ([_ _ ['var v] _]
     (l/conde [(l/== lc [])
               (env-lookupo ic v t)]
              [(l/== lc [[v t]])
               (not-in-envo v ic)]))
  ([_ _ [lam binder] [arrow vt bt]]
     (l/fresh [nic nlc b]
              (n/fresh [v]
                       (l/== binder (n/tie v b))
                       (l/conde [(l/== lam 'llam)
                                 (l/== arrow '->)
                                 (l/== ic nic)
                                 (env-addo lc v vt nlc)]
                                [(l/== lam 'ilam)
                                 (l/== arrow '=>)
                                 (l/== lc nlc)
                                 (env-addo ic v vt nic)])
                       (typeo nic nlc b bt))))
  ([_ _ ['app f a] _]
     (l/fresh [at]
              (l/conde [(l/fresh [lcf lca]
                                 (typeo ic lcf f ['-> at t])
                                 (typeo ic lca a at)
                                 (env-mergeo lcf lca lc))]
                       [(typeo ic lc f ['=> at t])
                        (typeo ic [] a at)]))))

(defn top-typeo
  ""
  [x t]
  (typeo [] [] x t))
