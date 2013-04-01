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


;; The parts below are based on the work of Nada Amin.

(l/defne substo [e a new out] ;; out == e[a/new]
  ([['const c] _ _ ['const c]])
  ([['var a] _ _ new])
  ([['var b] _ _ e]
     (n/hash a b))
  ([['app fn arg] _ _ ['app fn' arg']]
     (substo fn a new fn')
     (substo arg a new arg'))
  ([[lam binder] _ _ [lam binder']]
     (l/fresh [body body']
              (n/fresh [var]
                       (l/membero lam '[llam ilam])
                       (l/== binder (n/tie var body))
                       (l/== binder' (n/tie var body'))
                       (n/hash var a)
                       (n/hash var new)
                       (substo body a new body')))))

(l/defne valo [e]
  ([['const _]])
  ([['var _]])
  ([['app fn arg]]
     (valo fn)
     (valo arg)
     (l/fresh [fn-tag]
              (l/firsto fn fn-tag)
              (l/!= fn-tag 'llam)
              (l/!= fn-tag 'ilam)))
  ([[lam binder]]
     (l/fresh [body]
              (n/fresh [var]
                       (l/== binder (n/tie var body))
                       (valo body)))))

(l/defne stepo [e o]
  ([['app fn arg] ['app fn' arg]]
     (stepo fn fn'))
  ([['app fn arg] ['app fn arg']]
     (valo fn)
     (stepo arg arg'))
  ([['app fn arg] _]
     (valo fn)
     (valo arg)
     (l/fresh [lam fn-body]
              (n/fresh [fn-var]
                       (l/== fn [lam (n/tie fn-var fn-body)])
                       (l/membero lam '[llam ilam])
                       (substo fn-body fn-var arg o))))
  ([[lam binder] [lam binder']]
     (l/membero lam '[llam ilam])
     (l/fresh [body body']
              (n/fresh [var]
                       (l/== binder (n/tie var body)) 
                       (l/== binder' (n/tie var body'))
                       (stepo body body')))))

(defn stepo* [e o]
  (l/conde [(valo e)
            (l/== e o)]
           [(l/fresh [i]
                     (stepo e i)
                     (stepo* i o))]))
