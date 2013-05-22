(ns acg-clj.lambda
  "Lambda calculus foundations (type inference, reduction)."
  (:require [clojure.core.logic :as l]
            [clojure.core.logic.nominal :as n]))

;; This implementation does not put hash constraints on the values of
;; the context, but it can cause an occurs check stack overflow (TODO:
;; investigate and potentially file a bug).
#_(l/defne not-in-envo [name env]
  ([_ []])
  ([_ [[other-name _] . rest-env]]
     (n/hash name other-name)
     (not-in-envo name rest-env)))

(defn not-in-envo
  "`name' does not occur inside the typing context `env'."
  [name env]
  (n/hash name env))

(defn env-lookupo
  "The typing context `env' assigns the type `t' to the variable named
  by the nom `x'."
  [env x t]
  (l/membero [x t] env))

(defn env-addo
  "The typing context `e-out' is formed by taking the typing context
  `e-in' and adding an assignment from the nom `x' to the type `t'."
  [e-in x t e-out]
  (l/all (not-in-envo x e-in)
         (l/conso [x t] e-in e-out)))

(defn encodeo
  "`term' is the lambda calculus encoding of the `string'."
  [string term]
  (n/fresh [fin]
           (l/conde [(l/== string [])
                     (l/== term ['llam (n/tie fin ['var fin])])]
                    [(l/fresh [word rest-string rest-term rest-body]
                              (l/conso word rest-string string)
                              (l/== rest-term ['llam (n/tie fin rest-body)])
                              (l/== term ['llam (n/tie fin ['app ['const word]
                                                                 rest-body])])
                              (encodeo rest-string rest-term))])))

(l/defne ^{:doc "The list `l' can be formed by merging the lists `l1'
  and `l2'. When merging two lists, any of the two heads can be the
  head of the new list."} env-mergeo [e1 e2 e]
  ([[] e2 e2])
  ([[h1 . t1] [] [h1 . t1]])
  ([[[h1-n h1-t] . t1] [h2 . t2] [[h1-n h1-t] . t]]
     (not-in-envo h1-n e2)
     (env-mergeo t1 e2 t))
  ([[h1 . t1] [[h2-n h2-t] . t2] [[h2-n h2-t] . t]]
     (not-in-envo h2-n e1)
     (env-mergeo e1 t2 t)))

(l/defne ^{:doc "The lambda term `x' (in its tagged representation) has
  type `t', given the contexts `ic' and `lc' for variables provided by
  intuitionistic and linear intuitionistic lambdas, respectively."}
  typeo [ic lc x t]
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
  "The closed lambda term `x' has type `t'."
  [x t]
  (typeo [] [] x t))


;; The parts below (small-step interpreter and capture-free
;; substitution) are heavily based on the code from Nada Amin's talk
;; on core.logic.nominal. Thanks a lot for showing me the way!

(l/defne substo
  "The term `out' can be produced by substituting free occurrences of
  the nom `a' in the term `e' with the term `new' (out == e[a/new])."
  [e a new out] ;; out == e[a/new]
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

(l/defne valo
  "`e' is a value, that is a term in beta-normal form."
  [e]
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

(l/defne stepo
  "The term `o' can be reached from the term `e' by performing one
  step of beta-reduction in a left-to-right order of reduction."
  [e o]
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

(defn stepo*
  "`o' is the beta-normal form of the term `e'."
  [e o]
  (l/conde [(valo e)
            (l/== e o)]
           [(l/fresh [i]
                     (stepo e i)
                     (stepo* i o))]))
