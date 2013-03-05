(ns acg-clj.core
  (:require [clojure.core.logic :as l]
            [clojure.core.logic.nominal :as n])
  (:use [clojure.pprint :only [pprint]])
  (:use plumbing.core))

(defn logic-debug [message]
  (fn [s]
    (println message)
    (pprint (map-keys #(.oname %) (.s s)))
    (l/succeed s)))

(l/defne mergeo [l1 l2 l]
  ([[] l2 l2])
  ([[h1 . t1] [] [h1 . t1]])
  ([[h1 . t1] [h2 . t2] [h1 . t]]
     (mergeo t1 l2 t))
  ([[h1 . t1] [h2 . t2] [h2 . t]]
     (mergeo l1 t2 t)))

(l/defne lookupo [c x tx]
  ([[[x tx] . _] x tx])
  ([[[y ty] . rc] x tx]
     (n/hash x y)
     (lookupo c x tx)))

(l/defne typeo-new [ic lc x t]
  ([ic [] c t]
     (l/== c (l/partial-map {:type t})))
  ([ic [] v t]
     (lookupo ic v t))
  ([ic [[v t]] v t])
  ([ic lc [lam binder] [arrow at bt]]
     (n/fresh [a]
              (l/fresh [b nic nlc]
                       (l/== binder (n/tie a b))
                       (l/conde [(l/== lam 'llam)
                                 (l/== arrow '->)
                                 (l/conso [a at] lc nlc)
                                 (l/== ic nic)]
                                [(l/== lam 'ilam)
                                 (l/== arrow '=>)
                                 (l/== lc nlc)
                                 (l/conso [a at] ic nic)])
                       (n/hash a ic)
                       (n/hash a lc)
                       (typeo-new nic nlc b bt))))
  ([ic c ['app f a] t]
     (l/fresh [c1 c2 ft at]
              (l/conde [(l/== ft ['-> at t])
                        (mergeo c1 c2 c)]
                       [(l/== ft ['=> at t])
                        (l/== c1 c)
                        (l/== c2 [])])
              (typeo-new ic c1 f ft)
              (typeo-new ic c2 a at))))

(l/defne typeo [const ic lc x t]
  ([const ic [] ['const c] t]
     (l/membero [c t] const))
  ([const ic [] ['ivar v] t]
     (lookupo ic v t))
  ([const ic [[v t]] ['lvar v] t])
  ([const ic lc [lam binder] [arrow at bt]]
     (n/fresh [a]
              (l/fresh [b nic nlc]
                       (l/== binder (n/tie a b))
                       (l/conde [(l/== lam 'llam)
                                 (l/== arrow '->)
                                 (l/conso [a at] lc nlc)
                                 (l/== ic nic)]
                                [(l/== lam 'ilam)
                                 (l/== arrow '=>)
                                 (l/== lc nlc)
                                 (l/conso [a at] ic nic)])
                       (n/hash a ic)
                       (n/hash a lc)
                       (typeo const nic nlc b bt))))
  ([const ic c ['app f a] t]
     (l/fresh [c1 c2 ft at]
              (l/conde [(l/== ft ['-> at t])
                        (mergeo c1 c2 c)]
                       [(l/== ft ['=> at t])
                        (l/== c1 c)
                        (l/== c2 [])])
              (typeo const ic c1 f ft)
              (typeo const ic c2 a at))))




(defn substo [e new a out]
  (l/conde
    [(l/== ['var a] e) (l/== new out)]
    [(l/fresh [y]
       (l/== ['var y] e)
       (l/== ['var y] out)
       (n/hash a y))]
    [(l/fresh [rator ratorres rand randres]
       (l/== ['app rator rand] e)
       (l/== ['app ratorres randres] out)
       (substo rator new a ratorres)
       (substo rand new a randres))]
    [(l/fresh [body bodyres]
       (l/fresh [c]
         (l/== ['lam (n/tie c body)] e)
         (l/== ['lam (n/tie c bodyres)] out)
         (n/hash c a)
         (n/hash c new)
         (substo body new a bodyres)))]))

