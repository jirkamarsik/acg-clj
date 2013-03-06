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
  ([[[x tx] . _] _ _])
  ([[[y ty] . rc] _ _]
     (l/!= x y)
     (lookupo rc x tx)))

(l/defne typeo [c ic lc x t]
  ([_ _ _ ['var v] _]
     (l/conde [(lookupo c v :l)
               (l/== lc [[v t]])]
              [(lookupo c v :i)
               (lookupo ic v t)]))
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



#_(defn substo [e new a out]
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

