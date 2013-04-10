(ns acg-clj.examples.toy-grammar-test
  (:use clojure.test
        acg-clj.examples.toy-grammar
        acg-clj.acg
        acg-clj.testing))

(def test-wordforms ["une" "les" "dort" "mangent" "grand" "vert" "enfant"])

(deftest lexicon-tests
  (doseq [[signature lexo name] [[a-stx-sig a-stx->sim-sem-lexo 'a-stx->sim-sem]
                                 [a-stx-sig a-stx->ua-stx-lexo 'a-stx->ua-stx]
                                 [ua-stx-sig ua-stx->string-lexo 'ua-stx->string]
                                 [string-sig string->l-string-lexo 'string->l-string]]]
    (testing (str "Testing lexicon " name)
      (test-lexicon signature (extend-lexor lexo) test-wordforms))))

(deftest signature-tests
  (doseq [[signature name] [[a-stx-sig 'a-stx]
                            [sim-sem-sig 'sim-sem]
                            [ua-stx-sig 'ua-stx]
                            [string-sig 'string]
                            [l-string-sig 'l-string]]]
    (testing (str "Testing signature " name)
      (test-signature signature test-wordforms))))
