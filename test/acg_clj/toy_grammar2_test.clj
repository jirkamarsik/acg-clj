(ns acg-clj.toy-grammar2-test
  (:use clojure.test
        acg-clj.toy-grammar2
        acg-clj.acg
        acg-clj.testing))

(def test-wordforms ["une" "les" "dort" "mangent" "grand" "vert" "enfant"])

(deftest lexicon-tests
  (doseq [[signature lexo name] [[stx-sig stx->sim-sem-lexo 'stx->sim-sem]
                                 [stx-sig stx->string-lexo 'stx->string]]]
    (testing (str "Testing lexicon " name)
      (test-lexicon signature (lexo-extend lexo) test-wordforms))))

(deftest signature-tests
  (doseq [[signature name] [[stx-sig 'stx]]]
    (testing (str "Testing signature " name)
      (test-signature signature test-wordforms))))
