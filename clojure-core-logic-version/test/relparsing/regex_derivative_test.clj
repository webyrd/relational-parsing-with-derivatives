(ns relparsing.regex_derivative_test
  (:use [relparsing.regex_derivative] :reload)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l])
  (:use [clojure.test]))

;; NOTE(namin): Pruning of identical constraints. This should really be in core.logic.
(defn normalize-constraints [results]
  (map
    (fn [r]
      (if (= ':- (second r))
        (into [(first r) (second r)] (into #{} (rest (rest r))))
        r))
    results))

(deftest test-basics
  (is (= (run* [q] (repo regex-NULL q))
        [regex-BLANK]))
  (is (= (run* [q] (repo regex-BLANK q))
        [regex-BLANK]))
  (is (= (run* [q] (repo 'foo q))
        '((rep foo))))
  (is (= (run* [q] (alto regex-NULL 'foo q))
        '(foo)))
  (is (= (run* [q] (seqo regex-NULL 'foo q))
        [regex-NULL]))
  (is (= (run* [q] (seqo 'foo regex-NULL q))
        [regex-NULL]))
  (is (= (run* [q] (seqo regex-BLANK 'foo q))
        '(foo)))
  (is (= (run* [q] (seqo 'foo regex-BLANK q))
        '(foo)))
  (is (= (run* [q] (seqo 'foo 'bar q))
        '((seq foo bar)))))

(deftest test-delato
  (is (= (normalize-constraints
           (run 12 [q]
             (fresh [re out]
               (deltao re out)
               (== [re out] q))))
        '([true true]
          [false false]
          ([_0 false] :- (sym _0))
          [(rep _0) true]
          [(seq true true) true]
          [(alt true true) (alt true true)]
          [(seq true false) false]
          [(alt true false) true]
          ([(seq true _0) false] :- (sym _0))
          ([(alt true _0) true] :- (sym _0))
          [(seq false true) false]
          [(alt false true) true]))))

(deftest test-regex-derivativeo
  (is (= (normalize-constraints
           (run 5 [q]
             (fresh [re c out]
               (regex-derivativeo re c out)
               (== [re c out] q))))
        '(([true _0 false] :- (sym _0))
          ([false _0 false] :- (sym _0))
          ([_0 _0 true] :- (sym _0))
          ([_0 _1 false] :- (sym _0) (sym _1) (!= (_1 _0)))
          ([(rep true) _0 false] :- (sym _0))))))

(deftest test-regex-matcho
  (is (= (run* [q] (regex-matcho
                     '(seq foo (rep bar))
                     '(foo bar bar bar)
                     regex-BLANK))
        '(_0)))
  (is (= (run* [q] (regex-matcho
                     '(seq foo (rep bar))
                     '(foo bar baz bar bar)
                     regex-NULL))
        '(_0)))
  (is (= (run* [q] (regex-matcho
                     '(seq foo (rep (alt bar baz)))
                     '(foo bar baz bar bar)
                     regex-BLANK))
        '(_0))))

(deftest test-matcho-backwards-match
  (is (= (run 6 [q] (regex-matcho
                      '(seq foo (rep bar))
                      q
                      regex-BLANK))
        '((foo)
          (foo bar)
          (foo bar bar)
          (foo bar bar bar)
          (foo bar bar bar bar)
          (foo bar bar bar bar bar)))))

(deftest test-matcho-backwards-no-match
  (let [result
        '(()
          (bar)
          [(foo _0) :- (!= (_0 bar)) (sym _0)]
          [(bar _0) :- (sym _0)]
          [(_0) :- (!= (_0 foo)) (!= (_0 bar)) (sym _0)]
          [(foo _0 _1) :- (!= (_0 bar)) (sym _0) (sym _1)]
          [(bar _0 _1) :- (sym _0) (sym _1)]
          [(_0 _1) :- (!= (_0 foo)) (!= (_0 bar)) (sym _0) (sym _1)]
          [(foo _0 _1 _2) :- (!= (_0 bar)) (sym _0) (sym _2) (sym _1)]
          [(bar _0 _1 _2) :- (sym _0) (sym _2) (sym _1)]
          [(_0 _1 _2) :- (!= (_0 foo)) (!= (_0 bar)) (sym _0) (sym _2) (sym _1)]
          [(foo bar _0) :- (!= (_0 bar)) (sym _0)]
          [(foo _0 _1 _2 _3) :- (sym _3) (!= (_0 bar)) (sym _0) (sym _2) (sym _1)]
          [(bar _0 _1 _2 _3) :- (sym _3) (sym _0) (sym _2) (sym _1)]
          [(_0 _1 _2 _3) :- (sym _3) (!= (_0 foo)) (!= (_0 bar)) (sym _0) (sym _2) (sym _1)])]
    (is (= (normalize-constraints
             (run 15 [q] (regex-matcho
                           '(seq foo (rep bar))
                           q
                           regex-NULL)))
          result))
    (is (= (normalize-constraints
             (run 15 [q] (fresh [out]
                           (!= regex-BLANK out)
                           (regex-matcho
                             '(seq foo (rep bar))
                             q
                             out))))
          result))))

(deftest test-regex-matcho-backwards-patterns
  (is (= (run 3 [q] (regex-matcho
                      q
                      '(foo bar bar bar)
                      regex-BLANK))
        '((rep (alt foo bar))
          (rep (alt bar foo))
          (seq foo (rep bar))))))

(deftest test-regex-matcho-literal-matches
  (is (= (run 1 [q]
           (== '(seq foo (seq bar bar)) q)
           (regex-matcho
             q
             '(foo bar bar)
             regex-BLANK))
        '((seq foo (seq bar bar)))))
  (is (= (run 1 [q]
           (regex-matcho
             q
             '(foo bar bar)
             regex-BLANK)
           (== '(seq foo (seq bar bar)) q))
        '((seq foo (seq bar bar)))))
  (is (= (run 1 [q]
           (== '(seq foo (seq bar (seq bar bar))) q)
           (regex-matcho
             q
             '(foo bar bar bar)
             regex-BLANK))
        '((seq foo (seq bar (seq bar bar))))))
  (comment
    ;; Like in the scheme version, this one doesn't return.
    (is (= (run 1 [q]
             (regex-matcho
               q
               '(foo bar bar bar)
               regex-BLANK)
             (== '(seq foo (seq bar (seq bar bar))) q))
          '((seq foo (seq bar (seq bar bar))))))))

(deftest test-regex-matcho-patterns-matching-data
  (is (= (normalize-constraints
           (run 30 [q]
             (fresh [regex data]
               (regex-matcho regex data regex-BLANK)
               (== [regex data] q))))
        '([true ()]
          [(rep _0) ()]
          [(seq true true) ()]
          [(alt true false) ()]
          [[(alt true _0) ()] :- (sym _0)]
          [(alt false true) ()]
          [(seq true (rep _0)) ()]
          [[(alt _0 true) ()] :- (sym _0)]
          [[_0 (_0)] :- (sym _0)]
          [(alt false (rep _0)) ()]
          [(seq true (seq true true)) ()]
          [(seq (rep _0) true) ()]
          [(alt true (seq true false)) ()]
          [(seq true (alt true false)) ()]
          [[(alt _0 (rep _1)) ()] :- (sym _0)]
          [[(alt true (seq true _0)) ()] :- (sym _0)]
          [[(seq true (alt true _0)) ()] :- (sym _0)]
          [(alt (rep _0) false) ()]
          [(alt false (seq true true)) ()]
          [(seq true (alt false true)) ()]
          [(alt true (seq false true)) ()]
          [[(alt (rep _0) _1) ()] :- (sym _1)]
          [(alt true (seq false false)) ()]
          [(alt true (alt false false)) ()]
          [(seq true (seq true (rep _0))) ()]
          [(alt false (alt true false)) ()]
          [(seq (rep _0) (rep _1)) ()]
          [[(alt true (seq false _0)) ()] :- (sym _0)]
          [[(alt true (alt false _0)) ()] :- (sym _0)]
          [[(alt false (alt true _0)) ()] :- (sym _0)]))))

(deftest test-regex-matcho-patterns-not-matching-data
  (is (= (normalize-constraints
           (run 30 [q]
             (fresh [regex data]
               (regex-matcho regex data regex-NULL)
               (== [regex data] q))))
        '([false ()]
          [[_0 ()] :- (sym _0)]
          [[true (_0)] :- (sym _0)]
          [(alt true true) ()]
          [(seq true false) ()]
          [[(seq true _0) ()] :- (sym _0)]
          [[false (_0)] :- (sym _0)]
          [(seq false true) ()]
          [[true (_0 _1)] :- (sym _0) (sym _1)]
          [(alt false false) ()]
          [(seq false false) ()]
          [(alt true (rep _0)) ()]
          [[(alt false _0) ()] :- (sym _0)]
          [[(seq false _0) ()] :- (sym _0)]
          [[(seq _0 true) ()] :- (sym _0)]
          [[true (_0 _1 _2)] :- (sym _0) (sym _2) (sym _1)]
          [[(alt _0 false) ()] :- (sym _0)]
          [[false (_0 _1)] :- (sym _0) (sym _1)]
          [[(seq _0 false) ()] :- (sym _0)]
          [(seq false (rep _0)) ()]
          [[true (_0 _1 _2 _3)] :- (sym _3) (sym _0) (sym _2) (sym _1)]
          [[(alt _0 _1) ()] :- (sym _0) (sym _1)]
          [[(seq _0 _1) ()] :- (sym _0) (sym _1)]
          [(alt true (seq true true)) ()]
          [[true (_0 _1 _2 _3 _4)] :- (sym _3) (sym _4) (sym _0) (sym _2) (sym _1)]
          [(alt true (alt true true)) ()]
          [(seq true (alt true true)) ()]
          [[false (_0 _1 _2)] :- (sym _0) (sym _2) (sym _1)]
          [[_0 (_1)] :- (sym _0) (sym _1) (!= (_1 _0))]
          [[true (_0 _1 _2 _3 _4 _5)] :- (sym _5) (sym _3) (sym _4) (sym _0) (sym _2) (sym _1)]))))

(deftest test-regex-matcho-patterns-matching-non-empty-data
  ;; NOTE(namin): this is relatively fast compared to the Scheme version.
  (is (= (normalize-constraints
           (run 3 [q]
             (fresh [regex data]
               (!= () data)
               (regex-matcho regex data regex-BLANK)
               (== [regex data] q))))
        '(([_0 (_0)] :- (sym _0))
          [[(rep _0) (_0)] :- (sym _0) (!= (_0 true)) (!= (_0 false))]
          [[(rep _0) (_0 _0)] :- (sym _0) (!= (_0 true)) (!= (_0 false))]))))

(deftest test-regex-matcho-patterns-not-matching-non-empty-data
  (is (= (run 15 [q]
           (fresh [regex data]
             (!= () data)
             (regex-matcho regex data regex-NULL)
             (== [regex data] q)))
        '(([true (_0)] :- (sym _0))
          ([false (_0)] :- (sym _0))
          ([true (_0 _1)] :- (sym _1) (sym _0))
          ([true (_0 _1 _2)] :- (sym _2) (sym _1) (sym _0))
          ([false (_0 _1)] :- (sym _1) (sym _0))
          ([true (_0 _1 _2 _3)] :- (sym _3) (sym _2) (sym _1) (sym _0))
          ([true (_0 _1 _2 _3 _4)] :- (sym _4) (sym _3) (sym _2) (sym _1) (sym _0))
          ([false (_0 _1 _2)] :- (sym _2) (sym _1) (sym _0))
          ([_0 (_1)] :- (!= (_1 _0)) (sym _0) (sym _1))
          ([true (_0 _1 _2 _3 _4 _5)] :- (sym _5) (sym _4) (sym _3) (sym _2) (sym _1) (sym _0))
          ([_0 (_0 _1)] :- (sym _1) (sym _0) (sym _0))
          ([true (_0 _1 _2 _3 _4 _5 _6)] :- (sym _6) (sym _5) (sym _4) (sym _3) (sym _2) (sym _1) (sym _0))
          ([false (_0 _1 _2 _3)] :- (sym _3) (sym _2) (sym _1) (sym _0))
          ([true (_0 _1 _2 _3 _4 _5 _6 _7)] :- (sym _7) (sym _6) (sym _5) (sym _4) (sym _3) (sym _2) (sym _1) (sym _0))
          ([true (_0 _1 _2 _3 _4 _5 _6 _7 _8)] :- (sym _0) (sym _1) (sym _2) (sym _3) (sym _4) (sym _5) (sym _6) (sym _7) (sym _8))))))

(deftest test-regex-matcho-rep-weirdness
  (is (= (run 3 [q]
           (fresh [regex data]
             (== '(rep true) regex)
             (!= () data)
             (regex-matcho regex data regex-NULL)
             (== [regex data] q)))
        '(([(rep true) (_0)] :- (sym _0) (sym _0))
          ([(rep true) (_0 _1)] :- (sym _1) (sym _0) (sym _0))
          ([(rep true) (_0 _1 _2)] :- (sym _2) (sym _1) (sym _0) (sym _0))))))
