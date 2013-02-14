; William E. Byrd's miniKanren version of Matt Might's code for derivative
; parsing of regexp.

; Matt's original Scheme code can be found at
; http://matt.might.net/articles/implementation-of-regular-expression-matching-in-scheme-with-derivatives/

; This file requires core miniKanren (conde, ==, fresh) plus =/= and symbolo.

; In theory, tabling will allow this code to parse CFG's (or at least
; be something close to parsing CFG's).

;;; This version models the 'empty set' regex as failure. As a result, the
;;; miniKanren translations of 'regex-matcho' and 'deltao' merely succeed or fail
;;; rather than unifying with an 'out' variable.
;;;
;;; Oleg insists all true predicates succeed or fail rather than
;;; having an out variable. It is a matter of perspective whether
;;; regex-matcho is a predicate, or rather is returning the empty
;;; string or the empty set.  Although it is probably a matter of
;;; perspective whether the empty set should be a regex.
;;;
;;; We lose the flexibility of generating regex that don't match a
;;; string, or strings that don't match a regex. The advantage
;;; (hopefully) is that the code will be greatly simplified.

;;; Open issue:
;;;
;;; To what extent should constraints be used to enforce terms are in proper, normalized form?
;;; The relational arithmetic system assumes that the user will never instantiate terms incorrectly.
;;; Probably we should just have enough of a constraint to ensure illegal terms are instantiated when
;;; running backwards.
;;;
;;; For example, consider this answer in test 12:
;;;
;;; ((alt (rep (seq _.0 _.1)) _.2) (=/= ((_.0 . #t)) ((_.1 . #t))))
;;;
;;; the (=/= ((_.0 . #t)) ((_.1 . #t))) constraints aren't sufficient.
;;; For example, _.0 could become instantiated to (rep (rep EPSILON)),
;;; which isn't in normal form.  So perhaps those two constraints
;;; aren't very useful.  Need to think this through carefully.
;;;
;;; Another approach would be to add constraints to miniKanren for the
;;; different types of regex terms; the constraints would ensure the
;;; terms are never instantiated incorrectly.  Would need rep, alt,
;;; and seq constraints.

(load "mk.scm")

; <regex> ::= 
;          |  EPSILON                ; Empty/blank pattern (same as #t)
;          |  '<symbol>              ; Symbol
;          |  (alt <regex> <regex>)  ; Alternation
;          |  (seq <regex> <regex>)  ; Sequence
;          |  (rep <regex>)          ; Repetition


;; Special regular expression.
(define EPSILON #t)   ; the empty string

;; Simplifying regex constructors.
(define (valid-seqo exp)
  (fresh (pat1 pat2)
    (== `(seq ,pat1 ,pat2) exp)
    (=/= EPSILON pat1)
    (=/= EPSILON pat2)))

(define (seqo pat1 pat2 out)
  (conde    
    [(== EPSILON pat1) (== pat2 out)]
    [(== EPSILON pat2) (== pat1 out) (=/= EPSILON pat1)]
    [(=/= EPSILON pat1) (=/= EPSILON pat2) (== `(seq ,pat1 ,pat2) out)]))

(define (valid-alto exp)
  (fresh (pat1 pat2)
    (== `(alt ,pat1 ,pat2) exp)
    (=/= pat1 pat2)))

(define (alto pat1 pat2 out)
  (conde
    [(== pat1 pat2) (== pat1 out)]
    [(=/= pat1 pat2) (== `(alt ,pat1 ,pat2) out)]))

(define (valid-repo exp)
  (fresh (pat)
    (== `(rep ,pat) exp)
    (=/= EPSILON pat)
    (conde
      ((symbolo pat))
      ((fresh (re1 re2)
         (== `(seq ,re1 ,re2) pat)
         (valid-seqo pat)))
      ((fresh (re1 re2)
         (== `(alt ,re1 ,re2) pat)
         (valid-alto pat))))))

(define (repo pat out)
  (conde
    [(== EPSILON pat)
     (== EPSILON out)]
    [(conde
       ((symbolo pat) (== `(rep ,pat) out))
       ((fresh (re1 re2)
          (conde
            ((== `(rep ,re1) pat)
             ; remove nested reps
             (== pat out))
            ((== `(seq ,re1 ,re2) pat)
             (== `(rep ,pat) out)
             (valid-seqo pat))
            ((== `(alt ,re1 ,re2) pat)
             (== `(rep ,pat) out)
             (valid-alto pat))))))]))

;; Matching functions.

; deltao : regex
(define (deltao re)
  (conde
    [(== EPSILON re)]
    [(fresh (re1)
       (== `(rep ,re1) re)
       (valid-repo re))]
    [(fresh (re1 re2)
       (== `(alt ,re1 ,re2) re)
       (valid-alto re)
       (conde
         ((deltao re1))
         ((not-deltao re1) (deltao re2))))]
    [(fresh (re1 re2)
       (== `(seq ,re1 ,re2) re)
       (valid-seqo re)
       (deltao re1)
       (deltao re2))]))

(define (not-deltao re)
  (conde
    [(symbolo re)]
    [(fresh (re1 re2)       
       (== `(seq ,re1 ,re2) re)
       (valid-seqo re)
       (conde
         ((not-deltao re1))
         ((deltao re1) (not-deltao re2))))]
    [(fresh (re1 re2)
       (== `(alt ,re1 ,re2) re)
       (valid-alto re)
       (not-deltao re1)
       (not-deltao re2))]))

; d/dco : regex regex-atom regex
(define (d/dco re c out)
  (fresh ()
    (symbolo c)
    (conde
      [(== c re)
       (== EPSILON out)]
      [(fresh (re1 res1)
         (== `(rep ,re1) re)
         (valid-repo re)
         (seqo res1 re out)
         (d/dco re1 c res1))]
      [(fresh (re1 re2 res1 res2)
         (== `(alt ,re1 ,re2) re)
         (valid-alto re)
         (conde
           ((no-d/dco re2 c)
            (d/dco re1 c out))
           ((no-d/dco re1 c)
            (d/dco re2 c out))
           ((alto res1 res2 out)
            (d/dco re1 c res1)
            (d/dco re2 c res2))))]
      [(fresh (re1 re2 res1 res2 res3)
         (== `(seq ,re1 ,re2) re)
         (valid-seqo re)
         (seqo res1 re2 res2)
         (conde
           ((== res2 out) (not-deltao re1))
           ((alto res2 res3 out)
            (deltao re1)
            (d/dco re2 c res3)))
         (d/dco re1 c res1))])))

(define (no-d/dco re c)
  (fresh ()
    (symbolo c)
    (conde
      [(== EPSILON re)]
      [(symbolo re) (=/= c re)]
      [(fresh (re1 res1)
         (== `(rep ,re1) re)
         (valid-repo re)
         (no-d/dco re c))]
      [(fresh (re1 re2 res1 res2 res3)
         (== `(seq ,re1 ,re2) re)
         (valid-seqo re)
         (conde
           ((not-deltao re1))
           ((deltao re1) (no-d/dco re2 c)))
         (no-d/dco re1 c))]
      [(fresh (re1 re2 res1 res2)
         (== `(alt ,re1 ,re2) re)
         (valid-alto re)
         (no-d/dco re1 c)
         (no-d/dco re2 c))])))

; regex-matcho : regex list 
(define (regex-matcho pattern data)
  (conde
    [(== '() data) (deltao pattern)]
    [(fresh (a d res)
       (== `(,a . ,d) data)
       (d/dco pattern a res)
       (regex-matcho res d))]))

;; Tests.
(define-syntax check-expect
  (syntax-rules ()
    [(_ name check expect)
     (begin
       (display "testing ")
       (display name)
       (display "...")
       (newline)
       (if (not (equal? check expect))
           (begin (display "check-expect failed for test ")
                  (display name)
                  (newline)
                  (display "got: ")
                  (newline)
                  (display check)
                  (newline)
                  (display "expected: ")
                  (newline)
                  (display expect)
                  (newline)
                  (newline))))]))

;;; new tests

(check-expect "2"
              (run* (q) (repo EPSILON q))
              '(#t))

(check-expect "3"
              (run* (q) (repo 'foo q))
              '((rep foo)))

(check-expect "3-b"
              (run* (q)
                (fresh (res)
                  (repo 'foo res)
                  (repo res q)))
              '((rep foo)))

(check-expect "3-c"
              (run* (q)
                (fresh (res)
                  (repo EPSILON res)
                  (repo res q)))
              '(#t))

(check-expect "6"
              (run* (q) (alto 'foo 'bar q))
              '((alt foo bar)))

(check-expect "6-b"
              (run* (q) (alto 'foo EPSILON q))
              '((alt foo #t)))

(check-expect "6-c"
              (run* (q) (alto EPSILON 'foo q))
              '((alt #t foo)))

(check-expect "9"
              (run* (q) (seqo EPSILON 'foo q))
              '(foo))

(check-expect "10"
              (run* (q) (seqo 'foo EPSILON q))
              '(foo))

(check-expect "11"
              (run* (q) (seqo 'foo 'bar q))
              '((seq foo bar)))

(check-expect "12"
              (run 10 (q) (deltao q))
              '(#t
                ((rep _.0) (sym _.0))
                ((rep (seq _.0 _.1)) (=/= ((_.0 . #t)) ((_.1 . #t))))
                ((rep (alt _.0 _.1)) (=/= ((_.0 . _.1))))
                ((alt #t _.0) (=/= ((_.0 . #t))))
                ((alt _.0 #t) (sym _.0))
                ((alt (rep _.0) _.1) (=/= ((_.1 rep _.0))) (sym _.0))
                ((seq (rep _.0) (rep _.1)) (sym _.0 _.1))
                ((alt _.0 (rep _.1)) (sym _.0 _.1))
                ((alt (rep (seq _.0 _.1)) _.2) (=/= ((_.0 . #t)) ((_.1 . #t))))))

(check-expect "12-b"
              (run 10 (q) (not-deltao q))
              '((_.0 (sym _.0))
                ((seq _.0 _.1) (=/= ((_.1 . #t))) (sym _.0))
                ((alt _.0 _.1) (=/= ((_.0 . _.1))) (sym _.0 _.1))
                ((seq (rep _.0) _.1) (sym _.0 _.1))
                ((seq (seq _.0 _.1) _.2)
                 (=/= ((_.1 . #t)) ((_.2 . #t)))
                 (sym _.0))
                ((alt _.0 (seq _.1 _.2)) (=/= ((_.2 . #t))) (sym _.0 _.1))
                ((alt (seq _.0 _.1) _.2) (=/= ((_.1 . #t))) (sym _.0 _.2))
                ((seq (alt _.0 _.1) _.2)
                 (=/= ((_.0 . _.1)) ((_.2 . #t)))
                 (sym _.0 _.1))
                ((alt _.0 (alt _.1 _.2))
                 (=/= ((_.1 . _.2)))
                 (sym _.0 _.1 _.2))
                ((alt (alt _.0 _.1) _.2)
                 (=/= ((_.0 . _.1)))
                 (sym _.0 _.1 _.2))))

(check-expect "13"
              (run 10 (q)
                (fresh (re c out)
                  (d/dco re c out)
                  (== `(,re ,c ,out) q)))
              '(((_.0 _.0 #t) (sym _.0))
                (((rep _.0) _.0 (rep _.0)) (sym _.0))
                (((seq _.0 _.1) _.0 _.1) (=/= ((_.1 . #t))) (sym _.0))
                (((alt _.0 #t) _.0 #t) (sym _.0))
                (((alt _.0 _.1) _.0 #t) (=/= ((_.0 . _.1))) (sym _.0 _.1))
                (((alt #t _.0) _.0 #t) (sym _.0))
                (((rep (alt _.0 #t)) _.0 (rep (alt _.0 #t))) (sym _.0))
                (((rep (alt _.0 _.1)) _.0 (rep (alt _.0 _.1))) (=/= ((_.0 . _.1))) (sym _.0 _.1))
                (((rep (alt #t _.0)) _.0 (rep (alt #t _.0))) (sym _.0))
                (((alt _.0 _.1) _.1 #t) (=/= ((_.0 . _.1))) (sym _.0 _.1))))

(check-expect "14"
              (run* (q) (regex-matcho '(seq foo (rep bar)) 
                                      '(foo bar bar bar)))
              '(_.0))

(check-expect "14-b"
              (run* (q) (regex-matcho '(seq foo (rep bar))
                                      '(foo)))
              '(_.0))

(check-expect "14-c"
              (run* (q) (d/dco '(seq foo (rep bar)) 'foo q))
              '((rep bar)))

(check-expect "14-d"
              (run* (q) (valid-seqo '(seq foo (rep bar))))
              '(_.0))

(check-expect "14-e"
              (run* (q) (d/dco 'foo 'foo q))
              '(#t))

(check-expect "14-f"
              (run* (q) (d/dco '(rep bar) 'foo q))
              '())

(check-expect "15"
              (run* (q) (regex-matcho '(seq foo (rep bar)) 
                                      '(foo bar baz bar bar)))
              '())

(check-expect "16"
              (run* (q) (regex-matcho '(seq foo (rep (alt bar baz))) 
                                      '(foo bar baz bar bar)))
              '(_.0))

;;; generate regex patterns that match the input string (!)
;;; (seq foo (rep bar)) was the original regex
;;; The #t's in the answer represent epsilons.  This seems to be okay, actually!
;;; The run expression can produce equivalent regex's; for example,
;;;    (rep (alt foo bar))
;;; and
;;;    (rep (alt bar foo))
;;; Is there a canonical representation of regex's that would avoid these
;;; essentially duplicate answers?

;;; WEB   wow--these answers are very different from the previous answers in the naive mk translation.
(check-expect "20"
              (run 30 (q) (regex-matcho q '(foo bar bar bar)))
              '((seq foo (rep bar)) (seq foo (seq bar (rep bar))) (seq foo (seq bar (seq bar bar))) (seq foo (seq bar (seq bar (rep bar)))) ((seq foo (seq bar (seq bar (seq bar (rep _.0))))) (sym _.0)) (rep (alt foo bar)) (seq foo (seq bar (seq bar (alt bar #t)))) ((seq foo (seq bar (seq bar (seq bar (rep (seq _.0 _.1)))))) (=/= ((_.0 . #t)) ((_.1 . #t)))) ((seq foo (seq bar (seq bar (seq bar (rep (alt _.0 _.1)))))) (=/= ((_.0 . _.1)))) ((seq foo (seq bar (seq bar (seq bar (alt #t _.0))))) (=/= ((_.0 . #t)))) ((seq foo (seq bar (seq bar (seq bar (alt _.0 #t))))) (sym _.0)) (seq foo (rep (alt bar #t))) ((seq foo (seq bar (seq bar (seq bar (alt (rep _.0) _.1))))) (=/= ((_.1 rep _.0))) (sym _.0)) ((seq foo (seq bar (seq bar (alt bar _.0)))) (=/= ((_.0 . bar))) (sym _.0)) ((seq foo (seq bar (seq bar (seq bar (seq (rep _.0) (rep _.1)))))) (sym _.0 _.1)) (seq foo (seq bar (seq bar (alt #t bar)))) (seq foo (seq bar (rep (alt bar #t)))) ((seq foo (seq bar (seq bar (seq bar (alt _.0 (rep _.1)))))) (sym _.0 _.1)) ((seq foo (seq bar (seq bar (seq bar (alt (rep (seq _.0 _.1)) _.2))))) (=/= ((_.0 . #t)) ((_.1 . #t)))) ((seq foo (rep (alt bar _.0))) (=/= ((_.0 . bar))) (sym _.0)) ((seq foo (seq bar (seq bar (seq bar (alt (rep (alt _.0 _.1)) _.2))))) (=/= ((_.0 . _.1)))) ((seq foo (seq bar (seq bar (seq bar (seq (rep _.0) (rep (seq _.1 _.2))))))) (=/= ((_.1 . #t)) ((_.2 . #t))) (sym _.0)) ((seq foo (seq bar (seq bar (seq bar (alt (alt #t _.0) _.1))))) (=/= ((_.0 . #t)))) ((seq foo (seq bar (seq bar (seq bar (seq (rep _.0) (rep (alt _.1 _.2))))))) (=/= ((_.1 . _.2))) (sym _.0)) ((seq foo (seq bar (seq bar (seq bar (seq (rep _.0) (alt #t _.1)))))) (=/= ((_.1 . #t))) (sym _.0)) (seq foo (seq bar (seq bar (rep (alt bar #t))))) ((seq foo (seq bar (seq bar (seq bar (alt (seq _.0 _.1) #t))))) (=/= ((_.1 . #t))) (sym _.0)) ((seq foo (seq bar (seq bar (seq bar (seq (rep (seq _.0 _.1)) (rep _.2)))))) (=/= ((_.0 . #t)) ((_.1 . #t))) (sym _.2)) (rep (alt bar foo)) (seq foo (rep (alt #t bar))))

;;; old answers from naive mk translation
              
              ;; '((seq foo (rep bar)) ; jackpot!
              ;;   (rep (alt foo bar))
              ;;   (rep (alt bar foo)) ; equivalent to a previous regex
              ;;   (seq foo (rep (alt #t bar)))
              ;;   (seq foo (alt #t (rep bar)))
              ;;   (alt #t (seq foo (rep bar)))
              ;;   (seq foo (rep (alt bar #t)))
              ;;   (seq (rep foo) (rep bar))
              ;;   (rep (alt foo (rep bar)))
              ;;   (seq foo (alt foo (rep bar)))
              ;;   (rep (seq foo (rep bar)))
              ;;   (alt foo (seq foo (rep bar)))
              ;;   (seq foo (rep (alt #t (rep bar))))
              ;;   (seq foo (seq bar (rep bar)))
              ;;   ((seq foo (rep (alt bar _.0))) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0))
              ;;   ((seq foo (rep (alt _.0 bar))) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0))
              ;;   ((seq foo (rep (seq bar (rep _.0)))) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0))
              ;;   (seq foo (rep (seq bar (rep bar))))
              ;;   (seq (alt #t foo) (rep bar))
              ;;   (seq foo (rep (seq bar (rep foo))))
              ;;   (seq foo (alt (rep bar) #t))
              ;;   (rep (alt (rep bar) foo))
              ;;   (seq foo (seq (rep bar) bar))
              ;;   ((seq foo (rep (seq (rep _.0) bar))) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0))
              ;;   (rep (alt #t (alt foo bar)))
              ;;   (seq foo (rep (seq (rep bar) bar)))
              ;;   ((seq foo (alt _.0 (rep bar))) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0))
              ;;   (seq foo (alt bar (rep bar)))
              ;;   (alt #t (rep (alt foo bar)))
              ;;   (rep (alt foo (alt #t bar))))

              )

(check-expect "20-ab"
;;; takes around 10 seconds to generate 10,0000 answers under Petite
;;; Here's the 1,000th answer
              (car (reverse (run 1000 (q) (regex-matcho q '(foo bar bar bar)))))
              '((seq foo (seq bar (seq (seq bar bar) (alt (alt (rep (alt _.0 _.1)) _.2) _.3))))
                (=/= ((_.0 . _.1)))))

(check-expect "20-a"
              (run 1 (q) (regex-matcho '(alt #t (seq foo (rep bar))) '(foo bar bar bar)))
              '(_.0))

(check-expect "20-aa"
              (run 1 (q) (regex-matcho '(alt (seq foo (rep bar)) #t) '(foo bar bar bar)))
              '(_.0))

(check-expect "20-c"
              (run 1 (q) (d/dco '(alt #t (seq foo (rep bar))) 'foo q))
              '((rep bar)))

(check-expect "20-cc"
              (run 1 (q) (d/dco '(alt (seq foo (rep bar)) #t) 'foo q))
              '((rep bar)))

(check-expect "20-c1"
              (run 1 (q) (d/dco '#t 'foo q))
              '())

(check-expect "20-c2"
              (run 1 (q) (d/dco '(seq foo (rep bar)) 'foo q))
              '((rep bar)))

(check-expect "20-d"
              (run 1 (q) (d/dco '(alt (seq foo (rep bar)) #t) 'foo q))
              '((rep bar)))

(check-expect "20-e"
              ;;; illegal alt with duplicate patterns
              (run 1 (q) (d/dco '(alt (seq foo (rep bar)) (seq foo (rep bar))) 'foo q))
              '())

(check-expect "20-z"
              (run 1 (q) (fresh (e1 e2) (regex-matcho q '(foo bar bar bar)) (== `(alt ,e1 ,e2) q)))
              '((alt (seq foo (rep bar)) #t)))

;;; look for the literal match regex
;;; easy version
(check-expect "21"
              (run 1 (q)
                (== `(seq foo (seq bar bar)) q)
                (regex-matcho q 
                              '(foo bar bar)))
              '((seq foo (seq bar bar))))

;;; look for the literal match regex
;;; hard version (generate and test)
(check-expect "22"
              (run 1 (q)
                (regex-matcho q 
                              '(foo bar bar))
                (== `(seq foo (seq bar bar)) q))
              '((seq foo (seq bar bar))))

;;; look for the literal match regex (longer)
;;; easy version
(check-expect "23"
              (run 1 (q)
                (== `(seq foo (seq bar (seq bar bar))) q)
                (regex-matcho q 
                              '(foo bar bar bar)))
              '((seq foo (seq bar (seq bar bar)))))

;;; look for the literal match regex (longer)
;;; hard version (generate and test)
(check-expect "24"
              (run 1 (q)
                (regex-matcho q 
                              '(foo bar bar bar))
                (== `(seq foo (seq bar (seq bar bar))) q))
              '((seq foo (seq bar (seq bar bar)))))

;;; generate regex, and data that matches.
(check-expect "25"
              (run 30 (q)
                (fresh (regex data)
                  (regex-matcho regex 
                                data)
                  (== `(,regex ,data) q)))
              '((#t ()) (((rep _.0) ()) (sym _.0)) ((_.0 (_.0)) (sym _.0)) (((rep (seq _.0 _.1)) ()) (=/= ((_.0 . #t)) ((_.1 . #t)))) (((rep (alt _.0 _.1)) ()) (=/= ((_.0 . _.1)))) (((alt #t _.0) ()) (=/= ((_.0 . #t)))) (((alt _.0 #t) ()) (sym _.0)) (((alt (rep _.0) _.1) ()) (=/= ((_.1 rep _.0))) (sym _.0)) (((seq (rep _.0) (rep _.1)) ()) (sym _.0 _.1)) (((rep _.0) (_.0)) (sym _.0)) (((alt _.0 (rep _.1)) ()) (sym _.0 _.1)) (((alt (rep (seq _.0 _.1)) _.2) ()) (=/= ((_.0 . #t)) ((_.1 . #t)))) (((alt (rep (alt _.0 _.1)) _.2) ()) (=/= ((_.0 . _.1)))) (((seq (rep _.0) (rep (seq _.1 _.2))) ()) (=/= ((_.1 . #t)) ((_.2 . #t))) (sym _.0)) (((alt (alt #t _.0) _.1) ()) (=/= ((_.0 . #t)))) (((seq (rep _.0) (rep (alt _.1 _.2))) ()) (=/= ((_.1 . _.2))) (sym _.0)) (((seq (rep _.0) (alt #t _.1)) ()) (=/= ((_.1 . #t))) (sym _.0)) (((rep _.0) (_.0 _.0)) (sym _.0)) (((alt (seq _.0 _.1) #t) ()) (=/= ((_.1 . #t))) (sym _.0)) (((seq (rep (seq _.0 _.1)) (rep _.2)) ()) (=/= ((_.0 . #t)) ((_.1 . #t))) (sym _.2)) (((alt (alt _.0 #t) _.1) ()) (sym _.0)) (((alt (alt _.0 _.1) #t) ()) (=/= ((_.0 . _.1))) (sym _.0 _.1)) (((alt _.0 #t) (_.0)) (sym _.0)) (((seq (rep _.0) (alt _.1 #t)) ()) (sym _.0 _.1)) (((seq _.0 (rep _.1)) (_.0)) (sym _.0 _.1)) (((alt _.0 (rep (seq _.1 _.2))) ()) (=/= ((_.1 . #t)) ((_.2 . #t))) (sym _.0)) (((rep _.0) (_.0 _.0 _.0)) (sym _.0)) (((alt _.0 (rep (alt _.1 _.2))) ()) (=/= ((_.1 . _.2))) (sym _.0)) (((seq _.0 _.1) (_.0 _.1)) (sym _.0 _.1)) (((seq (rep (alt _.0 _.1)) (rep _.2)) ()) (=/= ((_.0 . _.1))) (sym _.2))))

;;; generate regexs, and *non-empty* data, that match
;;; This test was *extremely* slow under the naive miniKanren translation:  even run 3 took a while.
;;; Now run 1000 takes 4.5 seconds under Petite.
(check-expect "27"
              (run 20 (q)
                (fresh (regex data)
                  (=/= '() data)
                  (regex-matcho regex
                                data)
                  (== `(,regex ,data) q)))
              '(((_.0 (_.0)) (sym _.0)) (((rep _.0) (_.0)) (sym _.0)) (((rep _.0) (_.0 _.0)) (sym _.0)) (((alt _.0 #t) (_.0)) (sym _.0)) (((seq _.0 (rep _.1)) (_.0)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0)) (sym _.0)) (((seq _.0 _.1) (_.0 _.1)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0)) (sym _.0)) (((seq _.0 (rep (seq _.1 _.2))) (_.0)) (=/= ((_.1 . #t)) ((_.2 . #t))) (sym _.0)) (((seq _.0 (rep (alt _.1 _.2))) (_.0)) (=/= ((_.1 . _.2))) (sym _.0)) (((seq _.0 (alt #t _.1)) (_.0)) (=/= ((_.1 . #t))) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((alt _.0 _.1) (_.0)) (=/= ((_.0 . _.1))) (sym _.0 _.1)) (((seq _.0 (alt _.1 #t)) (_.0)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((alt #t _.0) (_.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((seq _.0 (alt (rep _.1) _.2)) (_.0)) (=/= ((_.2 rep _.1))) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0))))

;;; generate regexs, and *non-null* data
;;; This test was problematic under the naive mk translation.
(check-expect "28"
              (run 30 (q)
                (fresh (regex data)
                  (=/= '() data)
                  (regex-matcho regex 
                                data)
                  (== `(,regex ,data) q)))
              '(((_.0 (_.0)) (sym _.0)) (((rep _.0) (_.0)) (sym _.0)) (((rep _.0) (_.0 _.0)) (sym _.0)) (((alt _.0 #t) (_.0)) (sym _.0)) (((seq _.0 (rep _.1)) (_.0)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0)) (sym _.0)) (((seq _.0 _.1) (_.0 _.1)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0)) (sym _.0)) (((seq _.0 (rep (seq _.1 _.2))) (_.0)) (=/= ((_.1 . #t)) ((_.2 . #t))) (sym _.0)) (((seq _.0 (rep (alt _.1 _.2))) (_.0)) (=/= ((_.1 . _.2))) (sym _.0)) (((seq _.0 (alt #t _.1)) (_.0)) (=/= ((_.1 . #t))) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((alt _.0 _.1) (_.0)) (=/= ((_.0 . _.1))) (sym _.0 _.1)) (((seq _.0 (alt _.1 #t)) (_.0)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((alt #t _.0) (_.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((seq _.0 (alt (rep _.1) _.2)) (_.0)) (=/= ((_.2 rep _.1))) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((seq _.0 (seq (rep _.1) (rep _.2))) (_.0)) (sym _.0 _.1 _.2)) (((seq _.0 (rep _.1)) (_.0 _.1)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((rep (alt _.0 #t)) (_.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((seq _.0 (alt _.1 (rep _.2))) (_.0)) (sym _.0 _.1 _.2)) (((seq _.0 (alt (rep (seq _.1 _.2)) _.3)) (_.0)) (=/= ((_.1 . #t)) ((_.2 . #t))) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0))))

(check-expect "28-b"
              (run 10 (q)
                (fresh (a b c d regex data)
                  (== `(,a ,b ,b ,c ,c ,d) data)
                  (=/= a b)
                  (=/= b c)
                  (=/= c d)
                  (=/= d a)
                  (regex-matcho regex 
                                data)
                  (== `(,regex ,data) q)))
              '((((rep (alt _.0 _.1)) (_.0 _.1 _.1 _.0 _.0 _.1)) (=/= ((_.0 . _.1))) (sym _.0 _.1)) (((seq _.0 (seq _.1 (seq _.1 (seq _.2 (seq _.2 _.3))))) (_.0 _.1 _.1 _.2 _.2 _.3)) (=/= ((_.0 . _.1)) ((_.1 . _.2)) ((_.2 . _.3)) ((_.3 . _.0))) (sym _.0 _.1 _.2 _.3)) (((seq _.0 (rep (alt _.1 _.2))) (_.0 _.1 _.1 _.2 _.2 _.1)) (=/= ((_.0 . _.1)) ((_.1 . _.2))) (sym _.0 _.1 _.2)) (((seq _.0 (seq _.1 (seq _.1 (seq _.2 (seq _.2 (rep _.3)))))) (_.0 _.1 _.1 _.2 _.2 _.3)) (=/= ((_.0 . _.1)) ((_.1 . _.2)) ((_.2 . _.3)) ((_.3 . _.0))) (sym _.0 _.1 _.2 _.3)) (((rep (alt _.0 _.1)) (_.1 _.0 _.0 _.1 _.1 _.0)) (=/= ((_.1 . _.0))) (sym _.0 _.1)) (((seq _.0 (seq _.1 (seq _.1 (seq _.2 (seq _.2 (seq _.3 (rep _.4))))))) (_.0 _.1 _.1 _.2 _.2 _.3)) (=/= ((_.0 . _.1)) ((_.1 . _.2)) ((_.2 . _.3)) ((_.3 . _.0))) (sym _.0 _.1 _.2 _.3 _.4)) (((seq _.0 (seq _.1 (seq _.1 (seq _.2 (seq _.2 (alt _.3 #t)))))) (_.0 _.1 _.1 _.2 _.2 _.3)) (=/= ((_.0 . _.1)) ((_.1 . _.2)) ((_.2 . _.3)) ((_.3 . _.0))) (sym _.0 _.1 _.2 _.3)) (((seq _.0 (seq _.1 (rep (alt _.1 _.2)))) (_.0 _.1 _.1 _.2 _.2 _.1)) (=/= ((_.0 . _.1)) ((_.1 . _.2))) (sym _.0 _.1 _.2)) (((seq _.0 (seq _.1 (seq _.1 (seq _.2 (seq _.2 (seq _.3 (rep (seq _.4 _.5)))))))) (_.0 _.1 _.1 _.2 _.2 _.3)) (=/= ((_.0 . _.1)) ((_.1 . _.2)) ((_.2 . _.3)) ((_.3 . _.0)) ((_.4 . #t)) ((_.5 . #t))) (sym _.0 _.1 _.2 _.3)) (((seq _.0 (seq _.1 (seq _.1 (seq _.2 (seq _.2 (seq _.3 (rep (alt _.4 _.5)))))))) (_.0 _.1 _.1 _.2 _.2 _.3)) (=/= ((_.0 . _.1)) ((_.1 . _.2)) ((_.2 . _.3)) ((_.3 . _.0)) ((_.4 . _.5))) (sym _.0 _.1 _.2 _.3))))

(check-expect "29a"
              (run 10 (q)
                (fresh (regex data)
                  (== '(rep #t) regex)
                  (=/= '() data)
                  (regex-matcho regex data)
                  (== `(,regex ,data) q)))
              '())

(check-expect "29b"
              (run 10 (q)
                (fresh (regex data out)
                  (== '(rep #t) regex)
                  (regex-matcho regex data)))
              '())

(check-expect "29f"
              (run 10 (q)
                (fresh (regex data out)
                  (== '(seq #t #t) regex)
                  (regex-matcho regex data)))
              '())

(check-expect "29z"
              (run* (q)
                (fresh (regex data)
                  (== #t regex)
                  (=/= '() data)
                  (regex-matcho regex data)
                  (== `(,regex ,data) q)))
              '())

(check-expect "30"
              (run* (q) (repo EPSILON q))
              '(#t))

;;; original tests

(check-expect "31"
              (run* (q) (d/dco 'baz 'f q))
              '())

(check-expect "32"
              (run* (q) (d/dco '(seq foo barn) 'foo q))
              '(barn))

(check-expect "33"
              (run* (q) (d/dco '(alt (seq foo bar) (seq foo (rep baz))) 'foo q))
              '((alt bar (rep baz))))

(check-expect "34"
              (run* (q) (regex-matcho '(seq foo (rep bar)) 
                                      '(foo bar bar bar)))
              '(_.0))

(check-expect "35"
              (run* (q) (regex-matcho '(seq foo (rep bar)) 
                                      '(foo bar baz bar bar)))
              '())

(check-expect "36"
              (run* (q) (regex-matcho '(seq foo (rep (alt bar baz))) 
                                      '(foo bar baz bar bar)))
              '(_.0))

