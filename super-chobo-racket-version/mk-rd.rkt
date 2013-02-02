#lang racket

; Asumu Takikawa and Sam Tobin-Hochstadt's greatly cleaned up version
; of William E. Byrd's Super Chobo miniKanren version of Matt Might's
; code for derivative parsing of regexp.

; Matt's original Scheme code can be found at
; http://matt.might.net/articles/implementation-of-regular-expression-matching-in-scheme-with-derivatives/

; This file requires core miniKanren (conde, ==, fresh) plus =/= and symbolo.

; In theory, tabling will allow this code to parse CFG's (or at least
; be something close to parsing CFG's).

(require "mk.rkt"
         "racket-compat.rkt"
         (prefix-in ru: rackunit))

(provide (all-defined-out))

; <regex> ::= #f                     ; Unmatchable pattern
;          |  #t                     ; Empty/blank pattern
;          |  '<symbol>              ; Symbol
;          |  (alt <regex> <regex>)  ; Alternation
;          |  (seq <regex> <regex>)  ; Sequence
;          |  (rep <regex>)          ; Repetition


;; Special regular expressions.
(define regex-NULL #f)    ; -- the empty set
(define regex-BLANK #t)   ; -- the empty string


;; Simplifying regex constructors.
(define (seqo pat1 pat2 out)
  (conde
    ((== regex-NULL pat1) (== regex-NULL out))
    ((== regex-NULL pat2) (== regex-NULL out) (=/= regex-NULL pat1))
    ((== regex-BLANK pat1) (== pat2 out) (=/= regex-NULL pat2))
    ((== regex-BLANK pat2) (== pat1 out) (=/= regex-NULL pat1) (=/= regex-BLANK pat1))
    ((=/= regex-NULL pat1) (=/= regex-BLANK pat1) (=/= regex-NULL pat2) (=/= regex-BLANK pat2) (== `(seq ,pat1 ,pat2) out))))

(define (alto pat1 pat2 out)
  (conde
    ((== regex-NULL pat1) (== pat2 out))
    ((== regex-NULL pat2) (== pat1 out) (=/= regex-NULL pat1))
    ((=/= regex-NULL pat1) (=/= regex-NULL pat2) (== `(alt ,pat1 ,pat2) out))))

(define (repo pat out)
  (conde
    ((== regex-BLANK out)
     (conde
       ((== regex-NULL pat))
       ((== regex-BLANK pat))))
    ((=/= regex-NULL pat) (=/= regex-BLANK pat) (== `(rep ,pat) out))))

;; Matching functions.

; deltao : regex boolean
; WEB: what about the case of alt--does it really return a boolean,
; or merely a value that can be interpreted as true or false?
(define (deltao re out)
  (conde
    ((== regex-BLANK re) (== regex-BLANK out))
    ((== regex-NULL re) (== regex-NULL out))
    ((symbolo re) (== regex-NULL out))
    ((fresh (re1)
       (== `(rep ,re1) re)
       (== regex-BLANK out)))
    ((fresh (re1 re2 res1 res2)
       (== `(seq ,re1 ,re2) re)
       (deltao re1 res1)
       (deltao re2 res2)
       (seqo res1 res2 out)))
    ((fresh (re1 re2 res1 res2)
       (== `(alt ,re1 ,re2) re)
       (deltao re1 res1)
       (deltao re2 res2)
       (alto res1 res2 out)))))

; regex-derivativeo : regex regex-atom regex
(define (regex-derivativeo re c out)
  (fresh ()
    (symbolo c)
    (conde
      ((== regex-BLANK re) (== regex-NULL out))
      ((== regex-NULL re) (== regex-NULL out))
      ((symbolo re)
       (conde
         ((== c re) (== regex-BLANK out))
         ((=/= c re) (== regex-NULL out))))
      ((fresh (re1 res1 res2)
         (== `(rep ,re1) re)
         (d/dco re1 c res1)
         (repo re1 res2)
         (seqo res1 res2 out)))
      ((fresh (re1 re2 res1 res2)
         (== `(alt ,re1 ,re2) re)
         (d/dco re1 c res1)
         (d/dco re2 c res2)
         (alto res1 res2 out)))
      ((fresh (re1 re2 res1 res2 res3 res4 res5)
; WEB: this is going to be trouble
         (== `(seq ,re1 ,re2) re)
         (d/dco re1 c res1)
         (deltao re1 res3)
         (d/dco re2 c res4)
         (seqo res1 re2 res2)
         (seqo res3 res4 res5)
         (alto res2 res5 out))))))

; d/dco = regex-derivativeo
; WEB: what's the point of this???
; Especially since d/dco is called inside regex-derivativeo!
(define d/dco regex-derivativeo)

; regex-matcho : regex list boolean 
(define (regex-matcho pattern data out)
  (conde
    ((== '() data)
; WEB: I strongly suspect this can be simplified.  This is dependent
; upon deltao's output being a true boolean, though.
     (fresh (res)
       (conde
         ((== regex-BLANK out) (== regex-BLANK res))
         ((== regex-NULL out) (=/= regex-BLANK res)))
       (deltao pattern res)))
    ((fresh (a d res)
       (== `(,a . ,d) data)
       (d/dco pattern a res)
       (regex-matcho res d out)))))

;; Tests.

;; a `check-expect` macro that expands into a test submodule
;;
;; would be more idiomatic to just use `check-equal?` directly
;; but defined this way for compatibility (for now)
(define-syntax-rule (check-expect check expect)
  (module+ test (ru:check-equal? check expect)))

;;; new tests

(check-expect (run* (q) (repo regex-NULL q))
              `(,regex-BLANK))

(check-expect (run* (q) (repo regex-BLANK q))
              `(,regex-BLANK))

(check-expect (run* (q) (repo 'foo q))
              `((rep foo)))

(check-expect (run* (q) (alto regex-NULL 'foo q))
              `(foo))

(check-expect (run* (q) (alto 'foo regex-NULL q))
              `(foo))

(check-expect (run* (q) (alto 'foo 'bar q))
              `((alt foo bar)))

(check-expect (run* (q) (seqo regex-NULL 'foo q))
              `(,regex-NULL))

(check-expect (run* (q) (seqo 'foo regex-NULL q))
              `(,regex-NULL))

(check-expect (run* (q) (seqo regex-BLANK 'foo q))
              '(foo))

(check-expect (run* (q) (seqo 'foo regex-BLANK q))
              '(foo))

(check-expect (run* (q) (seqo 'foo 'bar q))
              '((seq foo bar)))

(check-expect (run 10 (q)
                (fresh (re out)
                  (deltao re out)
                  (== `(,re ,out) q)))
              '((#t #t)
                (#f #f)
                ((_.0 #f) (sym _.0))
                ((rep _.0) #t)                
                ((seq #t #t) #t)
                ((alt #t #t) (alt #t #t))
                ((seq #t #f) #f)
                ((alt #t #f) #t)
                ((seq #f #t) #f)
                ((alt #f #t) #t)))

(check-expect (run 5 (q)
                (fresh (re c out)
                  (regex-derivativeo re c out)
                  (== `(,re ,c ,out) q)))
              '(((#t _.0 #f) (sym _.0))
                ((#f _.0 #f) (sym _.0))
                ((_.0 _.0 #t) (sym _.0))
                ((_.0 _.1 #f) (=/= ((_.1 . _.0))) (sym _.0 _.1))
                (((rep #t) _.0 #f) (sym _.0))))

(check-expect (run* (q) (regex-matcho '(seq foo (rep bar)) 
                                      '(foo bar bar bar)
                                      regex-BLANK))
              '(_.0))

(check-expect (run* (q) (regex-matcho '(seq foo (rep bar)) 
                                      '(foo bar baz bar bar)
                                      regex-NULL))
              '(_.0))

(check-expect (run* (q) (regex-matcho '(seq foo (rep (alt bar baz))) 
                                      '(foo bar baz bar bar)
                                      regex-BLANK))
              '(_.0))

;;; running backwards for real
;;; generate strings that match the pattern
;;; seems to get slow surprisingly fast.  probably a goal ordering issue
(check-expect (run 6 (q) (regex-matcho '(seq foo (rep bar)) 
                                      q
                                      regex-BLANK))
              '((foo)
                (foo bar)
                (foo bar bar)
                (foo bar bar bar)
                (foo bar bar bar bar)
                (foo bar bar bar bar bar)))

;;; generate strings that *don't* match the pattern (!)
(check-expect (run 15 (q) (regex-matcho '(seq foo (rep bar)) 
                                      q
                                      regex-NULL))
              '(()
                (bar)
                ((_.0) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0))
                ((foo _.0) (=/= ((_.0 . bar))) (sym _.0))
                ((bar _.0) (sym _.0))
                ((_.0 _.1) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0 _.1))
                ((foo _.0 _.1) (=/= ((_.0 . bar))) (sym _.0 _.1))
                ((bar _.0 _.1) (sym _.0 _.1))
                ((_.0 _.1 _.2)
                 (=/= ((_.0 . bar)) ((_.0 . foo)))
                 (sym _.0 _.1 _.2))
                ((foo _.0 _.1 _.2) (=/= ((_.0 . bar))) (sym _.0 _.1 _.2))
                ((foo bar _.0) (=/= ((_.0 . bar))) (sym _.0))
                ((bar _.0 _.1 _.2) (sym _.0 _.1 _.2))
                ((_.0 _.1 _.2 _.3)
                 (=/= ((_.0 . bar)) ((_.0 . foo)))
                 (sym _.0 _.1 _.2 _.3))
                ((foo _.0 _.1 _.2 _.3)
                 (=/= ((_.0 . bar)))
                 (sym _.0 _.1 _.2 _.3))
                ((bar _.0 _.1 _.2 _.3) (sym _.0 _.1 _.2 _.3))))

;;; again, generate strings that *don't* match the pattern (!)
;;; this time, the output can be anything other than epsilon (as opposed to the empty set)
;;; Seems to generate the same answers as with the empty-set, which is good
;;; This distinction should disappear if regex-matcho can be simplified.
(check-expect (run 15 (q)
                (fresh (out)
                  (=/= regex-BLANK out)
                  (regex-matcho '(seq foo (rep bar)) 
                                q
                                out)))
              '(()
                (bar)
                ((_.0) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0))
                ((foo _.0) (=/= ((_.0 . bar))) (sym _.0))
                ((bar _.0) (sym _.0))
                ((_.0 _.1) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0 _.1))
                ((foo _.0 _.1) (=/= ((_.0 . bar))) (sym _.0 _.1))
                ((bar _.0 _.1) (sym _.0 _.1))
                ((_.0 _.1 _.2)
                 (=/= ((_.0 . bar)) ((_.0 . foo)))
                 (sym _.0 _.1 _.2))
                ((foo _.0 _.1 _.2) (=/= ((_.0 . bar))) (sym _.0 _.1 _.2))
                ((foo bar _.0) (=/= ((_.0 . bar))) (sym _.0))
                ((bar _.0 _.1 _.2) (sym _.0 _.1 _.2))
                ((_.0 _.1 _.2 _.3)
                 (=/= ((_.0 . bar)) ((_.0 . foo)))
                 (sym _.0 _.1 _.2 _.3))
                ((foo _.0 _.1 _.2 _.3)
                 (=/= ((_.0 . bar)))
                 (sym _.0 _.1 _.2 _.3))
                ((bar _.0 _.1 _.2 _.3) (sym _.0 _.1 _.2 _.3))))

;;; generate regex patterns that match the input string (!)
;;; (seq foo (rep bar)) was the original regex
;;; The #t's in the answer represent epsilons.  This seems to be okay, actually!
;;; The run expression can produce equivalent regex's; for example,
;;;    (rep (alt foo bar))
;;; and
;;;    (rep (alt bar foo))
;;; Is there a canonical representation of regex's that would avoid these
;;; essentially duplicate answers?
(check-expect (run 30 (q) (regex-matcho q 
                                      '(foo bar bar bar)
                                      regex-BLANK))
              '((rep (alt foo bar))
                (rep (alt bar foo)) ; equivalent to previous regex
                (seq foo (rep bar)) ; jackpot!
                (rep (seq foo (rep bar)))
                (rep (alt bar (rep foo)))
                (rep (alt #t (alt foo bar)))
                (alt #t (rep (alt foo bar)))
                (rep (alt foo (alt #t bar)))
                (rep (seq #t (alt foo bar)))
                (seq #t (rep (alt foo bar)))
                (rep (alt #t (alt bar foo)))
                (alt #t (rep (alt bar foo)))
                (seq foo (rep (alt #t bar)))
                (rep (alt foo (seq #t bar)))
                (rep (alt bar (alt #t foo)))
                (rep (seq #t (alt bar foo)))
                (seq #t (rep (alt bar foo)))
                (rep (alt foo (alt #f bar)))
                (rep (alt #f (alt foo bar)))
                (rep (rep (seq foo (rep bar))))
                (alt #f (rep (alt foo bar)))
                (seq foo (rep (seq #t bar)))
                (rep (alt bar (seq #t foo)))
                (seq foo (alt #t (rep bar)))
                (alt #t (seq foo (rep bar)))
                (seq foo (rep (alt #f bar)))
                (rep (alt foo (alt bar #t)))
                (rep (alt #f (alt bar foo)))
                (rep (alt bar (alt #f foo)))
                (rep (alt bar (rep (rep foo))))))

;;; look for the literal match regex
;;; easy version
(check-expect (run 1 (q)
                (== `(seq foo (seq bar bar)) q)
                (regex-matcho q 
                              '(foo bar bar)
                              regex-BLANK))
              '((seq foo (seq bar bar))))

;;; look for the literal match regex
;;; hard version (generate and test)
(check-expect (run 1 (q)
                (regex-matcho q 
                              '(foo bar bar)
                              regex-BLANK)
                (== `(seq foo (seq bar bar)) q))
              '((seq foo (seq bar bar))))

;;; look for the literal match regex (longer)
;;; easy version
(check-expect (run 1 (q)
                (== `(seq foo (seq bar (seq bar bar))) q)
                (regex-matcho q 
                              '(foo bar bar bar)
                              regex-BLANK))
              '((seq foo (seq bar (seq bar bar)))))

;;; look for the literal match regex (longer)
;;; hard version (generate and test)
;;; this test doesn't seem to come back (at least not quickly)
#;(check-expect (run 1 (q)
                (regex-matcho q 
                              '(foo bar bar bar)
                              regex-BLANK)
                (== `(seq foo (seq bar (seq bar bar))) q))
              '((seq foo (seq bar (seq bar bar)))))


;;; generate regex, and data that matches.
;;; interesting--the data is always null
(check-expect (run 30 (q)
                (fresh (regex data)
                  (regex-matcho regex 
                                data
                                regex-BLANK)
                  (== `(,regex ,data) q)))
              '((#t ())
                ((rep _.0) ())
                ((seq #t #t) ())
                ((alt #t #f) ())
                ((alt #f #t) ())
                (((alt #t _.0) ()) (sym _.0))
                ((seq #t (rep _.0)) ())
                (((alt _.0 #t) ()) (sym _.0))
                ((_.0 (_.0)) (sym _.0))
                ((alt #f (rep _.0)) ())
                ((seq #t (seq #t #t)) ())
                ((seq (rep _.0) #t) ())
                ((alt #t (seq #t #f)) ())
                ((seq #t (alt #t #f)) ())
                (((alt _.0 (rep _.1)) ()) (sym _.0))
                ((alt (rep _.0) #f) ())
                ((seq #t (alt #f #t)) ())
                ((alt #t (seq #f #t)) ())
                (((seq #t (alt #t _.0)) ()) (sym _.0))               
                (((alt #t (seq #t _.0)) ()) (sym _.0))
                (((alt (rep _.0) _.1) ()) (sym _.1))
                ((alt #f (seq #t #t)) ())
                ((alt #t (seq #f #f)) ())
                ((alt #t (alt #f #f)) ())
                (((seq #t (alt _.0 #t)) ()) (sym _.0))
                (((alt #t (seq _.0 #t)) ()) (sym _.0))
                ((seq #t (seq #t (rep _.0))) ())
                ((alt #f (alt #t #f)) ())
                (((alt #t (seq #f _.0)) ()) (sym _.0))
                (((alt #t (alt #f _.0)) ()) (sym _.0))))

;;; generate regex, and data that *doesn't* match.
(check-expect (run 30 (q)
                (fresh (regex data)
                  (regex-matcho regex 
                                data
                                regex-NULL)
                  (== `(,regex ,data) q)))
              '((#f ())
                ((_.0 ()) (sym _.0))
                ((#t (_.0)) (sym _.0))
                ((alt #t #t) ())
                ((seq #t #f) ())
                ((seq #f #t) ())
                (((seq #t _.0) ()) (sym _.0))
                ((#f (_.0)) (sym _.0))
                ((alt #f #f) ())
                ((seq #f #f) ())
                ((alt #t (rep _.0)) ())
                (((seq _.0 #t) ()) (sym _.0))
                ((#t (_.0 _.1)) (sym _.0 _.1))
                (((alt #f _.0) ()) (sym _.0))
                (((seq #f _.0) ()) (sym _.0))
                (((alt _.0 #f) ()) (sym _.0))
                (((seq _.0 #f) ()) (sym _.0))
                ((#t (_.0 _.1 _.2)) (sym _.0 _.1 _.2))
                ((seq #f (rep _.0)) ())
                (((alt _.0 _.1) ()) (sym _.0 _.1))
                (((seq _.0 _.1) ()) (sym _.0 _.1))
                ((#f (_.0 _.1)) (sym _.0 _.1))
                ((alt #t (seq #t #t)) ())
                ((#t (_.0 _.1 _.2 _.3)) (sym _.0 _.1 _.2 _.3))
                ((alt #t (alt #t #t)) ())
                ((seq #t (alt #t #t)) ())
                ((alt (rep _.0) #t) ())
                ((#t (_.0 _.1 _.2 _.3 _.4)) (sym _.0 _.1 _.2 _.3 _.4))
                ((seq #t (seq #t #f)) ())
                ((alt #t (alt #t #f)) ())))

;;; generate regexs, and *non-empty* data, that match
;;; This is *amazingly* slow to generate answers.  Even a run2 takes a while.
;;; Very interesting...
(check-expect (run 2 (q)
                (fresh (regex data)
                  (=/= '() data)
                  (regex-matcho regex 
                                data
                                regex-BLANK)
                  (== `(,regex ,data) q)))
              '(((_.0 (_.0)) (sym _.0))
                (((rep _.0) (_.0)) (sym _.0))))

;;; generate regexs, and *non-null* data, that *don't* match
;;; these answers come back immediately, as opposed to the
;;; non-empty data that *does* match.  Why???
;;;
;;; Also, I'm nervous about having #f as the regex.  Is this really
;;; legit, from a type standpoint?
;;;
;;;
;;; longer runs (such as run 100) generate more interesting answers, including:
;;; (((rep #t) (_.0 _.1 _.2)) (sym _.0 _.1 _.2))
;;; this answer is suspect, though, since the simplifying rep constructor
;;; simplified (rep #t) to #t.  Why didn't this happen here?  This
;;; may indicate a larger problem.
;;;
;;; is there a way to avoid so many boring answers?
(check-expect (run 15 (q)
                (fresh (regex data)
                  (=/= '() data)
                  (regex-matcho regex 
                                data
                                regex-NULL)
                  (== `(,regex ,data) q)))
              '(((#t (_.0)) (sym _.0))
                ((#f (_.0)) (sym _.0))
                ((#t (_.0 _.1)) (sym _.0 _.1))
                ((#t (_.0 _.1 _.2)) (sym _.0 _.1 _.2))
                ((#f (_.0 _.1)) (sym _.0 _.1))
                ((#t (_.0 _.1 _.2 _.3)) (sym _.0 _.1 _.2 _.3))
                ((#t (_.0 _.1 _.2 _.3 _.4)) (sym _.0 _.1 _.2 _.3 _.4))
                ((_.0 (_.1)) (=/= ((_.1 . _.0))) (sym _.0 _.1))
                ((#f (_.0 _.1 _.2)) (sym _.0 _.1 _.2))
                ((#t (_.0 _.1 _.2 _.3 _.4 _.5))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5))
                ((_.0 (_.0 _.1)) (sym _.0 _.1)) ; interesting
                ((#t (_.0 _.1 _.2 _.3 _.4 _.5 _.6))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6))
                ((#f (_.0 _.1 _.2 _.3)) (sym _.0 _.1 _.2 _.3))
                ((#t (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7))
                ((#t (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8))))

;;; this test seems to show a problem, as described in the previous test.
;;; (rep #t) shouldn't actually be a legal value.  Maybe this is illegal input.
;;; The real problem is that regex-matcho seems to not just accept this regex,
;;; but also to generate it.
;;;
;;; I think I know the problem.  We use the 'repo' constructor/simplifier to
;;; *construct* terms, but not to destruct terms.  Of course, with unification this
;;; distinction between constructing and desctructing is very slippery.  Is there
;;; any way to destruct using 'repo' (and similarly for 'seqo' and 'alto')?
;;; If that won't work, probably is necessary to add constraints when destructuring,
;;; to ensure illegal terms can't be instantiated when running backwards.
(check-expect (run 10 (q)
                (fresh (regex data)
                  (== '(rep #t) regex)
                  (=/= '() data)
                  (regex-matcho regex 
                                data
                                regex-NULL)
                  (== `(,regex ,data) q)))
              '((((rep #t) (_.0)) (sym _.0))
                (((rep #t) (_.0 _.1)) (sym _.0 _.1))
                (((rep #t) (_.0 _.1 _.2)) (sym _.0 _.1 _.2))
                (((rep #t) (_.0 _.1 _.2 _.3)) (sym _.0 _.1 _.2 _.3))
                (((rep #t) (_.0 _.1 _.2 _.3 _.4)) (sym _.0 _.1 _.2 _.3 _.4))
                (((rep #t) (_.0 _.1 _.2 _.3 _.4 _.5))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5))
                (((rep #t) (_.0 _.1 _.2 _.3 _.4 _.5 _.6))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6))
                (((rep #t) (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7))
                (((rep #t) (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8))
                (((rep #t) (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9))))

(check-expect (run* (q) (repo regex-BLANK q))
              `(,regex-BLANK))

;;; original tests

(check-expect (run* (q) (d/dco 'baz 'f q))
              `(,regex-NULL))

(check-expect (run* (q) (d/dco '(seq foo barn) 'foo q))
              '(barn))

(check-expect (run* (q) (d/dco '(alt (seq foo bar) (seq foo (rep baz))) 'foo q))
              '((alt bar (rep baz))))

(check-expect (run* (q) (regex-matcho '(seq foo (rep bar)) 
                                      '(foo bar bar bar)
                                      q))
              `(,regex-BLANK))

(check-expect (run* (q) (regex-matcho '(seq foo (rep bar)) 
                                      '(foo bar baz bar bar)
                                      q))
              `(,regex-NULL))

(check-expect (run* (q) (regex-matcho '(seq foo (rep (alt bar baz))) 
                                      '(foo bar baz bar bar)
                                      q))
              `(,regex-BLANK))
