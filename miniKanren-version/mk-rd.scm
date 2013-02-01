; William E. Byrd's miniKanren version of Matt Might's code for derivative
; parsing of regexp.

; Matt's original Scheme code can be found at
; http://matt.might.net/articles/implementation-of-regular-expression-matching-in-scheme-with-derivatives/

; This file requires core miniKanren (conde, ==, fresh) plus =/= and symbolo.

; In theory, tabling will allow this code to parse CFG's (or at least
; be something close to parsing CFG's).

(load "mk.scm")

; <regex> ::= #f                     ; Unmatchable pattern
;          |  #t                     ; Empty/blank pattern
;          |  '<symbol>              ; Symbol
;          |  (alt <regex> <regex>)  ; Alternation
;          |  (seq <regex> <regex>)  ; Sequence
;          |  (rep <regex>)          ; Repetition


;; Special regular expressions.
;;; Would these be better represented as symbols?
;;; Would probably make answers easier to read.
(define regex-NULL #f)    ; -- the empty set
(define regex-BLANK #t)   ; -- the empty string

;;; Important!
;;;
;;; (rep regex-NULL) and (rep regex-BLANK) both simplify to
;;; regex-BLANK. Since we want a canonical representation for each
;;; term, (rep regex-NULL) and (rep regex-BLANK) are not legal input
;;; expressions: regex-BLANK should be used instead.
;;;
;;; Similarly, seq and alt expressions can also be simplified.

;; Simplifying regex constructors.

(define (valid-seqo exp)
  (fresh (pat1 pat2)
    (== `(seq ,pat1 ,pat2) exp)
    (=/= regex-NULL pat1)
    (=/= regex-BLANK pat1)
    (=/= regex-NULL pat2)
    (=/= regex-BLANK pat2)))

(define (seqo pat1 pat2 out)
  (conde
    [(== regex-NULL pat1) (== regex-NULL out)]
    [(== regex-NULL pat2) (== regex-NULL out) (=/= regex-NULL pat1)]
    [(== regex-BLANK pat1) (== pat2 out) (=/= regex-NULL pat2)]
    [(== regex-BLANK pat2) (== pat1 out) (=/= regex-NULL pat1) (=/= regex-BLANK pat1)]
    [(=/= regex-NULL pat1) (=/= regex-BLANK pat1) (=/= regex-NULL pat2) (=/= regex-BLANK pat2) (== `(seq ,pat1 ,pat2) out)]))

(define (valid-alto exp)
  (fresh (pat1 pat2)
    (== `(alt ,pat1 ,pat2) exp)
    (=/= regex-NULL pat1)
    (=/= regex-NULL pat2)))

(define (alto pat1 pat2 out)
  (conde
    [(== regex-NULL pat1) (== pat2 out)]
    [(== regex-NULL pat2) (== pat1 out) (=/= regex-NULL pat1)]
    [(=/= regex-NULL pat1) (=/= regex-NULL pat2) (== `(alt ,pat1 ,pat2) out)]))

(define (valid-repo exp)
  (fresh (pat)
    (== `(rep ,pat) exp)
    (=/= regex-BLANK pat)
    (=/= regex-NULL pat)))

(define (repo pat out)
  (conde
    [(== regex-BLANK out)
     (conde
       [(== regex-NULL pat)]
       [(== regex-BLANK pat)])]
    [(=/= regex-NULL pat) (=/= regex-BLANK pat) (== `(rep ,pat) out)]))

;; Matching functions.

; deltao : regex boolean
; WEB: what about the case of alt--does it really return a boolean,
; or merely a value that can be interpreted as true or false?
(define (deltao re out)
  (conde
    [(== regex-BLANK re) (== regex-BLANK out)]
    [(== regex-NULL re) (== regex-NULL out)]
    [(symbolo re) (== regex-NULL out)]
    [(fresh (re1)
       (== `(rep ,re1) re)
       (valid-repo re)
       (== regex-BLANK out))]
    [(fresh (re1 re2 res1 res2)
       (== `(seq ,re1 ,re2) re)
       (valid-seqo re)
       (deltao re1 res1)
       (deltao re2 res2)
       (seqo res1 res2 out))]
    [(fresh (re1 re2 res1 res2)
       (== `(alt ,re1 ,re2) re)
       (valid-alto re)
       (deltao re1 res1)
       (deltao re2 res2)
       (alto res1 res2 out))]))

; regex-derivativeo : regex regex-atom regex
(define (regex-derivativeo re c out)
  (fresh ()
    (symbolo c)
    (conde
      [(== regex-BLANK re) (== regex-NULL out)]
      [(== regex-NULL re) (== regex-NULL out)]
      [(symbolo re)
       (conde
         [(== c re) (== regex-BLANK out)]
         [(=/= c re) (== regex-NULL out)])]
      [(fresh (re1 res1 res2)
         (== `(rep ,re1) re)
         (valid-repo re)                  
         (d/dco re1 c res1)
         (repo re1 res2)
         (seqo res1 res2 out))]
      [(fresh (re1 re2 res1 res2)
         (== `(alt ,re1 ,re2) re)
         (valid-alto re)
         (d/dco re1 c res1)
         (d/dco re2 c res2)
         (alto res1 res2 out))]
      [(fresh (re1 re2 res1 res2 res3 res4 res5)
; WEB: this is going to be trouble
         (== `(seq ,re1 ,re2) re)
         (valid-seqo re)
         (d/dco re1 c res1)
         (deltao re1 res3)
         (d/dco re2 c res4)
         (seqo res1 re2 res2)
         (seqo res3 res4 res5)
         (alto res2 res5 out))])))

; d/dco = regex-derivativeo
; WEB: what's the point of this???
; Especially since d/dco is called inside regex-derivativeo!
(define d/dco regex-derivativeo)

; regex-matcho : regex list boolean 
(define (regex-matcho pattern data out)
  (conde
    [(== '() data)
; WEB: I strongly suspect this can be simplified.  This is dependent
; upon deltao's output being a true boolean, though.
     (fresh (res)
       (conde
         [(== regex-BLANK out) (== regex-BLANK res)]
         [(== regex-NULL out) (=/= regex-BLANK res)])
       (deltao pattern res))]
    [(fresh (a d res)
       (== `(,a . ,d) data)
       (d/dco pattern a res)
       (regex-matcho res d out))]))

;; Tests.
(define (check-expect name check expect)
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
             (newline))))

;;; new tests

(check-expect "1"
              (run* (q) (repo regex-NULL q))
              `(,regex-BLANK))

(check-expect "2"
              (run* (q) (repo regex-BLANK q))
              `(,regex-BLANK))

(check-expect "3"
              (run* (q) (repo 'foo q))
              `((rep foo)))

(check-expect "4"
              (run* (q) (alto regex-NULL 'foo q))
              `(foo))

(check-expect "5"
              (run* (q) (alto 'foo regex-NULL q))
              `(foo))

(check-expect "6"
              (run* (q) (alto 'foo 'bar q))
              `((alt foo bar)))

(check-expect "7"
              (run* (q) (seqo regex-NULL 'foo q))
              `(,regex-NULL))

(check-expect "8"
              (run* (q) (seqo 'foo regex-NULL q))
              `(,regex-NULL))

(check-expect "9"
              (run* (q) (seqo regex-BLANK 'foo q))
              '(foo))

(check-expect "10"
              (run* (q) (seqo 'foo regex-BLANK q))
              '(foo))

(check-expect "11"
              (run* (q) (seqo 'foo 'bar q))
              '((seq foo bar)))

(check-expect "12"
              (run 10 (q)
                (fresh (re out)
                  (deltao re out)
                  (== `(,re ,out) q)))
              '((#t #t)
                (#f #f)
                ((_.0 #f) (sym _.0))
                (((rep _.0) #t) (=/= ((_.0 . #f)) ((_.0 . #t))))
                (((seq _.0 _.1) #f) (sym _.0 _.1))
                ((alt #t #t) (alt #t #t))
                (((alt #t _.0) #t) (sym _.0))
                (((alt _.0 #t) #t) (sym _.0))
                (((alt _.0 _.1) #f) (sym _.0 _.1))
                (((seq _.0 (rep _.1)) #f) (=/= ((_.1 . #f)) ((_.1 . #t))) (sym _.0))))

(check-expect "13"
              (run 5 (q)
                (fresh (re c out)
                  (regex-derivativeo re c out)
                  (== `(,re ,c ,out) q)))
              '(((#t _.0 #f) (sym _.0))
                ((#f _.0 #f) (sym _.0))
                ((_.0 _.0 #t) (sym _.0))
                ((_.0 _.1 #f) (=/= ((_.1 . _.0))) (sym _.0 _.1))
                (((rep _.0) _.0 (rep _.0)) (sym _.0))))

(check-expect "14"
              (run* (q) (regex-matcho '(seq foo (rep bar)) 
                                      '(foo bar bar bar)
                                      regex-BLANK))
              '(_.0))

(check-expect "15"
              (run* (q) (regex-matcho '(seq foo (rep bar)) 
                                      '(foo bar baz bar bar)
                                      regex-NULL))
              '(_.0))

(check-expect "16"
              (run* (q) (regex-matcho '(seq foo (rep (alt bar baz))) 
                                      '(foo bar baz bar bar)
                                      regex-BLANK))
              '(_.0))

;;; running backwards for real
;;; generate strings that match the pattern
;;; seems to get slow surprisingly fast.  probably a goal ordering issue
(check-expect "17"
              (run 6 (q) (regex-matcho '(seq foo (rep bar)) 
                                      q
                                      regex-BLANK))
              '((foo)
                (foo bar)
                (foo bar bar)
                (foo bar bar bar)
                (foo bar bar bar bar)
                (foo bar bar bar bar bar)))

;;; generate strings that *don't* match the pattern (!)
(check-expect "18"
              (run 15 (q) (regex-matcho '(seq foo (rep bar)) 
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
                ((_.0 _.1 _.2) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0 _.1 _.2))
                ((foo _.0 _.1 _.2) (=/= ((_.0 . bar))) (sym _.0 _.1 _.2))
                ((bar _.0 _.1 _.2) (sym _.0 _.1 _.2))
                ((foo bar _.0) (=/= ((_.0 . bar))) (sym _.0))
                ((_.0 _.1 _.2 _.3) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0 _.1 _.2 _.3))
                ((foo _.0 _.1 _.2 _.3) (=/= ((_.0 . bar))) (sym _.0 _.1 _.2 _.3))
                ((bar _.0 _.1 _.2 _.3) (sym _.0 _.1 _.2 _.3))))

;;; again, generate strings that *don't* match the pattern (!)
;;; this time, the output can be anything other than epsilon (as opposed to the empty set)
;;; Seems to generate the same answers as with the empty-set, which is good
;;; This distinction should disappear if regex-matcho can be simplified.
(check-expect "19"
              (run 15 (q)
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
                ((_.0 _.1 _.2) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0 _.1 _.2))
                ((foo _.0 _.1 _.2) (=/= ((_.0 . bar))) (sym _.0 _.1 _.2))
                ((bar _.0 _.1 _.2) (sym _.0 _.1 _.2))
                ((foo bar _.0) (=/= ((_.0 . bar))) (sym _.0))
                ((_.0 _.1 _.2 _.3) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0 _.1 _.2 _.3))
                ((foo _.0 _.1 _.2 _.3) (=/= ((_.0 . bar))) (sym _.0 _.1 _.2 _.3))
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
(check-expect "20"
              (run 30 (q) (regex-matcho q 
                                      '(foo bar bar bar)
                                      regex-BLANK))
              '((seq foo (rep bar)) ; jackpot!
                (rep (alt foo bar))
                (rep (alt bar foo)) ; equivalent to previous regex
                (rep (seq foo (rep bar)))
                (seq (rep foo) (rep bar))
                (rep (seq (rep foo) bar))
                (rep (rep (seq foo (rep bar))))
                (rep (alt bar (rep foo)))
                (seq foo (rep (alt #t bar)))
                (rep (alt (rep foo) bar))
                (alt #t (seq foo (rep bar)))
                (seq foo (alt #t (rep bar)))
                (rep (alt #t (alt foo bar)))
                (seq foo (rep (alt bar #t)))
                (alt #t (rep (alt foo bar)))
                (rep (alt foo (alt #t bar)))
                (seq foo (rep (alt foo bar)))
                (rep (alt #t (alt bar foo)))
                (alt #t (rep (alt bar foo)))
                (rep (alt bar (alt #t foo)))
                (rep (rep (rep (seq foo (rep bar)))))
                (seq foo (rep (alt bar foo)))
                (rep (seq foo (rep (alt #t bar))))
                (rep (alt foo (alt bar #t)))
                (seq foo (alt foo (rep bar)))
                (alt foo (seq foo (rep bar)))
                (rep (alt bar (alt foo #t)))
                (rep (alt bar (rep (rep foo))))
                (seq foo (seq bar (rep bar)))
                ((seq foo (rep (alt bar _.0))) (=/= ((_.0 . bar)) ((_.0 . foo))) (sym _.0))))

;;; look for the literal match regex
;;; easy version
(check-expect "21"
              (run 1 (q)
                (== `(seq foo (seq bar bar)) q)
                (regex-matcho q 
                              '(foo bar bar)
                              regex-BLANK))
              '((seq foo (seq bar bar))))

;;; look for the literal match regex
;;; hard version (generate and test)
(check-expect "22"
              (run 1 (q)
                (regex-matcho q 
                              '(foo bar bar)
                              regex-BLANK)
                (== `(seq foo (seq bar bar)) q))
              '((seq foo (seq bar bar))))

;;; look for the literal match regex (longer)
;;; easy version
(check-expect "23"
              (run 1 (q)
                (== `(seq foo (seq bar (seq bar bar))) q)
                (regex-matcho q 
                              '(foo bar bar bar)
                              regex-BLANK))
              '((seq foo (seq bar (seq bar bar)))))

;;; look for the literal match regex (longer)
;;; hard version (generate and test)
;;; this test doesn't seem to come back (at least not quickly)
#;(check-expect "24"
               (run 1 (q)
                (regex-matcho q 
                              '(foo bar bar bar)
                              regex-BLANK)
                (== `(seq foo (seq bar (seq bar bar))) q))
              '((seq foo (seq bar (seq bar bar)))))


;;; generate regex, and data that matches.
;;; interesting--the data is always null
(check-expect "25"
              (run 30 (q)
                (fresh (regex data)
                  (regex-matcho regex 
                                data
                                regex-BLANK)
                  (== `(,regex ,data) q)))
              '((#t ())
                (((rep _.0) ()) (=/= ((_.0 . #f)) ((_.0 . #t))))
                (((alt #t _.0) ()) (sym _.0))
                (((alt _.0 #t) ()) (sym _.0))
                ((_.0 (_.0)) (sym _.0))
                (((alt _.0 (rep _.1)) ()) (=/= ((_.1 . #f)) ((_.1 . #t))) (sym _.0))
                (((seq (rep _.0) (rep _.1)) ()) (=/= ((_.0 . #f)) ((_.0 . #t)) ((_.1 . #f)) ((_.1 . #t))))
                (((alt (rep _.0) _.1) ()) (=/= ((_.0 . #f)) ((_.0 . #t))) (sym _.1))
                (((alt #t (seq _.0 _.1)) ()) (sym _.0 _.1))
                (((alt #t (alt _.0 _.1)) ()) (sym _.0 _.1))
                (((alt #t (seq _.0 (rep _.1))) ()) (=/= ((_.1 . #f)) ((_.1 . #t))) (sym _.0))
                (((alt #t (seq (rep _.0) _.1)) ()) (=/= ((_.0 . #f)) ((_.0 . #t))) (sym _.1))
                (((seq (rep _.0) (alt #t _.1)) ()) (=/= ((_.0 . #f)) ((_.0 . #t))) (sym _.1))
                (((alt _.0 (alt #t _.1)) ()) (sym _.0 _.1))
                (((seq (rep _.0) (alt _.1 #t)) ()) (=/= ((_.0 . #f)) ((_.0 . #t))) (sym _.1))
                (((alt _.0 (alt _.1 #t)) ()) (sym _.0 _.1))
                (((alt (seq _.0 _.1) #t) ()) (sym _.0 _.1))
                (((alt (rep _.0) (seq _.1 _.2)) ()) (=/= ((_.0 . #f)) ((_.0 . #t))) (sym _.1 _.2))
                (((alt #t (seq _.0 (seq _.1 _.2))) ()) (sym _.0 _.1 _.2))
                (((alt #t (seq _.0 (alt #t #t))) ()) (sym _.0))
                (((alt (seq _.0 _.1) (rep _.2)) ()) (=/= ((_.2 . #f)) ((_.2 . #t))) (sym _.0 _.1))
                (((alt #t (seq _.0 (alt #t _.1))) ()) (sym _.0 _.1))
                (((alt #t (seq _.0 (alt _.1 #t))) ()) (sym _.0 _.1))
                (((seq (alt #t _.0) (rep _.1)) ()) (=/= ((_.1 . #f)) ((_.1 . #t))) (sym _.0))
                (((alt #t (seq (seq _.0 _.1) _.2)) ()) (sym _.0 _.1 _.2))
                (((seq (rep _.0) (alt _.1 (rep _.2))) ()) (=/= ((_.0 . #f)) ((_.0 . #t)) ((_.2 . #f)) ((_.2 . #t))) (sym _.1))
                (((seq (rep _.0) (seq (rep _.1) (rep _.2))) ()) (=/= ((_.0 . #f)) ((_.0 . #t)) ((_.1 . #f)) ((_.1 . #t)) ((_.2 . #f)) ((_.2 . #t))))
                (((alt (rep _.0) (alt _.1 _.2)) ()) (=/= ((_.0 . #f)) ((_.0 . #t))) (sym _.1 _.2))
                (((alt _.0 (alt _.1 (rep _.2))) ()) (=/= ((_.2 . #f)) ((_.2 . #t))) (sym _.0 _.1))
                (((alt _.0 (seq (rep _.1) (rep _.2))) ()) (=/= ((_.1 . #f)) ((_.1 . #t)) ((_.2 . #f)) ((_.2 . #t))) (sym _.0))))

;;; generate regex, and data that *doesn't* match.
(check-expect "26"
              (run 30 (q)
                (fresh (regex data)
                  (regex-matcho regex 
                                data
                                regex-NULL)
                  (== `(,regex ,data) q)))
              '((#f ())
                ((_.0 ()) (sym _.0))
                ((#t (_.0)) (sym _.0))
                (((seq _.0 _.1) ()) (sym _.0 _.1))
                ((alt #t #t) ())
                ((#f (_.0)) (sym _.0))
                (((alt _.0 _.1) ()) (sym _.0 _.1))
                (((seq _.0 (rep _.1)) ()) (=/= ((_.1 . #f)) ((_.1 . #t))) (sym _.0))
                ((#t (_.0 _.1)) (sym _.0 _.1))
                (((seq (rep _.0) _.1) ()) (=/= ((_.0 . #f)) ((_.0 . #t))) (sym _.1))
                (((alt #t (rep _.0)) ()) (=/= ((_.0 . #f)) ((_.0 . #t))))
                ((#t (_.0 _.1 _.2)) (sym _.0 _.1 _.2))
                (((alt (rep _.0) #t) ()) (=/= ((_.0 . #f)) ((_.0 . #t))))
                ((#f (_.0 _.1)) (sym _.0 _.1))
                (((seq _.0 (seq _.1 _.2)) ()) (sym _.0 _.1 _.2))
                ((#t (_.0 _.1 _.2 _.3)) (sym _.0 _.1 _.2 _.3))
                (((seq _.0 (alt #t #t)) ()) (sym _.0))
                ((alt #t (alt #t #t)) ())
                ((#t (_.0 _.1 _.2 _.3 _.4)) (sym _.0 _.1 _.2 _.3 _.4))
                (((seq _.0 (alt #t _.1)) ()) (sym _.0 _.1))
                (((alt #t (alt #t _.0)) ()) (sym _.0))
                ((_.0 (_.1)) (=/= ((_.1 . _.0))) (sym _.0 _.1))
                ((#f (_.0 _.1 _.2)) (sym _.0 _.1 _.2))
                (((seq _.0 (alt _.1 #t)) ()) (sym _.0 _.1))
                (((alt #t (alt _.0 #t)) ()) (sym _.0))
                ((#t (_.0 _.1 _.2 _.3 _.4 _.5)) (sym _.0 _.1 _.2 _.3 _.4 _.5))
                (((seq (seq _.0 _.1) _.2) ()) (sym _.0 _.1 _.2))
                ((_.0 (_.0 _.1)) (sym _.0 _.1))
                (((alt (rep _.0) (rep _.1)) ()) (=/= ((_.0 . #f)) ((_.0 . #t)) ((_.1 . #f)) ((_.1 . #t))))
                ((#t (_.0 _.1 _.2 _.3 _.4 _.5 _.6)) (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6))))

;;; generate regexs, and *non-empty* data, that match
;;; This seems slow to generate answers.  Even a run2 takes a while.
(check-expect "27"
              (run 2 (q)
                (fresh (regex data)
                  (=/= '() data) ; perhaps unifying data with a pair would be better style
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
;;; Actually, this behavior shouldn't be surprising:
;;; there are many, many more regexs that *don't* match than match.
;;; Same when generating strings.
;;;
;;; I'm nervous about having #f as the regex.  Is this really
;;; legit, from a type standpoint?
;;;
;;;
;;; longer runs (such as run 100) generate more interesting answers
;;;
;;; is there a way to avoid so many boring answers?
(check-expect "28"
              (run 15 (q)
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

(check-expect "29a"
              (run 10 (q)
                (fresh (regex data)
                  (== '(rep #t) regex)
                  (=/= '() data)
                  (regex-matcho regex 
                                data
                                regex-NULL)
                  (== `(,regex ,data) q)))
              '())

(check-expect "29b"
              (run 10 (q)
                (fresh (regex data out)
                  (== '(rep #t) regex)
                  (regex-matcho regex data out)))
              '())

(check-expect "29c"
              (run 10 (q)
                (fresh (regex data out)
                  (== '(rep #f) regex)
                  (regex-matcho regex data out)))
              '())

(check-expect "29d"
              (run 10 (q)
                (fresh (regex data out)
                  (== '(alt #f #f) regex)
                  (regex-matcho regex data out)))
              '())

(check-expect "29e"
              (run 10 (q)
                (fresh (regex data out)
                  (== '(seq #f #f) regex)
                  (regex-matcho regex data out)))
              '())

(check-expect "29f"
              (run 10 (q)
                (fresh (regex data out)
                  (== '(seq #t #t) regex)
                  (regex-matcho regex data out)))
              '())

(check-expect "29z"
              (run 10 (q)
                (fresh (regex data)
                  (== #t regex)
                  (=/= '() data)
                  (regex-matcho regex 
                                data
                                regex-NULL)
                  (== `(,regex ,data) q)))
              '(((#t (_.0)) (sym _.0))
                ((#t (_.0 _.1)) (sym _.0 _.1))
                ((#t (_.0 _.1 _.2)) (sym _.0 _.1 _.2))
                ((#t (_.0 _.1 _.2 _.3)) (sym _.0 _.1 _.2 _.3))
                ((#t (_.0 _.1 _.2 _.3 _.4)) (sym _.0 _.1 _.2 _.3 _.4))
                ((#t (_.0 _.1 _.2 _.3 _.4 _.5))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5))
                ((#t (_.0 _.1 _.2 _.3 _.4 _.5 _.6))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6))
                ((#t (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7))
                ((#t (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8))
                ((#t (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9))
                 (sym _.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9))))

(check-expect "30"
              (run* (q) (repo regex-BLANK q))
              `(,regex-BLANK))

;;; original tests

(check-expect "31"
              (run* (q) (d/dco 'baz 'f q))
              `(,regex-NULL))

(check-expect "32"
              (run* (q) (d/dco '(seq foo barn) 'foo q))
              '(barn))

(check-expect "33"
              (run* (q) (d/dco '(alt (seq foo bar) (seq foo (rep baz))) 'foo q))
              '((alt bar (rep baz))))

(check-expect "34"
              (run* (q) (regex-matcho '(seq foo (rep bar)) 
                                      '(foo bar bar bar)
                                      q))
              `(,regex-BLANK))

(check-expect "35"
              (run* (q) (regex-matcho '(seq foo (rep bar)) 
                                      '(foo bar baz bar bar)
                                      q))
              `(,regex-NULL))

(check-expect "36"
              (run* (q) (regex-matcho '(seq foo (rep (alt bar baz))) 
                                      '(foo bar baz bar bar)
                                      q))
              `(,regex-BLANK))
