; William E. Byrd's miniKanren version of (a subset) of Matt Might's code for
; a Scheme lexer, based on derivative parsing of regexp.

; Matt's original code can be found at
; http://matt.might.net/articles/nonblocking-lexing-toolkit-based-on-regex-derivatives/

; This file requires the miniKanren version of Matt Might's code for derivative
; parsing of regexp.

(load "mk-rd.scm")

;;; Regular language convenience operators

; Exactly n repetitions
; n must be a Peano numeral: z, (s z), (s (s z)), etc.
(define (n-repso n pat out)
  (fresh ()
    (conde
      [(== 'z n) (== regex-BLANK out)]
      [(fresh (n-1 res)
         (== `(s ,n-1) n)
         (n-repso n-1 pat res)
         (seqo pat res out))])))

; Kleene plus: one or more repetitions
; (not to be mistaken with the relational arithmetic pluso!)
(define (pluso pat out)
  (fresh (res)
    (repo pat res)
    (seqo pat res out)))

; Option: zero or one instances
(define (optiono pat out)
  (fresh ()
    (alto regex-BLANK pat out)))


;;; letters: a-d (to make the branching factor tolerable)
(define alphas '(alt
                  (alt a b)
                  (alt c d)))

;;; special characters: _, ?, #, and \ (to make the branching factor tolerable)
(define specials '(alt
                    (alt _ ?)
                    (alt hash slash)))

;;; whitespace: ' ' and '\n' (to make the branching factor tolerable)
(define white-space '(alt space newline))

(define parens '(alt left-paren right-paren))

; Match any character
; Here we represent characters as symbols.
;;; WEB: I don't think I can just use a fresh logic variable
;;; to represent AnyChar, for the same reason that _ is tricky in miniKanren.
;;; Basically, the question is how should this program behave:
;;;
;;; (run* (q)
;;;   (fresh (x out)
;;;     (any-charo x)
;;;     (repo x out)
;;;     (== `(,x ,out) q)))
;;;
;;; I assume the correct interpretation is [a-zA-Z0-0]*
;;; In other words, this regex should match 'abc', not just 'aaa'.
;;; Yet, the definition of any-charo below would only match 'aaa'.
;;;
;;; This feels like a scoping issue.  Could nominal logic resolve this problem?
;;;
;;;(define (any-charo x) (symbolo x))
(define any-char `(alt (alt ,alphas ,specials) (alt ,white-space ,parens)))

;;; Scheme lexer

; abbreviations

;;; Scheme literal character: #\\ ~ AnyChar
(define ch `(seq (seq hash slash) (seq slash ,alphas)))

;;; (simplified) Scheme identifier:
;;; (('a' thru 'd') ||
;;;  oneOf("_?%"))+
;;;
;;; The resulting regex is quite large.  Tempting to use a
;;; higher-order representation using a conde.  Not sure if this will
;;; run into the _-style problem described above.
(define id
  (let ((pat `(alt ,alphas ,specials)))
    `(seq ,pat (rep ,pat))))

;;; ** all of these character classes smell like constraints **

(define (appendo l s out)
  (conde
    [(== '() l) (== s out)]
    [(fresh (a d res)
       (== `(,a . ,d) l)
       (== `(,a . ,res) out)
       (appendo d s res))]))

;;; the main lexer loop
(define (maino chars tokens)
  (conde
    [(== '() chars) (== '() tokens)]
    [(fresh (a d pat prefix suffix tok res)
       (== `(,a . ,d) chars)
       (emito pat chars prefix suffix tok)
       (appendo tok res tokens)
       (maino suffix res))]))

;;; *** fascinating!  This appears, at first glance, to be a counter
;;; example to Will's Law: that simpler goals that have finitely many
;;; answers should come first in a conde.  However, Will's Law stil
;;; holds, since the paren cases can actually diverge.  Still, the
;;; useful ordering seems counter intuitive!
(define (emito pat chars prefix suffix tok)
  (fresh ()
    (conde
;;; I don't think I need the END pattern.
      [(== id pat) (== `((SymbolToken ,prefix)) tok)]
      [(== ch pat) (== `((CharToken ,prefix)) tok)]
      [(== white-space pat) (== '() tok)]
      [(== 'left-paren pat) (== '((PuncToken left-paren)) tok)]
      [(== 'right-paren pat) (== '((PuncToken right-paren)) tok)])
    (regex-matcho pat prefix #t)
    (appendo prefix suffix chars)))

;;; tests

(check-expect "n-repso-1"
              (run 10 (q)
                (fresh (n pat out)
                  (n-repso n pat out)
                  (== `(,n ,pat ,out) q)))
              '((z _.0 #t) ; is this true, even if _.0 is #f?
                ((s z) #f #f)
                ((s z) #t #t)
                (((s z) _.0 _.0) (=/= ((_.0 . #f)) ((_.0 . #t))))
                ((s (s z)) #f #f)
                ((s (s z)) #t #t)
                (((s (s z)) _.0 (seq _.0 _.0)) (=/= ((_.0 . #f)) ((_.0 . #t))))
                ((s (s (s z))) #f #f)
                ((s (s (s z))) #t #t)
                (((s (s (s z))) _.0 (seq _.0 (seq _.0 _.0))) (=/= ((_.0 . #f)) ((_.0 . #t))))))

(check-expect "pluso-1"
              (run* (q)
                (fresh (pat out)
                  (pluso pat out)
                  (== `(,pat ,out) q)))
              '((#f #f)
                ((_.0 (seq _.0 (rep _.0))) (sym _.0))
                (#t #t)
                ((rep _.0) (seq (rep _.0) (rep _.0)))
                ((seq _.0 _.1) (seq (seq _.0 _.1) (rep (seq _.0 _.1))))
                ((alt _.0 _.1) (seq (alt _.0 _.1) (rep (alt _.0 _.1))))))

(check-expect "optiono-1"
              (run* (q)
                (fresh (pat out)
                  (optiono pat out)
                  (== `(,pat ,out) q)))
              '((#t #t)
                (#f #t)
                ((_.0 (alt #t _.0)) (=/= ((_.0 . #f)) ((_.0 . #t))))))

; run 5 appears to diverge
(check-expect "alphas-1"
              (run 4 (q)
                (regex-matcho alphas q regex-BLANK))
              '((a) (b) (c) (d)))

(check-expect "specials-1"
              (run 4 (q)
                (regex-matcho specials q regex-BLANK))
              '((_) (?) (hash) (slash)))

(check-expect "white-space-1"
              (run 2 (q)
                (regex-matcho white-space q regex-BLANK))
              '((space) (newline)))

(check-expect "parens-1"
              (run 2 (q)
                (regex-matcho parens q regex-BLANK))
              '((left-paren) (right-paren)))

(check-expect "any-char-1"
              (run 5 (q)
                (regex-matcho any-char q regex-BLANK))
              '((a) (b) (c) (d) (_)))

(check-expect "ch-1"
              (run 4 (q)
                (regex-matcho ch q regex-BLANK))
              '((hash slash slash a)
                (hash slash slash b)
                (hash slash slash c)
                (hash slash slash d)))

(check-expect "id-1"
              (run 20 (q)
                (regex-matcho id q regex-BLANK))
              '((a)
                (b)
                (a a)
                (a b)
                (c)
                (b a)
                (a a a)
                (a c)
                (b b)
                (a a b)
                (d)
                (a d)
                (c a)
                (b a a)
                (a a a a)
                (b c)
                (a a c)
                (a _)
                (a b a)
                (c b)))

(check-expect "rep-any-char-1"
              (run 10 (q)
                (regex-matcho `(rep ,any-char) q regex-BLANK))
              '(() (a) (b) (a a) (c) (a b) (b a) (d) (a a a) (a c)))

(check-expect "pluso-any-char-1"
              (run 10 (q)
                (fresh (pat)
                  (pluso any-char pat)
                  (regex-matcho pat q regex-BLANK)))
              '((a) (b) (a a) (a b) (c) (b a) (a a a) (a c) (b b) (a a b)))

(check-expect "appemdo-1"
              (run* (q)
                (appendo '(a b c) '(d e) q))
              '((a b c d e)))

(check-expect "emito-1"
              (run 10 (q)
                (fresh (pat chars prefix suffix tok)
                  (emito pat chars prefix suffix tok)
                  (== `(,pat ,chars ,prefix ,suffix ,tok) q)))
              '((left-paren
                 (left-paren . _.0)
                 (left-paren)
                 _.0
                 ((PuncToken left-paren)))
                (right-paren
                 (right-paren . _.0)
                 (right-paren)
                 _.0
                 ((PuncToken right-paren)))
                ((alt space newline) (space . _.0) (space) _.0 ())
                ((alt space newline) (newline . _.0) (newline) _.0 ())
                ((seq (alt (alt (alt a b) (alt c d))
                           (alt (alt _ ?) (alt hash slash)))
                      (rep (alt (alt (alt a b) (alt c d))
                                (alt (alt _ ?) (alt hash slash)))))
                 (a . _.0)
                 (a)
                 _.0
                 ((SymbolToken (a))))
                ((seq (alt (alt (alt a b) (alt c d))
                           (alt (alt _ ?) (alt hash slash)))
                      (rep (alt (alt (alt a b) (alt c d))
                                (alt (alt _ ?) (alt hash slash)))))
                 (b . _.0)
                 (b)
                 _.0
                 ((SymbolToken (b))))
                ((seq (alt (alt (alt a b) (alt c d))
                           (alt (alt _ ?) (alt hash slash)))
                      (rep (alt (alt (alt a b) (alt c d))
                                (alt (alt _ ?) (alt hash slash)))))
                 (a a . _.0)
                 (a a)
                 _.0
                 ((SymbolToken (a a))))
                ((seq (seq hash slash)
                      (seq slash (alt (alt a b) (alt c d))))
                 (hash slash slash a . _.0) ; !!!!!! WTF!?  sweet
                 (hash slash slash a)
                 _.0
                 ((CharToken (hash slash slash a))))
                ((seq (alt (alt (alt a b) (alt c d))
                           (alt (alt _ ?) (alt hash slash)))
                      (rep (alt (alt (alt a b) (alt c d))
                                (alt (alt _ ?) (alt hash slash)))))
                 (a b . _.0)
                 (a b)
                 _.0
                 ((SymbolToken (a b))))
                ((seq (alt (alt (alt a b) (alt c d))
                           (alt (alt _ ?) (alt hash slash)))
                      (rep (alt (alt (alt a b) (alt c d))
                                (alt (alt _ ?) (alt hash slash)))))
                 (c . _.0)
                 (c)
                 _.0
                 ((SymbolToken (c))))))

(check-expect "maino-1"
              (run 50 (q)
                (fresh (chars tokens)
                  (maino chars tokens)
                  (== `(,chars ,tokens) q)))
              '((() ())
                ((left-paren) ((PuncToken left-paren)))
                ((right-paren) ((PuncToken right-paren)))
                ((space) ())
                ((left-paren left-paren)
                 ((PuncToken left-paren) (PuncToken left-paren)))
                ((left-paren right-paren)
                 ((PuncToken left-paren) (PuncToken right-paren)))
                ((right-paren left-paren)
                 ((PuncToken right-paren) (PuncToken left-paren)))
                ((right-paren right-paren)
                 ((PuncToken right-paren) (PuncToken right-paren)))
                ((left-paren space) ((PuncToken left-paren)))
                ((left-paren left-paren left-paren)
                 ((PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)))
                ((newline) ())
                ((left-paren left-paren right-paren)
                 ((PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken right-paren)))
                ((space left-paren) ((PuncToken left-paren)))
                ((left-paren right-paren left-paren)
                 ((PuncToken left-paren)
                  (PuncToken right-paren)
                  (PuncToken left-paren)))
                ((space right-paren) ((PuncToken right-paren)))
                ((left-paren right-paren right-paren)
                 ((PuncToken left-paren)
                  (PuncToken right-paren)
                  (PuncToken right-paren)))
                ((right-paren space) ((PuncToken right-paren)))
                ((right-paren left-paren left-paren)
                 ((PuncToken right-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)))
                ((right-paren left-paren right-paren)
                 ((PuncToken right-paren)
                  (PuncToken left-paren)
                  (PuncToken right-paren)))
                ((left-paren left-paren space)
                 ((PuncToken left-paren) (PuncToken left-paren)))
                ((left-paren left-paren left-paren left-paren)
                 ((PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)))
                ((left-paren newline) ((PuncToken left-paren)))
                ((left-paren left-paren left-paren right-paren)
                 ((PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken right-paren)))
                ((right-paren right-paren left-paren)
                 ((PuncToken right-paren)
                  (PuncToken right-paren)
                  (PuncToken left-paren)))
                ((left-paren space left-paren)
                 ((PuncToken left-paren) (PuncToken left-paren)))
                ((newline left-paren) ((PuncToken left-paren)))
                ((right-paren right-paren right-paren)
                 ((PuncToken right-paren)
                  (PuncToken right-paren)
                  (PuncToken right-paren)))
                ((left-paren left-paren right-paren left-paren)
                 ((PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken right-paren)
                  (PuncToken left-paren)))
                ((left-paren space right-paren)
                 ((PuncToken left-paren) (PuncToken right-paren)))
                ((newline right-paren) ((PuncToken right-paren)))
                ((left-paren left-paren right-paren right-paren)
                 ((PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken right-paren)
                  (PuncToken right-paren)))
                ((space space) ())
                ((left-paren right-paren space)
                 ((PuncToken left-paren) (PuncToken right-paren)))
                ((space left-paren left-paren)
                 ((PuncToken left-paren) (PuncToken left-paren)))
                ((left-paren right-paren left-paren left-paren)
                 ((PuncToken left-paren)
                  (PuncToken right-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)))
                ((right-paren left-paren space)
                 ((PuncToken right-paren) (PuncToken left-paren)))
                ((space left-paren right-paren)
                 ((PuncToken left-paren) (PuncToken right-paren)))
                ((left-paren right-paren left-paren right-paren)
                 ((PuncToken left-paren)
                  (PuncToken right-paren)
                  (PuncToken left-paren)
                  (PuncToken right-paren)))
                ((right-paren left-paren left-paren left-paren)
                 ((PuncToken right-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)))
                ((left-paren left-paren left-paren space)
                 ((PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)))
                ((right-paren newline) ((PuncToken right-paren)))
                ((right-paren left-paren left-paren right-paren)
                 ((PuncToken right-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken right-paren)))
                ((left-paren left-paren left-paren left-paren left-paren)
                 ((PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)))
                ((left-paren left-paren newline)
                 ((PuncToken left-paren) (PuncToken left-paren)))
                ((left-paren left-paren left-paren left-paren right-paren)
                 ((PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken right-paren)))
                ((space right-paren left-paren)
                 ((PuncToken right-paren) (PuncToken left-paren)))
                ((left-paren right-paren right-paren left-paren)
                 ((PuncToken left-paren)
                  (PuncToken right-paren)
                  (PuncToken right-paren)
                  (PuncToken left-paren)))
                ((right-paren space left-paren)
                 ((PuncToken right-paren) (PuncToken left-paren)))
                ((right-paren left-paren right-paren left-paren)
                 ((PuncToken right-paren)
                  (PuncToken left-paren)
                  (PuncToken right-paren)
                  (PuncToken left-paren)))
                ((left-paren left-paren space left-paren)
                 ((PuncToken left-paren)
                  (PuncToken left-paren)
                  (PuncToken left-paren)))))

(check-expect "maino-2"
              (run 9 (q)
                (fresh (chars tokens x y z* rest)
                  (maino chars tokens)
                  (== `((SymbolToken (,x ,y . ,z*)) . ,rest) tokens)
                  (== `(,chars ,tokens) q)))
              '(((a a) ((SymbolToken (a a))))
                ((a a left-paren)
                 ((SymbolToken (a a)) (PuncToken left-paren)))
                ((a a right-paren)
                 ((SymbolToken (a a)) (PuncToken right-paren)))
                ((a a space) ((SymbolToken (a a))))
                ((a a left-paren left-paren)
                 ((SymbolToken (a a))
                  (PuncToken left-paren)
                  (PuncToken left-paren)))
                ((a a left-paren right-paren)
                 ((SymbolToken (a a))
                  (PuncToken left-paren)
                  (PuncToken right-paren)))
                ((a a right-paren left-paren)
                 ((SymbolToken (a a))
                  (PuncToken right-paren)
                  (PuncToken left-paren)))
                ((a a right-paren right-paren)
                 ((SymbolToken (a a))
                  (PuncToken right-paren)
                  (PuncToken right-paren)))
                ((a a left-paren space)
                 ((SymbolToken (a a)) (PuncToken left-paren)))))

(check-expect "maino-3"
              (run 1 (q)
                (maino '(left-paren a b right-paren) q))
              '(((PuncToken left-paren)
                 (SymbolToken (a))
                 (SymbolToken (b))
                 (PuncToken right-paren))))

;; this takes too long to run
;(check-expect "maino-4"
;              (run 1 (q)
;                (maino '(left-paren a b c c a space c a space right-paren) q))
;              '???)

(check-expect "maino-5"
              (run 1 (q)
                (maino q '((PuncToken left-paren))))
              '((left-paren)))

(check-expect "maino-6"
              (run 1 (q)
                (maino q '((PuncToken left-paren)
                           (SymbolToken (a)))))
              '((left-paren a)))

;;; too slow to run
;(check-expect "maino-9"
;              (run 1 (q)
;                (maino q '((PuncToken left-paren)
;                           (SymbolToken (a))
;                           (SymbolToken (b)))))
;              '???)

;;; too slow
;(check-expect "maino-10"
;              (run 1 (q)
;                (maino q '((PuncToken left-paren)
;                           (SymbolToken (a))
;                           (SymbolToken (b))
;                           (PuncToken right-paren))))
;              '???)
