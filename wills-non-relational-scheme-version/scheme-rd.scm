; William E. Byrd's Scheme version of Matt Might's code for derivative
; parsing of regexp.

(load "match.scm")

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
(define (seq pat1 pat2)
  (match `(,pat1 ,pat2)
    ((,pat1 ,pat2) (guard (and (not (eq? pat1 #f))
                               (not (eq? pat1 #t))
                               (not (eq? pat2 #f))
                               (not (eq? pat2 #t))))
     (list 'seq pat1 pat2))
    ((,pat1 #t) (guard (and (not (eq? pat1 #f))
                            (not (eq? pat1 #t))))
     pat1)
    ((#t ,pat2) (guard (not (eq? pat2 #f))) pat2)
    ((,pat1 #f) (guard (not (eq? pat1 #f))) regex-NULL)
    ((#f ,_) regex-NULL)))

(define (alt pat1 pat2)
  (match `(,pat1 ,pat2)
    ((,pat1 ,pat2) (guard (and (not (eq? pat1 #f))
                               (not (eq? pat2 #f))))
     (list 'alt pat1 pat2))
    ((,pat1 #f) (guard (not (eq? pat1 #f))) pat1)
    ((#f ,pat2) pat2)))

; WEB: should (rep regex-NULL) really become regex-BLANK?
; shouldn't it be regex-NULL instead?  Need to think about the types here.
(define (rep pat)
  (match pat
    (,pat (guard (and (not (eq? pat #f))
                      (not (eq? pat #t))))
          (list 'rep pat))
    (#f regex-BLANK)
    (#t regex-BLANK)))

;; Matching functions.

; delta : regex -> boolean
; WEB: what about the case of alt--does it really return a boolean,
; or merely a value that can be interpreted as true or false?
(define (delta re)
  (match re
    ((rep ,re) #t)
    ((alt ,re1 ,re2)
     (alt (delta re1) (delta re2)))
    ((seq ,re1 ,re22)
     (seq (delta re1) (delta re2)))
    (,re (guard (symbol? re)) #f)
    (#f #f)
    (#t #t)))

; regex-derivative : regex regex-atom -> regex
(define (regex-derivative re c)
  (and (symbol? c)
       (match re
         ((rep ,re)
          (seq (d/dc re c) (rep re)))
         ((alt ,re1 ,re2)
          (alt (d/dc re1 c) (d/dc re2 c)))
         ((seq ,re1 ,re2)
          (alt (seq (d/dc re1 c) re2)
               (seq (delta re1) (d/dc re2 c))))
         (,re (guard (symbol? re))
              (cond
                ((eq? c re) regex-BLANK)
                ((not (eq? c re)) regex-NULL)))
         (#t regex-NULL)
         (#f regex-NULL))))
                
; d/dc = regex-derivative
; WEB: what's the point of this???
; Especially since d/dc is called inside regex-derivative!
(define d/dc regex-derivative)

; regex-match : regex list -> boolean 
(define (regex-match pattern data)
  (match data
    ((,a . ,d) (regex-match (d/dc pattern a) d))
    (() (eq? (delta pattern) #t))))

;; Tests.
(define (check-expect check expect)
  (if (not (equal? check expect))
      (begin (display "check-expect failed; got: ")
             (display check)
             (display "; expected: ")
             (display expect)
             (newline))))
       
(check-expect (d/dc 'baz 'f)
              #f)

(check-expect (d/dc '(seq foo barn) 'foo)
              'barn)

(check-expect (d/dc '(alt (seq foo bar) (seq foo (rep baz))) 'foo)
              '(alt bar (rep baz)))

(check-expect (regex-match '(seq foo (rep bar)) 
                           '(foo bar bar bar))
              #t)

(check-expect (regex-match '(seq foo (rep bar)) 
                           '(foo bar baz bar bar))
              #f)

(check-expect (regex-match '(seq foo (rep (alt bar baz))) 
                           '(foo bar baz bar bar))
              #t)