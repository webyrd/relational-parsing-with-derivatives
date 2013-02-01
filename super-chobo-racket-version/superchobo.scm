#lang racket

; super chobo Racket version.  Somepony please fix!  (see README file)

; Racket compatibility
(define (remp p ls)
  (cond
    ((null? ls) '())
    ((p (car ls)) (remp p (cdr ls)))
    (else (cons (car ls) (remp p (cdr ls))))))

(define (exists p ls)
  (cond
    ((null? ls) #f)
    ((p (car ls)) #t)
    (else (exists p (cdr ls)))))

(define (my-sort comp ls)
  (sort ls comp))

(define datum->string
  (lambda (x)
    (with-output-to-string
      (lambda () (display x)))))



;;; miniKanren with =/=, symbolo, numbero, and noo (A new goal) (noo
;;; 'clasure x).  not-in is gone; there are fewer uses of 'sym; and
;;; no uses of 'num (except when creating numbero.)

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

(define a->s (lambda (a) (car a)))
(define a->c* (lambda (a) (cadr a)))
(define a->t (lambda (a) (caddr a)))

(define-syntax lambdag@
  (syntax-rules (:)
    ((_ (a) e) (lambda (a) e))
    ((_ (a : s c* t) e)
     (lambda (a)
       (let ((s (a->s a)) (c* (a->c* a)) (t (a->t a)))
         e)))))

(define mzero (lambda () #f))
(define unit (lambdag@ (a) a))
(define choice (lambda (a f) (cons a f)))
(define-syntax lambdaf@ 
  (syntax-rules () ((_ () e) (lambda () e))))

(define-syntax inc
  (syntax-rules () ((_ e) (lambdaf@ () e))))

(define empty-f (lambdaf@ () (mzero)))

(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((a^) e2) ((a f) e3))
     (let ((a-inf e))
       (cond
         ((not a-inf) e0)
         ((procedure? a-inf)  (let ((f^ a-inf)) e1))
         ((not (and (pair? a-inf)
                 (procedure? (cdr a-inf))))
          (let ((a^ a-inf)) e2))
         (else (let ((a (car a-inf)) (f (cdr a-inf))) 
                 e3)))))))
(define take
  (lambda (n f)
    (cond
      ((and n (zero? n)) '())
      (else
       (case-inf (f)
         (() '())
         ((f) (take n f))
         ((a) (cons a '()))
         ((a f) (cons a (take (and n (- n 1)) f))))))))

(define empty-a '(() () ()))
  
(define-syntax run
  (syntax-rules ()
    ((_ n (x) g0 g ...)
     (take n
       (lambdaf@ ()
         ((fresh (x) g0 g ...
            (lambdag@ (final-a)
              (choice ((reify x) final-a) empty-f)))
          empty-a))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (x) g ...) (run #f (x) g ...))))

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (a)
       (inc
         (let ((x (var 'x)) ...)
           (bind* (g0 a) g ...)))))))

(define-syntax bind*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g ...) (bind* (bind e g0) g ...))))

(define bind
  (lambda (a-inf g)
    (case-inf a-inf
      (() (mzero))
      ((f) (inc (bind (f) g)))
      ((a) (g a))
      ((a f) (mplus (g a) (lambdaf@ () (bind (f) g)))))))

(define mplus
  (lambda (a-inf f)
    (case-inf a-inf
      (() (f))
      ((f^) (inc (mplus (f) f^)))
      ((a) (choice a f))
      ((a f^) (choice a (lambdaf@ () (mplus (f) f^)))))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (a) 
       (inc 
         (mplus* 
           (bind* (g0 a) g ...)
           (bind* (g1 a) g^ ...) ...))))))

(define-syntax mplus*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...) (mplus e0 
                    (lambdaf@ () (mplus* e ...))))))

(define pr-t->tag
  (lambda (pr-t)
    (car (rhs pr-t))))

(define pr-t->pred
  (lambda (pr-t)
    (cdr (rhs pr-t))))

(define noo
  (lambda (tag u)
    (let ((pred (lambda (x) (not (eq? x tag)))))
      (lambdag@ (a : s c* t)
        (noo-aux tag u pred a s c* t)))))

(define noo-aux
  (lambda (tag u pred a s c* t)
    (let ((u (if (var? u) (walk u s) u)))
      (cond
        ((pair? u)
         (cond
           ((pred u)
            (let ((a (noo-aux tag (car u) pred a s c* t)))
              (and a
                ((lambdag@ (a : s c* t)
                   (noo-aux tag (cdr u) pred a s c* t))
                 a))))
           (else (mzero))))
        ((not (var? u))
         (cond
           ((pred u) (unit a))
           (else (mzero))))
        ((ext-t u tag pred s t) =>
         (lambda (t0)
           (cond
             ((not (eq? t0 t))
              (let ((t^ (list (car t0))))
                (let ((c* (subsume t^ c*)))
                  (unit (subsume-t s c* t0)))))
             (else (unit a)))))
        (else (mzero))))))

(define make-flat-tag
  (lambda (tag pred)
    (lambda (u)
      (lambdag@ (a : s c* t)
        (let ((u (if (var? u) (walk u s) u)))
          (cond
            ((not (var? u))
             (cond
               ((pred u) (unit a))
               (else (mzero))))
            ((ext-t u tag pred s t) =>
             (lambda (t0)
               (cond
                 ((not (eq? t0 t))
                  (let ((t^ (list (car t0))))
                    (let ((c* (subsume t^ c*)))
                      (unit (subsume-t s c* t0)))))
                 (else (unit a)))))
            (else (mzero))))))))

(define deep-tag?
  (lambda (tag)
    (not (or (eq? tag 'sym) (eq? tag 'num)))))

;;; We can extend t with a deep tag provided
;;; It is not in a singleton c of c* with the same
;;; tag.  That would mean lifting an innocent
;;; constraint to an overarching constraint,
;;; would be wrong.  So, no change to c* or t.
;;; in that case.

(define ext-t
  (lambda (x tag pred s t^)
    (let ((x (walk x s)))
      (let loop ((t t^))
        (cond
          ((null? t) (cons `(,x . (,tag . ,pred)) t^))
          ((not (eq? (walk (lhs (car t)) s) x)) (loop (cdr t)))
          ((eq? (pr-t->tag  (car t)) tag) t^)
          ((works-together? (pr-t->tag (car t)) tag)
           (loop (cdr t)))
          (else #f))))))

(define works-together?
  (lambda (t1 t2)
    (or (deep-tag? t1) (deep-tag? t2))))

(define subsume-t
  (lambda (s c* t)
    (let loop
      ((x* (rem-dups (map lhs t)))
       (c* c*)
       (t t))
      (cond
        ((null? x*) `(,s ,c* ,t))
        (else
         (let ((c*/t (subsume-c*/t (car x*) s c* t)))
           (loop (cdr x*) (car c*/t) (cdr c*/t))))))))

(define rem-dups
  (lambda (vars)
    (cond
      ((null? vars) '())
      ((memq (car vars) (cdr vars))
       (rem-dups (cdr vars)))
      (else (cons (car vars) (rem-dups (cdr vars)))))))

(define have-flat-tag?
  (lambda (pred x)
    (lambda (pr-t)
      (let ((tag (pr-t->tag pr-t)))
        (and
         (not (deep-tag? tag))
         (eq? (lhs pr-t) x)
         (pred tag))))))

(define subsume-c*/t
  (lambda (x s c* t)
    (cond
      ((exists (have-flat-tag? (lambda (u) (eq? u 'sym)) x) t)
       (subsumed-from-t-to-c* x s c* t '()))
      ((exists (have-flat-tag? (lambda (u) (not (eq? u 'sym))) x) t)
       `(,c* . ,(drop-from-t x t)))
      (else `(,c* . ,t)))))

(define drop-from-t
  (lambda (x t)
    (remp (lambda (pr-t)
            (and
              (eq? (lhs pr-t) x)
              (deep-tag? (pr-t->tag pr-t))))
      t)))

(define subsumed-from-t-to-c*
  (lambda (x s c* t t^)
    (cond
      ((null? t) `(,c* . ,t^))
      (else
       (let ((pr-t (car t)))
         (let ((tag (pr-t->tag pr-t))
               (y (lhs pr-t)))
           (cond
             ((and (eq? y x) (deep-tag? tag))
              (subsumed-from-t-to-c* x s
                (new-c* x tag c* s)
                (cdr t)
                t^))
             (else
              (subsumed-from-t-to-c* x s
                c*
                (cdr t)
                (cons (car t) t^))))))))))

(define new-c*
  (lambda (x tag c* s)
    (cond
      ((exists
         (lambda (c)
           (and (null? (cdr c))
             (eq? (walk (lhs (car c)) s) x)
             (eq? (rhs (car c)) tag)))
         c*)
       c*)
      (else (cons `((,x . ,tag)) c*)))))

;;; End reading here.

(define subsume
  (lambda (t c*)
    (remp (lambda (c)
            (exists (subsumed-pr? t) c))
      c*)))
 
(define subsumed-pr?
  (lambda (t)
    (lambda (pr-c)
      (let ((u (rhs pr-c)))
        (and (not (var? u))
          (let ((x (lhs pr-c)))
            (let ((pr-t (assq x t)))
              (and pr-t
                (let ((tag (pr-t->tag pr-t)))
                  (cond
                    ((and (deep-tag? tag) (eq? tag u)))
                    ((not ((pr-t->pred pr-t) u)))
                    (else #f)))))))))))

(define booleano
  (lambda (x)
    (conde
      ((== #f x))
      ((== #t x)))))

(define symbolo (make-flat-tag 'sym symbol?))

(define numbero (make-flat-tag 'num number?))

(define =/=
  (lambda (u v)
    (lambdag@ (a : s c* t)
      (cond
        ((unify u v s) =>
         (lambda (s0)
           (cond
             ((eq? s0 s) (mzero))
             (else
              (let ((p* (list (prefix-s s0 s))))
                (let ((p* (subsume t p*)))
                  (let ((c* (append p* c*)))
                    (unit `(,s ,c* ,t)))))))))
        (else (unit a))))))

(define prefix-s
  (lambda (s0 s)
    (cond
      ((eq? s0 s) '())
      (else (cons (car s0)
              (prefix-s (cdr s0) s))))))

(define ==
  (lambda (u v)
    (lambdag@ (a : s c* t)
      (cond
        ((unify u v s) =>
         (lambda (s0)
           (cond
             ((eq? s0 s) (unit a))
             ((verify-c* c* s0) =>
              (lambda (c*)
                (cond
                  ((verify-t t s0) =>
                   (lambda (t)
                     (let ((c* (subsume t c*)))
                       (unit (subsume-t s0 c* t)))))
                  (else (mzero)))))
             (else (mzero)))))
        (else (mzero))))))
 
(define verify-c*
  (lambda (c* s)
    (cond
      ((null? c*) '())
      ((verify-c* (cdr c*) s) =>
       (lambda (c0*)
         (let ((c (car c*)))
           (cond
             ((verify-c*-aux c c0* s))
             (else (mzero))))))
      (else #f))))

(define verify-c*-aux
  (lambda (c c0* s)
    (cond
      ((unify* c s) =>
       (lambda (s0)
         (and (not (eq? s0 s))
           (cons (prefix-s s0 s) c0*))))
      (else c0*))))

(define verify-t
  (lambda (t s)
    (cond
      ((null? t) '())
      ((verify-t (cdr t) s) =>
       (letrec ((rec
         (lambda (u)
           (let ((u (if (var? u) (walk u s) u)))
             (let ((tag (pr-t->tag (car t)))
                   (pred (pr-t->pred (car t))))
               (lambda (t0)
                 (cond
                   ((var? u)
                    (ext-t u tag pred s t0))
                   ((pair? u)
                    (if (deep-tag? tag)
                      (cond
                        (((rec (car u)) t0) =>
                         (rec (cdr u)))
                        (else #f))
                      (and (pred u) t0)))
                   (else (and (pred u) t0)))))))))
         (rec (lhs (car t)))))
      (else #f))))

(define succeed (== #f #f))

(define fail (== #f #t))

(define var (lambda (dummy) (vector dummy)))
(define var? (lambda (x) (vector? x)))
(define lhs (lambda (pr) (car pr)))
(define rhs (lambda (pr) (cdr pr)))

(define walk
  (lambda (x s)
    (let ((a (assq x s)))
      (cond
        (a (let ((u (rhs a)))
             (if (var? u) (walk u s) u)))
        (else x)))))

(define walk*
  (lambda (v s)
    (let ((v (if (var? v) (walk v s) v)))
      (cond
        ((var? v) v)
        ((pair? v)
         (cons (walk* (car v) s) (walk* (cdr v) s)))
        (else v)))))

(define unify
  (lambda (u v s)
    (let ((u (if (var? u) (walk u s) u))
          (v (if (var? v) (walk v s) v)))
      (cond
        ((and (pair? u) (pair? v))
         (let ((s (unify (car u) (car v) s)))
           (and s
             (unify (cdr u) (cdr v) s))))
        (else (unify-nonpair u v s))))))

(define unify-nonpair
  (lambda (u v s)
    (cond
      ((eq? u v) s)      
      ((var? u)
       (and (or (not (pair? v)) (valid? u v s))
         (cons `(,u . ,v) s)))
      ((var? v)
       (and (or (not (pair? u)) (valid? v u s))
         (cons `(,v . ,u) s)))
      ((equal? u v) s)
      (else #f))))

(define valid?
  (lambda (x v s)
    (not (occurs-check x v s))))

(define occurs-check
  (lambda (x v s)
    (let ((v (if (var? v) (walk v s) v)))
      (cond
        ((var? v) (eq? v x))
        ((pair? v) 
         (or (occurs-check x (car v) s)
             (occurs-check x (cdr v) s)))
        (else #f)))))  

(define reify-s
  (lambda (v)
    (let reify-s ((v v) (r '()))
      (let ((v (if (var? v) (walk v r) v)))
        (cond
          ((var? v)
           (let ((n (length r)))
             (let ((name (reify-name n)))
               (cons `(,v . ,name) r))))
          ((pair? v)
           (let ((r (reify-s (car v) r)))
             (reify-s (cdr v) r)))
          (else r))))))

(define reify-name
  (lambda (n)
    (string->symbol
      (string-append "_" "." (number->string n)))))

(define reify
  (lambda (x)
    (lambdag@ (a : s c* t)
      (let ((v (walk* x s)))
        (let ((r (reify-s v)))
          (reify-aux r v
            (let ((c* (remp
                        (lambda (c)
                          (anyvar? c r))
                        c*)))
              (rem-subsumed c*))        
            (remp
              (lambda (pr)
                (var? (walk (lhs pr) r)))
              t)))))))

(define reify-aux
  (lambda (r v c* t)
    (let ((v (walk* v r))
          (c* (walk* c* r))
          (t (walk* t r)))
      (let ((c* (sorter (map sorter c*)))
            (p* (sorter
                  (map sort-t-vars
                    (partition* t)))))
        (cond
          ((and (null? c*) (null? p*)) v)
          ((null? c*) `(,v . ,p*))
          (else `(,v (=/= . ,c*) . ,p*)))))))

(define sorter
  (lambda (ls)
    (my-sort lex<=? ls)))
 
(define sort-t-vars
  (lambda (pr-t)
    (let ((tag (car pr-t))
          (x* (sorter (cdr pr-t))))
      (let ((reified-tag (tag->reified-tag tag)))
        `(,reified-tag . ,x*)))))

(define tag->reified-tag
  (lambda (tag)
    (if (deep-tag? tag)
      (string->symbol
        (string-append "no-"
          (symbol->string tag)))
      tag)))

(define lex<=?
  (lambda (x y)
    (string<=? (datum->string x) (datum->string y))))
  
(define anyvar?
  (lambda (c r)
    (cond
      ((pair? c)
       (or (anyvar? (car c) r)
           (anyvar? (cdr c) r)))
      (else (and (var? c) (var? (walk c r)))))))

(define rem-subsumed
  (lambda (c*)
    (let rem-subsumed ((c* c*) (c^* '()))
      (cond
        ((null? c*) c^*)
        ((or (subsumed? (car c*) (cdr c*))
             (subsumed? (car c*) c^*))
         (rem-subsumed (cdr c*) c^*))
        (else (rem-subsumed (cdr c*)
                (cons (car c*) c^*)))))))

(define unify*
  (lambda (c s)
    (unify (map lhs c) (map rhs c) s)))
 
(define subsumed?
  (lambda (c c*)
    (cond
      ((null? c*) #f)
      (else
        (let ((c^ (unify* (car c*) c)))
          (or
            (and c^ (eq? c^ c))
            (subsumed? c (cdr c*))))))))

(define part
  (lambda (tag t x* y*)
    (cond
     ((null? t)
      (cons `(,tag . ,x*) (partition* y*)))
     ((eq? (pr-t->tag (car t)) tag)
      (let ((x (lhs (car t))))
        (let ((x* (cond
                    ((memq x x*) x*)
                    (else (cons x x*)))))
          (part tag (cdr t) x* y*))))
     (else
      (let ((y* (cons (car t) y*)))
        (part tag (cdr t) x* y*))))))

(define partition*
  (lambda (t)
    (cond
      ((null? t) '())
      (else
       (part (pr-t->tag (car t)) t '() '())))))

(define-syntax project 
  (syntax-rules ()
    ((_ (x ...) g g* ...)  
     (lambdag@ (a : s c* t)
       (let ((x (walk* x s)) ...)
         ((fresh () g g* ...) a))))))

(define-syntax conda
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (a)
       (inc
         (ifa ((g0 a) g ...)
              ((g1 a) g^ ...) ...))))))

(define-syntax ifa
  (syntax-rules ()
    ((_) (mzero))
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
         (() (ifa b ...))
         ((f) (inc (loop (f))))
         ((a) (bind* a-inf g ...))
         ((a f) (bind* a-inf g ...)))))))

(define-syntax condu
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (a)
       (inc
         (ifu ((g0 a) g ...)
              ((g1 a) g^ ...) ...))))))

(define-syntax ifu
  (syntax-rules ()
    ((_) (mzero))
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
         (() (ifu b ...))
         ((f) (inc (loop (f))))
         ((a) (bind* a-inf g ...))
         ((a f) (bind* (unit a) g ...)))))))

(define onceo (lambda (g) (condu (g))))

;;;

; William E. Byrd's miniKanren version of Matt Might's code for derivative
; parsing of regexp.

; Matt's original Scheme code can be found at
; http://matt.might.net/articles/implementation-of-regular-expression-matching-in-scheme-with-derivatives/

; This file requires core miniKanren (conde, ==, fresh) plus =/= and symbolo.

; In theory, tabling will allow this code to parse CFG's (or at least
; be something close to parsing CFG's).

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
(define (check-expect check expect)
  (when (not (equal? check expect))
      (begin (display "check-expect failed; got: ")
             (display check)
             (display "; expected: ")
             (display expect)
             (newline))))

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
