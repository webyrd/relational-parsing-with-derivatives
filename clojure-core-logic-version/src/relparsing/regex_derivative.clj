(ns relparsing.regex_derivative
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]))

(defn symbolo [x]
  (predc x symbol? (fn [c v r a] `(~'sym ~(walk* r (walk* a x))))))

; <regex> ::= #f                     ; Unmatchable pattern
;          |  #t                     ; Empty/blank pattern
;          |  '<symbol>              ; Symbol
;          |  (alt <regex> <regex>)  ; Alternation
;          |  (seq <regex> <regex>)  ; Sequence
;          |  (rep <regex>)          ; Repetition

(def regex-NULL false)
(def regex-BLANK true)

(defn seqo [pat1 pat2 out]
  (conde
    [(== regex-NULL pat1) (== regex-NULL out)]
    [(== regex-NULL pat2) (== regex-NULL out) (!= regex-NULL pat1)]
    [(== regex-BLANK pat1) (== pat2 out) (!= regex-NULL pat2)]
    [(== regex-BLANK pat2) (== pat1 out) (!= regex-NULL pat1) (!= regex-BLANK pat1)]
    [(!= regex-NULL pat1) (!= regex-BLANK pat1) (!= regex-NULL pat2) (!= regex-BLANK pat2)
     (== `(~'seq ~pat1 ~pat2) out)]))

(defn alto [pat1 pat2 out]
  (conde
    [(== regex-NULL pat1) (== pat2 out)]
    [(== regex-NULL pat2) (== pat1 out) (!= regex-NULL pat1)]
    [(!= regex-NULL pat1) (!= regex-NULL pat2)
     (== `(~'alt ~pat1 ~pat2) out)]))

(defn repo [pat out]
  (conde
    [(== regex-BLANK out)
     (conde
       [(== regex-NULL pat)]
       [(== regex-BLANK pat)])]
    [(!= regex-NULL pat) (!= regex-BLANK pat)
     (== `(~'rep ~pat) out)]))

(defn deltao [re out]
  (conde
    [(== regex-BLANK re) (== regex-BLANK out)]
    [(== regex-NULL re) (== regex-NULL out)]
    [(symbolo re) (== regex-NULL out)]
    [(fresh [re1]
       (== `(~'rep ~re1) re)
       (== regex-BLANK out))]
    [(fresh [re1 re2 res1 res2]
       (== `(~'seq ~re1 ~re2) re)
       (deltao re1 res1)
       (deltao re2 res2)
       (seqo res1 res2 out))]
    [(fresh [re1 re2 res1 res2]
       (== `(~'alt ~re1 ~re2) re)
       (deltao re1 res1)
       (deltao re2 res2)
       (alto res1 res2 out))]))

(defn regex-derivativeo [re c out]
  (all
    (symbolo c)
    (conde
      [(== regex-BLANK re) (== regex-NULL out)]
      [(== regex-NULL re) (== regex-NULL out)]
      [(symbolo re)
       (conde
         [(== c re) (== regex-BLANK out)]
         [(!= c re) (== regex-NULL out)])]
      [(fresh [re1 res1 res2]
         (== `(~'rep ~re1) re)
         (regex-derivativeo re1 c res1)
         (repo re1 res2)
         (seqo res1 res2 out))]
      [(fresh [re1 re2 res1 res2]
         (== `(~'alt ~re1 ~re2) re)
         (regex-derivativeo re1 c res1)
         (regex-derivativeo re2 c res2)
         (alto res1 res2 out))]
      [(fresh [re1 re2 res1 res2 res3 res4 res5]
         (== `(~'seq ~re1 ~re2) re)
         (regex-derivativeo re1 c res1)
         (deltao re1 res3)
         (regex-derivativeo re2 c res4)
         (seqo res1 re2 res2)
         (seqo res3 res4 res5)
         (alto res2 res5 out))])))

(defn regex-matcho [pattern data out]
  (conde
    [(== () data)
     (fresh [res]
       (conde
         [(== regex-BLANK out) (== regex-BLANK res)]
         [(== regex-NULL out) (!= regex-BLANK res)])
       (deltao pattern res))]
    [(fresh [a d res]
       (conso a d data)
       (regex-derivativeo pattern a res)
       (regex-matcho res d out))]))

