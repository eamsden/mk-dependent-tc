#lang racket
(require "pmatch.rkt")
(require "mini-for-dependent.rkt")
(provide (all-defined-out) (all-from-out "mini-for-dependent.rkt"))

; Fails with pmatch failure
(define (lookup x env)
  (pmatch env
     (`((,y . ,t) . ,rst) (if (eqv? x y) t (lookup x rst)))))

(define (extend env x t) `((,x . ,t) . ,env))

; Needs to do alpha-renaming of binders
; Invariant: val is in normal form
(define (subst exp val x)
  (pmatch exp
    (`,y (guard (symbol? y)) (if (eqv? x y)
                                 val
                                 y))
    (`(lambda (,y : ,t) ,bod) `(lambda (,y : ,(subst t val x)) ,(if (eqv? x y)
                                                                    bod
                                                                    (subst bod val x))))
    (`(forall (,y : ,t) ,bod) `(forall (,y : ,(subst t val x)) ,(if (eqv? x y)
                                                                    bod
                                                                    (subst bod val x))))
    (`(,rator ,rand) `(,(subst rator val x) ,(subst rand val x)))))

; Invariant: exp has a type
(define (nf exp)
  (pmatch exp
    (`,x (guard (symbol? x)) x)
    (`(lambda (,x : ,t) ,bod) `(lambda (,x : ,t) ,(nf bod)))
    (`(forall (,x : ,t) ,bod) `(forall (,x : ,t) ,(nf bod)))
    (`(,rator ,rand)
      (pmatch (nf rator)
        (`(lambda (,x : ,t) ,bod) (subst bod (nf rand) x))
        (`,rator^ `(,rator^ ,(nf rand)))))))

(define (compat env trator rand)
  (pmatch (nf trator)
    (`(forall (,x : ,t) ,bod)
      (if (equal? t (tc env rand))
        (subst bod (nf rand) x)
        (error 'compat-type-eq "Type mismatch")))))

(define (tc exp env)
  (pmatch exp
     (`(type) `(type))
     (`,x (guard (symbol? x)) (lookup exp env))
     (`(lambda (,x : ,t) ,bod) (if (equal? (tc t env) `(type))
                                   `(forall (,x : ,t) ,(tc bod (extend env x t)))
                                   (error 'tc-lambda "type of annotation is not (type)")))
     (`(forall (,x : ,t) ,bod) (if (equal? (tc t env) `(type))
                                   (if (equal? (tc bod (extend env x t)))
                                       `(type)
                                       (error 'tc-forall-bod "type of forall body is not (type)"))
                                   (error 'tc-forall-bind "type of annotation is not (type)")))
     (`(,rator ,rand) (compat env (tc env rator) rand))))

(define (lookupo env x ty)
  (fresh (y t rst)
    (== env `((,y . ,t) . ,rst))
    (conde
      ((== x y) (== ty t))
      ((=/= x y) (lookupo rst x ty)))))

(define (extendo env x ty env^)
  (== env^ `((,x . ,ty) . ,env)))

(define (nfo tin tout)
  (conde
    ((== tin `(type)) (== tout `(type)))
    ((symbolo tin) (== tin tout))
    ((fresh (x t t^ bod bod^)
       (== tin `(lambda (,x : ,t) ,bod))
       (== tout `(lambda (,x : ,t^) ,bod^))
       (nfo t t^)
       (nfo bod bod^)))
    ((fresh (x t t^ bod bod^)
       (== tin `(forall (,x : ,t) ,bod))
       (== tout `(forall (,x : ,t^) ,bod^))
       (nfo t t^)
       (nfo bod bod^)))
    ((fresh (rator rand rator^ rand^)
       (== tin `(,rator ,rand))
       (conde
         ((fresh (x t bod)
            (== rator^ `(lambda (,x : ,t) ,bod))
            (substo bod rand^ x tout)))
         ((symbolo rator^) (== tin tout))
         ((fresh (rator^^ rand^^)
            (== rator^ `(,rator^^ ,rand^^))
            (== tin tout))))
       (nfo rator rator^)
       (nfo rand rand^)))))

(define (compato env trator rand tout)
  (fresh (trator^ trand x t bod rand^ t^)
    (== trator^ `(forall (,x : ,t) ,bod))
    (symbolo x)
    (tco rand env trand)
    (nfo trator trator^)
    (nfo t t^)
    (nfo trand t^)
    (nfo rand rand^)
    (substo bod rand^ x tout)))

(define (substo exp v x expout)
  (fresh ()
    (symbolo x)
    (conde
      ((== exp `(type)) (== exp expout))
      ((symbolo exp) (=/= exp x) (== exp expout))
      ((== exp x) (== expout v))
      ((fresh (y t bod t^)
         (symbolo y)
         (== `(lambda (,y : ,t) ,bod) exp)
         (conde
           ((== x y) (== expout `(lambda (,y : ,t^) ,bod)))
           ((=/= x y) (fresh (z bod^ bod^^)
                        (symbolo z)
                        (=/= x z)
                        (== expout `(lambda (,z : ,t^) ,bod^^))
                        (absento z v)
                        (absento z bod)
                        (substo bod z y bod^)
                        (substo bod^ v x bod^^))))
         (substo t v x t^)))
      ((fresh (y t bod t^)
         (symbolo y)
         (== `(forall (,y : ,t) ,bod) exp)
         (conde
           ((== x y) (== expout `(forall (,y : ,t^) ,bod)))
           ((=/= x y) (fresh (z bod^ bod^^)
                        (symbolo z)
                        (=/= x z)
                        (== expout `(forall (,z : ,t^) ,bod^^))
                        (absento z v)
                        (absento z bod)
                        (substo bod z y bod^)
                        (substo bod^ v x bod^^))))
         (substo t v x t^))))))
                        



(define (tco exp env ty)
  (conde
     ((== exp `(type)) (== ty `(type)))
     ((symbolo exp) (lookupo env exp ty))
     ((fresh (x t bod bodty env^)
        (symbolo x)
        (== exp `(lambda (,x : ,t) ,bod))
        (== ty `(forall (,x : ,t) ,bodty))
        (tco t env `(type))
        (extendo env x t env^) 
        (tco bod env^ bodty)))
     ((fresh (x t bod env^ tt bodt)
        (symbolo x)
        (== exp `(forall (,x : ,t) ,bod))
        (== ty `(type))
        (tco t env tt)
        (nfo tt `(type))
        (extendo env x t env^)
        (tco bod env^ bodt)
        (nfo bodt `(type))))
     ((fresh (rator rand trator)
        (== exp `(,rator ,rand))
        (tco rator env trator)
        (compato env trator rand ty)))))

