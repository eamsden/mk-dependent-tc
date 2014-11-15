#lang racket
(require "micro-for-dependent.rkt")
(provide fresh conde run == =/= symbolo <o absento)

(define-syntax Zzz
  (syntax-rules ()
    ((_ g) (lambda (s/d/c)
             (lambda ()
               (g s/d/c))))))

(define-syntax conj+
  (syntax-rules ()
    ((_ g) g)
    ((_ g0 g* ...)
     (conj g0 (conj+ g* ...)))))

(define-syntax disj+
  (syntax-rules ()
    ((_ g) g)
    ((_ g0 g* ...)
     (disj g0 (disj+ g* ...)))))

(define-syntax fresh
  (syntax-rules ()
    ((_ () g0 g* ...) (conj+ g0 g* ...))
    ((_ (x0 x* ...) g0 g* ...)
     (call/fresh
      (lambda (x0)
        (fresh (x* ...) g0 g* ...))))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g* ...) (g0* g** ...) ...)
     (Zzz (disj+ (conj+ g0 g* ...)
                 (conj+ g0* g** ...) ...)))))

(define (pull $) (if (procedure? $) (pull ($)) $))

(define (take n $)
  (cond
    ((zero? n) '())
    (else
     (let (($ (pull $)))
       (cond
         ((null? $) '())
         (else
          (cons (car $)
                (take (- n 1) (cdr $)))))))))

(define (take* $)
  (let (($ (pull $)))
    (cond
      ((null? $) '())
      (else
       (cons (car $) (take* (cdr $)))))))

(define-syntax run*
  (syntax-rules ()
    [(_ (q) g0 g ...)
     (let ((q (var 'q)))
       (map (reify-1st q)
            (take* (call/empty-state (conj+ g0 g ...)))))]))

(define-syntax run
  (syntax-rules ()
    ((_ n (q) g0 g ...)
     (let ((q (var 'q)))
       (map (reify-1st q)
            (take n (call/empty-state (conj+ g0 g ...))))))))

