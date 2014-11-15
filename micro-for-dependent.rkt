#lang racket
(provide conj disj == call/fresh reify-1st call/empty-state var =/= symbolo <o absento)
(require graph)

(define (var x) (vector x))
(define (var? x) (vector? x))

(define (ext-s x v s)
  (cond
    ((occurs? x v s) #f)
    (else `((,x . ,v) . ,s))))

(define occurs?
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? x v))
        ((pair? v) (or (occurs? x (car v) s)
                       (occurs? x (cdr v) s)))
        (else #f)))))

(define (walk u s)
  (let ((pr (and (var? u) (assq u s))))
    (if pr (walk (cdr pr) s) u)))

(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
      ((and (var? u) (var? v) (eq? u v)) s)
      ((var? u) (ext-s u v s))
      ((var? v) (ext-s v u s))
      ((and (not (var? u)) (not (var? v)) (eqv? u v)) s)
      (else
       (and (pair? u) (pair? v)
            (let ((s (unify (car u) (car v) s)))
              (and s (unify (cdr u) (cdr v) s))))))))

(define mzero '())

(define empty-c-store (make-immutable-hash '((d . ()) (s . ()) (l . ()) (a . ()))))

(define empty-state `(() ,empty-c-store . 0))

(define (call/fresh f)
  (lambda (s/d/c)
    (let ((c (cddr s/d/c)))
      ((f (var c)) `(,(car s/d/c) ,(cadr s/d/c) . ,(+ c 1))))))

(define (== u v)
  (lambda (s/d/c)
    (let ((s (unify u v (car s/d/c))))
      (cond
        (s (cond
             ((ormap (lambda (pr) (eq? s (unify (car pr) (cdr pr) s))) (hash-ref (cadr s/d/c) 'd)) mzero)
             ((ormap (lambda (non-sym) (symbol? (walk non-sym s))) (hash-ref (cadr s/d/c) 's)) mzero)
             ((ormap (lambda (pr) (mem-check (car pr) (cdr pr) s)) (hash-ref (cadr s/d/c) 'a)) mzero)
             (else (unit `(,s . ,(cdr s/d/c))))))
        (else mzero)))))

(define (acyclic? ls)
  (let ((g (unweighted-graph/directed ls)))
    (dag? g)))

;; doesn't work with =/= or symbolo or == or absento
(define (<o u v)
  (lambda (s/d/c)
    (let ((s (car s/d/c)))
      (let ((u^ (walk u s)) (v^ (walk v s)))
        (let ((d (cadr s/d/c)))
          (let ((oldls (foldr (lambda (pr ls)
                                `((,(walk (car pr) s) ,(walk (cdr pr) s)) . ,ls))
                              '()
                              (hash-ref d 'l))))
            (cond
              ((acyclic? `((,u ,v) . ,oldls))
               (unit `(,s ,(hash-update d 'l ((curry cons) `(,u . ,v))) . ,(cddr s/d/c))))
              (else mzero))))))))

;; doesn't work with <o
(define (=/= u v)
  (lambda (s/d/c)
    (let ((s (car s/d/c)))
      (let ((s^ (unify u v s)))
        (cond
          (s^ (cond
                ((eq? s s^) mzero)
                (else (unit `(,s ,(hash-update (cadr s/d/c) 'd ((curry cons) `(,u . ,v))) . ,(cddr s/d/c))))))
          (else (unit s/d/c)))))))

(define (symbolo sym)
  (lambda (s/d/c)
    (let ((s (car s/d/c)))
      (let ((sym^ (walk sym s)))
        (cond
          ((symbol? sym^) mzero)
          (else (unit `(,s ,(hash-update (cadr s/d/c) 's ((curry cons) sym^)) . ,(cddr s/d/c)))))))))

(define (unit s/d/c) (cons s/d/c mzero))

(define (disj g1 g2) (lambda (s/d/c) (mplus (g1 s/d/c) (g2 s/d/c))))

(define (conj g1 g2) (lambda (s/d/c) (bind (g1 s/d/c) g2)))

(define (mplus $1 $2)
  (cond
    ((procedure? $1) (lambda () (mplus $2 ($1))))
    ((null? $1) $2)
    (else (cons (car $1) (mplus (cdr $1) $2)))))

(define (bind $ g)
  (cond
    ((procedure? $) (lambda () (bind ($) g)))
    ((null? $) mzero)
    (else (mplus (g (car $)) (bind (cdr $) g)))))

;; doesn't work with any of the constraints
(define absento
  (lambda (u v)
    (lambda (s/d/c)
      (let ((s (car s/d/c)))
        (cond
          ((mem-check u v s) mzero)
          (else
           (unit `(,s ,(hash-update (cadr s/d/c) 'l ((curry cons) `(,u . ,v))) . ,(cddr s/d/c)))))))))

(define mem-check
  (lambda (u t s)
    (let ((t (walk t s)))
      (cond
        ((pair? t)
         (or (term=? u t s)
             (mem-check u (car t) s)
             (mem-check u (cdr t) s)))
        (else (term=? u t s))))))

(define term=?
  (lambda (u v s)
    (let ((u (walk u s)) (v (walk v s)))
      (cond
        ((and (pair? u) (pair? v))
         (and (term=? (car u) (car v) s)
              (term=? (cdr u) (cdr v) s)))
        (else (term=?-nonpair u v s))))))

;; this *should* just work here?? Maybe??
(define term=?-nonpair
  (lambda (u v s)
    (cond
      ((eq? u v) #t)
      ((var? u) #f)
      ((var? v) #f)
      ((equal? u v) #t)
      (else #f))))

(define walk*
  (lambda (w s)
    (let ((v (walk w s)))
      (cond
        ((var? v) v)
        ((pair? v) (cons (walk* (car v) s)
                         (walk* (cdr v) s)))
        (else v)))))

(define (reify-r v s)
  (let ((v (walk v s)))
    (cond
      ((var? v)
       (let ((n (reify-name (length s))))
         (cons `(,v . ,n) s)))
      ((pair? v) (reify-r (cdr v) (reify-r (car v) s)))
      (else s))))

(define (reify-name n)
  (string->symbol
    (string-append "_." (number->string n))))

(define (reify-1st q)
  (lambda (s/d/c)
    (let ((s (car s/d/c)))
      (let ((v (walk* q s)))
        (let ((d? (map (lambda (pr) (unify (car pr) (cdr pr) s)) (hash-ref (cadr s/d/c) 'd))))
          (let ((d+ (filter (lambda (x) x) (map (find-pfx s) d?))))
            (let ((rename-s (reify-r v '())))
              (let ((d (filter-not (lambda (d) (anyvar? d rename-s)) (rem-subsumed d+))))
                (form (walk* v rename-s) (walk* d rename-s))))))))))

(define form
  (lambda (v d)
    (let ((fd (sort-D d)))
      (cond
        ((null? fd) v)
        (else
         (let ((fd (drop-dot-D fd)))
           `(,v . ((=/= . ,fd)))))))))

(define sorter
  (lambda (ls)
    (sort ls lex<=?)))

(define sort-D
  (lambda (D)
    (sorter (map sort-d D))))

(define sort-d
  (lambda (d)
    (sort
      (map sort-pr d)
      (lambda (x y)
        (lex<=? (car x) (car y))))))

(define drop-dot
  (lambda (X)
    (map (lambda (t)
           (let ((a (car t))
                 (d (cdr t)))
             `(,a ,d)))
         X)))

(define drop-dot-D
  (lambda (D)
    (map drop-dot D)))

(define lex<-reified-name?
  (lambda (r)
    (char<?
      (string-ref (datum->string r) 0)
      (string-ref "_" 0))))

(define (call-with-string-output-port f)
  (define p (open-output-string))
    (f p)
    (get-output-string p))

(define datum->string
  (lambda (x)
    (call-with-string-output-port
      (lambda (p) (display x p)))))

(define sort-pr
  (lambda (pr)
    (let ((l (car pr))
          (r (cdr pr)))
      (cond
        ((lex<-reified-name? r) pr)
        ((lex<=? r l) `(,r . ,l))
        (else pr)))))

(define lex<=?
  (lambda (x y)
    (cond
      ((boolean? x)
       (cond
         ((boolean? y) (or (not x) (eq? x y)))
         (else #t)))
      ((boolean? y) #f)
      ((null? x) #t)
      ((null? y) #f)
      ((number? x)
       (cond
         ((number? y) (<= x y))
         (else #t)))
      ((number? y) #f)
      ((symbol? x)
       (cond
         ((symbol? y)
          (string<=? (symbol->string x)
                     (symbol->string y)))
         (else #t)))
      ((symbol? y) #f)
      ((pair? x)
       (cond
         ((pair? y)
          (cond
            ((equal? (car x) (car y))
             (lex<=? (cdr x) (cdr y)))
            (else (lex<=? (car x) (car y)))))))
      ((pair? y) #f)
      (else #t))))

(define find-pfx
  (lambda (s)
    (lambda (s^)
      (cond
        ((not s^) #f)
        ((eq? s s^) '())
        (else (cons (car s^) ((find-pfx s) (cdr s^))))))))

(define rem-subsumed
  (lambda (D)
    (let loop ((D D) (D+ '()))
      (cond
        ((null? D) D+)
        ((or (subsumed? (car D) (cdr D))
             (subsumed? (car D) D+))
         (loop (cdr D) D+))
        (else (loop (cdr D)
                (cons (car D) D+)))))))

(define unify*
  (lambda (S+ S)
    (unify (map car S+) (map cdr S+) S)))

(define subsumed?
  (lambda (d D)
    (cond
      ((null? D) #f)
      (else (let ((d^ (unify* (car D) d)))
              (or (and d^ (eq? d^ d))
                  (subsumed? d (cdr D))))))))

(define anyvar?
  (lambda (u S)
    (cond
      ((var? u) (var? (walk u S))) 
      ((pair? u) (or (anyvar? (car u) S)
                     (anyvar? (cdr u) S)))
      (else #f))))

(define call/empty-state
  (lambda (g) (g empty-state)))