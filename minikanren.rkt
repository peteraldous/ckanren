#lang racket

(provide (all-defined-out))



(define-syntax λG
  (syntax-rules (:)
    [(_ (a : s d c) body)
     (λ (a)
       (let ([s (car a)]
             [d (cadr a)]
             [c (cddr a)])
         body))]
    [(_ (a) body) (λ (a) body)]))

(define-syntax λM
  (syntax-rules (:)
    [(_ (a : s d c) body)
     (λ (a)
       (let ((s (car a)) (d (cadr a)) (c (cddr a)))
         body))]
    [(_ (a) body) (λ (a) body)]))

(define (mzeroG) #f)
(define unitG (λG (a) a))
(define choiceG cons)

(define (goal-construct fM)
  (λG (a)
      (cond
        [(fM a) => unitG]
        [else (mzeroG)])))

(define (prefix-s s ŝ)
  (cond
    [(null? s) ŝ]
    [else (let loop ((ŝ ŝ))
            (cond
              [(eq? ŝ s) '()]
              [else (cons (car ŝ) (loop (cdr ŝ)))]))]))

(define (make-a s d c)
  (cons s (cons d c)))

(define process-prefix (make-parameter 'dummy))

(define enforce-constraints (make-parameter 'dummy))
(define reify-constraints (make-parameter 'dummy))

(define (==c u v)
  (λM (a : s d c)
      (cond
        [(unify `((,u . ,v )) s)
         => (λ (ŝ)
              (cond
                [(eq? s ŝ) a]
                [else
                 (let ([p (prefix-s s ŝ)]
                       [a (make-a ŝ d c)])
                   (((process-prefix) p c) a))]))]
        [else #f])))

(define ==
  (λ (u v )
    (goal-construct (==c u v ))))

(define-syntax mplusG*
  (syntax-rules ()
    [(_ e) e]
    [(_ e0 e ...) (mplusG e0 (λF () (mplusG* e ...)))]))

(define-syntax case∞
  (syntax-rules ()
    [(_ e (() e0) ((fˆ) e1) ((â) e2) ((a f) e3))
     (let ([a∞ e])
       (cond
         [(not a∞) e0]
         [(procedure? a∞) (let ([fˆ a∞]) e1)]
         [(not (and (pair? a∞)
                    (procedure? (cdr a∞))))
          (let ([â a∞]) e2)]
         [else (let ([a (car a∞)] [f (cdr a∞)])
                 e3)]))]))

(define-syntax λF
  (syntax-rules ()
    [(_ () e) (λ () e)]))

(define-syntax inc
  (syntax-rules ()
    [(_ e) (λF () e)]))

(define (mplusG a∞ f)
  (case∞ a∞
         [() (f )]
         [(fˆ) (inc (mplusG (f) fˆ))]
         [(a) (choiceG a f )]
         [(a fˆ) (choiceG a (λF () (mplusG (f) fˆ)))]))

(define bindG
  (λ (a∞ g)
    (case∞ a∞
           [() (mzeroG)]
           [(f) (inc (bindG (f) g))]
           [(a) (g a)]
           [(a f ) (mplusG (g a) (λF () (bindG (f) g)))])))

(define-syntax bindG*
  (syntax-rules ()
    [(_ e) e]
    [(_ e g0 g ...) (bindG* (bindG e g0 ) g ...)]))

(define-syntax conde
  (syntax-rules ()
    [(_ (g0 g ...) (g1 ĝ ...) ...)
     (λG (a)
         (inc (mplusG* (bindG* (g0 a) g ...)
                       (bindG* (g1 a) ĝ ...)
                       ...)))]))

(define (ext-s x v s)
  (cons `(,x . ,v) s))

(define (oc->proc oc) (car oc))
(define (oc->rator oc) (car (cdr oc)))
(define (oc->rands oc) (cdr (cdr oc)))
(define (oc->prefix oc) (car (oc->rands oc)))

(define var vector)
(define var? vector?)
; this one is my best guess
(define (eq-var? a b)
  (and
   (var? a)
   (var? b)
   (= (vector-length a) (vector-length b) 1)
   (eq? (vector-ref 0 a) (vector-ref 0 b))))
(define empty-s '())
(define lhs car)
(define rhs cdr)

(define (walk u s)
  (cond
    [(not (var? u)) u]
    [(assq u s) => (λ (pr) (walk (rhs pr) s))]
    [else u]))

(define (occurs x v s)
  (let ([v (walk v s)])
    (cond
      [(var? v ) (eq-var? v x )]
      [(pair? v )
       (or (occurs x (car v ) s) (occurs x (cdr v ) s))]
      [else #f])))

(define (unify e s)
  (cond
    [(null? e) s]
    [else
     (let loop ([u (caar e)] [v (cdar e)] [e (cdr e)])
       (let ([u (walk u s)] [v (walk v s)])
         (cond
           [(eq? u v ) (unify e s)]
           [(var? u)
            (and (not (occurs u v s))
                 (unify e (ext-s u v s)))]
           [(var? v )
            (and (not (occurs v u s))
                 (unify e (ext-s v u s)))]
           [(and (pair? u) (pair? v))
            (loop (car u) (car v )
                  `((,(cdr u) . ,(cdr v )) . ,e))]
           [(equal? u v ) (unify e s)]
           [else #f])))]))

(define succeed (== #f #f))
(define fail (== #f #t))
(define (find f l)
  (cond [(memf f l) => car] [else #f]))

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (λG (a)
         (inc
          (let* ([x (var 'x)] ...)
            (bindG* (g0 a) g ...)))))))

(define (walk* w s)
  (let ([v (walk w s)])
    (cond
      [(var? v ) v]
      [(pair? v )
       (cons (walk* (car v ) s) (walk* (cdr v ) s))]
      [else v])))

(define size-s length)

(define (reify-s v s)
  (let ((v (walk v s)))
    (cond
      ((var? v ) (ext-s v (reify-n (size-s s)) s))
      ((pair? v ) (reify-s (cdr v ) (reify-s (car v ) s)))
      (else s))))

(define (reify-n n)
  (string->symbol
   (string-append " " "." (number->string n))))

(define empty-f (λF () (mzeroG)))

(define (reify x)
  (fresh ()
         ((enforce-constraints) x )
         (λG (a : s d c)
             (choiceG
              (let* ([v (walk* x s)]
                     [r (reify-s v empty-s)])
                (cond
                  [(null? r ) v]
                  [else
                   (let ((v (walk* v r )))
                     (cond
                       ((null? c) v )
                       (else
                        (((reify-constraints) v r ) a))))]))
              empty-f))))

(define (take n f)
  (cond
    [(and n (zero? n)) '()]
    [else
     (case∞ (f)
            [() '()]
            [(f) (take n f )]
            [(a) (cons a '())]
            [(a f) (cons a (take (and n (- n 1)) f ))])]))

(define empty-d '())
(define empty-c '())
(define empty-a (make-a empty-s empty-d empty-c))

(define-syntax run
  (syntax-rules ()
    ((_ n (x) g0 g ...)
     (take n
           (λF ()
               ((fresh (x ) g0 g ... (reify x))
                empty-a))))))
(define-syntax run*
  (syntax-rules ()
    ((_ (x ) g0 g ...) (run #f (x ) g0 g ...))))


(define (list-sorted? pred ls)
  (cond
    [(or (null? ls) (null? (cdr ls))) #t]
    [(pred (car ls) (cadr ls)) (list-sorted? pred (cdr ls))]
    [else #f]))
(define (list-insert pred x ls)
  (cond
    [(null? ls) (cons x '())]
    [(pred x (car ls)) (cons x ls)]
    [else (cons (car ls) (list-insert pred x (cdr ls)))]))
