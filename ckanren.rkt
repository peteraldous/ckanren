#lang racket

(require "minikanren.rkt")

(provide (all-defined-out))


(define identityM (λM (a) a))
(define (composeM fM fˆM)
  (λM (a)
      (let ([a (fM a)])
        (and a (fˆM a)))))

; Since x* is a list of variables, which is constructed using
; var, which is itself, constructed using vector, we must use
; memq, when checking for membership in the list. In a purely
; functional setting, we would need to build variables in a
; different way, probably relying on a monotonically increasing
; non-negative integer variable.
(define (any/var? t)
  (cond
    [(var? t) #t]
    [(pair? t)
     (or (any/var? (car t)) (any/var? (cdr t)))]
    [else #f]))
(define (any-relevant/var? t x*)
  (cond
    [(var? t) (memq t x*)]
    [(pair? t) (or (any-relevant/var? (car t) x* )
                   (any-relevant/var? (cdr t) x* ))]
    [else #f]))

(define (ext-c oc c)
  (cond
    [(any/var? (oc->rands oc)) (cons oc c)]
    [else c]))

; getδ looks up a variable's current domain in d . If a variable
; does not currently have a domain, this function returns false.
; In order to distinguish between variables without domains,
; and values that can never have domains (such as #t or
; negative numbers), the argument to getδ must be a variable.
(define (getδ x d)
  (cond
    [(assq x d) => rhs]
    [else #f]))

; appendix A

; Applying conventional operations to domains is efficient
; when the lists representing the domains are sorted.
(define (value?δ v) (and (integer? v) (<= 0 v)))
(define (memv?δ v δ) (and (value?δ v) (memv v δ)))
(define null?δ null?)
(define (singleton?δ δ) (null? (cdr δ)))
(define singleton-elementδ car)
(define minδ car)
(define (maxδ δ)
  (cond
    [(null? (cdr δ)) (car δ)]
    [else (maxδ (cdr δ))]))
(define (disjoint?δ δ1 δ2)
  (cond
    [(or (null? δ1 ) (null? δ2 )) #t]
    [(= (car δ1) (car δ2)) #f]
    [(< (car δ1) (car δ2))
     (disjoint?δ (cdr δ1) δ2)]
    [else (disjoint?δ δ1 (cdr δ2))]))
(define (diffδ δ1 δ2)
  (cond
    [(or (null? δ1 ) (null? δ2 )) δ1]
    [(= (car δ1) (car δ2)) (diffδ (cdr δ1 ) (cdr δ2 ))]
    [(< (car δ1) (car δ2))
     (cons (car δ1) (diffδ (cdr δ1) δ2 ))]
    [else (diffδ δ1 (cdr δ2 ))]))
(define (intersectionδ δ1 δ2)
  (cond
    [(or (null? δ1) (null? δ2)) '()]
    [(= (car δ1) (car δ2))
     (cons (car δ1)
           (intersectionδ (cdr δ1) (cdr δ2)))]
    [(< (car δ1) (car δ2))
     (intersectionδ (cdr δ1) δ2)]
    [else (intersectionδ δ1 (cdr δ2))]))

(define (recover/vars p)
  (cond
    [(null? p) '()]
    [else
     (let ([x (lhs (car p))]
           [v (rhs (car p))]
           [r (recover/vars (cdr p))])
       (cond
         [(var? v) (ext/vars v (ext/vars x r))]
         [else (ext/vars x r)]))]))
(define (ext/vars x r)
  (cond
    [(memq x r) r]
    [else (cons x r)]))


(define (verify-all-bound c bound-x*)
  (unless (null? c)
    (cond
      [(find (λ (x) (not (memq x bound-x*)))
             (filter var? (oc->rands (car c))))
       => (λ (x)
            (error 'verify-all-bound
                   "Constrained variable ~s without domain"
                   x))]
      [else (verify-all-bound (cdr c) bound-x*)])))

(define (subsumes? p s)
  (cond
    [(unify p s)
     => (λ (ŝ) (eq? s ŝ))]
    [else #f]))

; finite domains dependencies

(define (rem/run oc)
  (λM (a : s d c)
      (cond
        [(memq oc c)
         (let [(ĉ (remq oc c))]
           ((oc->proc oc) (make-a s d ĉ)))]
        (else a))))

(define (run-constraints x* c)
  (cond
    ((null? c) identityM)
    ((any-relevant/var? (oc->rands (car c)) x* )
     (composeM
      (rem/run (car c))
      (run-constraints x* (cdr c))))
    (else (run-constraints x* (cdr c)))))

(define (ext-d x fd d) (cons `(,x . ,fd) d))

(define (resolve-storableδ δ x)
  (λM (a : s d c)
      (cond
        [(singleton?δ δ)
         (let* ((n (singleton-elementδ δ))
                (a (make-a (ext-s x n s) d c)))
           ((run-constraints `(,x ) c) a))]
        [else (make-a s (ext-d x δ d ) c)])))

(define (update-varδ x δ)
  (λM (a : s d c)
      (cond
        ((getδ x d )
         => (λ (xδ )
              (let ((i (intersectionδ xδ δ)))
                (cond
                  ((null? δ i) #f)
                  (else ((resolve-storableδ i x ) a))))))
        (else ((resolve-storableδ δ x ) a)))))

(define (processδ v δ)
  (λM (a)
      (cond
        [(var? v ) ((update-varδ v δ) a)]
        [(memv?δ v δ) a]
        [else #f])))

(define (makeδ n*) n*)

(define-syntax letδ
  (syntax-rules (:)
    ((_ (s d ) ((u : uδ ) ...) body)
     (let ((u (walk u s)) ...)
       (let ((uδ (cond
                   ((var? u) (getδ u d ))
                   (else (makeδ `(,u)))))
             ...)
         body)))))

(define-syntax build-auxoc
  (syntax-rules ()
    [(_ op () (z ...) (arg ...))
     (let ([z arg] ...) `(,(op z ...) . (op ,z ...)))]
    [(_ op (arg0 arg ...) (z ...) args)
     (build-auxoc op (arg ...) (z ... q) args)]))
(define-syntax buildoc
  (syntax-rules ()
    [(_ op arg ...)
     (build-auxoc op (arg ...) () (arg ...))]))

(define-syntax c-op
  (syntax-rules (:)
    ((_ op ((u : uδ ) ...) body)
     (λM (a : s d c)
         (letδ (s d ) ((u : uδ ) ...)
               (let* ([c (ext-c (buildoc op u ...) c)]
                      [a (make-a s d c)])
                 (cond
                   [(and uδ ...) (body a)]
                   [else a])))))))

; finite domains
(define (copy-before pred δ)
  (cond
    [(null? δ) '()]
    [(pred  (car δ)) '()]
    [else (cons (car δ) (copy-before pred (cdr δ)))]))
(define (drop-before pred δ)
  (cond
    [(null? δ) '()]
    [(pred (car δ)) δ]
    [else (drop-before pred (cdr δ))]))

(define (domfdc x n*)
  (λM (a : s d c)
      ((processδ (walk x s) (makeδ n* )) a)))

(define (domfd x n*)
  (goal-construct (domfdc x n*)))

(define (⩽fd u v)
  (goal-construct (⩽fdc u v)))

(define (⩽fdc u v)
  (c-op ⩽fdc ((u : uδ) (v : vδ))
        (let ([umin (minδ uδ)]
              [vmax (maxδ vδ)])
          (composeM
           (processδ u (copy-before (λ (u) (< vmax u)) uδ))
           (processδ v (drop-before (λ (v) (<= umin v )) vδ))))))

(define (+fdc u v w)
  (c-op +fdc ((u : uδ) (v : vδ) (w : wδ))
        (let ([umin (minδ uδ)] [umax (maxδ uδ)]
                               [vmin (minδ vδ)]
                               [vmax (maxδ vδ)]
                               [wmin (minδ wδ)]
                               [wmax (maxδ wδ)])
          (composeM
           (processδ w
                     (range (+ umin vmin) (+ umax vmax)))
           (composeM
            (processδ u
                      (range
                       (- wmin vmax) (- wmax vmin)))
            (processδ v
                      (range
                       (- wmin umax) (- wmax umin))))))))

(define (+fd u v w)
  (goal-construct (+fdc u v w)))

(define (=/=fdc u v)
  (λM (a : s d c)
      (letδ (s d) ((u : uδ) (v : vδ))
            (cond
              [(or (not uδ) (not vδ))
               (make-a s d (ext-c (buildoc =/=fdc u v) c))]
              [(and (singleton?δ uδ )
                    (singleton?δ vδ )
                    (= (singleton-elementδ uδ )
                       (singleton-elementδ vδ )))
               #f]
              [(disjoint?δ uδ vδ) a]
              [else
               (let* ([ĉ (ext-c (buildoc =/=fd
                                         c u v ) c)]
                      [a (make-a s d ĉ)])
                 (cond
                   [(singleton?δ uδ)
                    ((processδ v (diffδ vδ uδ)) a)]
                   [(singleton?δ vδ)
                    ((processδ u (diffδ uδ vδ)) a)]
                   [else a]))]))))

(define (=/=fd u v)
  (goal-construct (=/=fdc u v)))

(define (exclude-fromδ δ1 d x*)
  (let loop ([x* x*])
    (cond
      [(null? x*) identityM]
      [(getδ (car x* ) d )
       => (λ (δ2 )
            (composeM
             (processδ (car x*) (diffδ δ2 δ1 ))
             (loop (cdr x*))))]
      [else (loop (cdr x* ))])))

(define (all-diff/fdc y* n*)
  (λM (a : s d c)
      (let loop ((y* y*) (n* n*) (x* '()))
        (cond
          [(null? y*)
           (let* ([oc (buildoc all-diff/fdc x* n*)]
                  [a (make-a s d (ext-c oc c))])
             ((exclude-fromδ (makeδ n* ) d x*) a))]
          [else
           (let ([y (walk (car y*) s)])
             (cond
               [(var? y) (loop (cdr y* ) n* (cons y x* ))]
               [(memv?δ y n* ) #f]
               [else (let ((n* (list-insert < y n*)))
                       (loop (cdr y*) n* x* ))]))]))))

; sort is list-sort in r6rs
(define list-sort sort)

(define (all-difffdc v*)
  (λM (a : s d c)
      (let ([v* (walk v* s)])
        (cond
          [(var? v*)
           (let* ((oc (buildoc all-difffdc v*)))
             (make-a s d (ext-c oc c)))]
          [else
           (let-values (((x* n*) (partition var? v*)))
             (let ([n* (list-sort < n*)])
               (cond
                 [(list-sorted? < n*)
                  ((all-diff/fdc x* n*) a)]
                 [else #f])))]))))

(define (all-difffd v*)
  (goal-construct (all-difffdc v*)))

(define-syntax infd
  (syntax-rules ()
    ((_ x0 x ... e)
     (let ([n* e])
       (fresh () (domfd x0 n*) (domfd x n*) ...)))))

#|
(define (run-constraints0 x∗-ignored c)
  (cond
    [(null? c) identityM]
    [else
      (composeM
        (oc->proc (car c))
        (run-constraints0 x∗-ignored (cdr c)))]))

(define (run-constraints1 x∗ c)
     (cond
       [(null? c) identityM]
       [(any-relevant/var? (oc->rands (car c)) x∗ )
         (composeM
           (oc->proc (car c))
           (run-constraints1 x∗ (cdr c)))]
       [else (run-constraints1 x∗ (cdr c))]))
|#

(define (process-prefix-FD p c)
  (cond
    [(null? p) identityM]
    [else
       (let ([x (lhs (car p))]
             [v (rhs (car p))])
         (let ([t (composeM
                    (run-constraints `(,x ) c)
                    (process-prefix-FD (cdr p) c))])
           (λM (a : s d c)
                 (cond
                   [(getδ x d )
                    => (λ (δ)
                         ((composeM (processδ v δ) t) a))]
                   [else (t a)]))))]))

(define (map-sum f)
  (letrec
    ([loop
       (λ (ls)
          (cond
            [(null? ls) fail]
            [else
              (conde
                [(f (car ls))]
                [(loop (cdr ls))])]))])
    loop))

(define (force-ans x)
  (λG (a : s d c)
      (let ([x (walk x s)])
        ((cond
           [(and (var? x ) (getδ x d ))
            => (map-sum (λ (v ) (== x v)))]
           [(pair? x )
            (fresh ()
              (force-ans (car x ))
              (force-ans (cdr x )))]
           [else succeed])
         a))))

(define-syntax ifu
  (syntax-rules ()
    ((_) (mzeroG))
    ((_ (e g ...) b ...)
     (let loop ([a∞ e])
       (case∞ a∞
              (() (ifu b ...))
         ((f) (inc (loop (f))))
         ((a) (bindG* a∞ g ...))
         ((a f) (bindG* a g ...)))))))

(define-syntax condu
  (syntax-rules ()
    [(_ (g0 g ...) (g1 ĝ ...) ...)
     (λG (a)
         (inc (ifu ((g0 a) g ...) ((g1 a) ĝ ...) ...)))]))
(define (onceo g) (condu (g)))

(define (enforce-constraints-FD x)
  (fresh ()
    (force-ans x)
    (λG (a : s d c)
        (let ([bound-x∗ (map lhs d )])
          (verify-all-bound c bound-x∗ )
          ((onceo (force-ans bound-x∗ )) a)))))

(define (reify-constraints-FD m r)
  (error 'reify-constraints-FD "Unbound vars at end\n"))
