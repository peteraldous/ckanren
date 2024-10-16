#lang racket

(require "r6rs-compat.rkt")

(provide (all-defined-out))
(provide (all-from-out "r6rs-compat.rkt"))

; Take a substitution and produce an ordered sequence of zero or more values
; (usually substitutions).
;
; Produce a λ that takes a value a and executes body.
; If s, d, and c are provided, the lambda matches a against the pattern (s . (d
; . c)) and those names are bound in the execution of body.
; Alternately, specifying only a essentially makes this form into a λ.
(define-syntax λG
  (syntax-rules (:)
    ; a syntax that breaks `a` down to match the pattern `(,s (,d ,c)) and then evaluates `body`.
    [(_ (a : s d c) body)
     (λ (a)
       (match a
         [(package s d c) body]))]
    ; in this form, identical to `λ`
    [(_ (a) body) (λ (a) body)]))

; Identical (except for its name) to λG
(define-syntax λM
  (syntax-rules (:)
    [(_ (a : s d c) body)
     (λ (a)
       (match a
         [(package s d c) body]))]
    [(_ (a) body) (λ (a) body)]))

; streams
; anywhere we see a∞ or case∞, we know it's dealing with these streams

; empty stream
(define (mzeroG)
  #f)
; singleton stream
; a must not be `#f`, a function, or a pair whose `cdr` is a function
(define unitG (λG (a) a))
; a stream: `car` is the first element; `cdr` is the thunk that produces the remainder
(define choiceG cons)
; incomplete stream - e evaluates to a stream
(define-syntax inc
  (syntax-rules ()
    [(_ e) (λF () e)]))

; case - cond for streams
; the four cases correspond in order to an empty stream, a non-empty
; (non-singleton) stream, a singleton stream, and a pair whose cdr is a
; function; in other words, a choice variant.
(define-syntax case∞
  (syntax-rules ()
    [(_ e (() e0) ((fˆ) e1) ((â) e2) ((a f) e3))
     (let ([a∞ e])
       (cond
         ; empty stream - mzero
         [(not a∞) e0]
         ; inc (not unit, by convention)
         [(procedure? a∞) (let ([fˆ a∞]) e1)]
         ; not false (mzero) because that test failed
         ; not a procedure (inc) because that test failed
         ; not a pair whose second element is a procedure (choice)
         ; the remaining option is unit
         [(not (and (pair? a∞) (procedure? (cdr a∞)))) (let ([â a∞]) e2)]
         ; a pair whose cdr is a function - choice
         [else
          (let ([a (car a∞)]
                [f (cdr a∞)])
            e3)]))]))

; Intuitively, take a function `fM` and turn it into a goal; as a goal, it takes a package `a` and
; applies `fM` to it. If the result is #f, it produces an empty stream `(aka `(mzeroG)`). Otherwise,
; it takes the result of `(fM A)` and stores it in a singleton stream (aka `unitG`).
(define (goal-construct fM)
  (λG (a)
      (cond
        [(fM a)
         =>
         unitG]
        [else (mzeroG)])))

; return the prefix of `s` that is not in `ŝ`. To restate in a way that is less tied to the
; implementation, produce a substitution containing the elements that were added to `ŝ` to form `s`.
(define (prefix-s s ŝ)
  (cond
    [(null? s) ŝ]
    [else
     (let loop ([ŝ ŝ])
       (cond
         [(eq? ŝ s) '()]
         [else (cons (car ŝ) (loop (cdr ŝ)))]))]))

; a stands for package (obviously :P) and its contents s d and c stand for substitution, domains,
; and constraints.
; This differs from the original formulation, which expressed a package in the form `(,s . (,d .
; ,c)).
;
; A substitution, as noted elsewhere, is a sequence of bindings.
; `d` is a list of (var . domain) pairs, where a domain is a non-empty list of possible values (in
; ckanren's FD domain, this is natural numbers).
; `c` contains predefined constraints in a normalized form.
(struct package (substitution domains constraints))

; intuitively, `p` is a prefix of a substitution (i.e., the bindings added to a substitution since
; some point in time. `process-prefix` adds those new constraints to `c`, the current constraints.
(define process-prefix (make-parameter (λ (p c) 'dummy)))
; called prior to reification; `x` is the variable to be reified
(define enforce-constraints (make-parameter (λ (x) 'dummy)))
(define reify-constraints (make-parameter (λ (v r) 'dummy)))

(define (==c u v)
  (λM (a : s d c)
      (cond
        [(unify `((,u . ,v)) s)
         =>
         (λ (ŝ)
           (cond
             [(eq? s ŝ) a]
             [else
              (let ([p (prefix-s s ŝ)]
                    [a (package ŝ d c)])
                (((process-prefix) p c) a))]))]
        [else #f])))

(define == (λ (u v) (goal-construct (==c u v))))

; A thunk that produces the remainder of a stream - in implementation, `λF` is equivalent to `λ`.
(define-syntax λF
  (syntax-rules ()
    [(_ () e) (λ () e)]))

#|
mplusG - combine streams together in an interleaved fashion

(define (mplusG a∞ f)
  (case∞ a∞
         [() (f)]
         [(fˆ) (inc (mplusG (f) fˆ))]
         [(a) (choiceG a f)]
         [(a fˆ) (choiceG a (λF () (mplusG (f) fˆ)))]))

becomes

; in both the procedure and choice cases, (f) goes before f^. This is the reverse of what I
; expected. Why? Is this because "... a relative fairness because all of the stream values will be
; interleaved"? Why are they interleaved?
(λ (a∞ f)
  (let ([a∞ a∞])
    (cond
      ; if `a∞` is an empty stream, then call `f` to produce a stream
      [(not a∞) (f)]
      ; if `a∞` is a procedure, then make an inc that calls `f` and prepends it to `a∞`
      [(procedure? a∞) (let ([f^ a∞]) (inc (mplusG (f) f^)))]
      ; if it's unit (a singleton), prepend it to `f`
      [(not (and (pair? a∞) (procedure? (cdr a∞)))) (let ([a a∞]) (choiceG a f))]
      ; otherwise, it's a choice
      ; get the value and thunk and build a stream that starts with the value `(car a∞)` and
      ;   continues with a thunk that produces a stream: the concatenation of two the stream
      ;   produced by calling `f` and the stream that is the second half of `a∞`.
      [else
        (let ([a (car a∞)]
              [f^ (cdr a∞)])
          (choiceG a (λF () (mplusG (f) f^))))])))

|#

(define (mplusG a∞ f)
  (case∞ a∞
         [() (f)]
         [(fˆ) (inc (mplusG (f) fˆ))]
         [(a) (choiceG a f)]
         [(a fˆ) (choiceG a (λF () (mplusG (f) fˆ)))]))

; use mplusG to combine an arbitrary number of streams together
(define-syntax mplusG*
  (syntax-rules ()
    [(_ e) e]
    [(_ e0 e ...) (mplusG e0 (λF () (mplusG* e ...)))]))

; apply the goal `g` to each element in `a∞`.
(define (bindG a∞ g)
  (case∞ a∞
         ; if it's an empty stream, then return an empty stream
         [() (mzeroG)]
         ; if it's an inc, get the value and use `bindG` on it (and wrap it back in an `inc`)
         [(f) (inc (bindG (f) g))]
         ; if it's a unit (singleton), apply `g` to it directly
         [(a) (g a)]
         ; if it's a choice, then apply `g` to `a` and then make a function that lazily recurs to
         ; apply apply the goal `g` to whatever `f` produces.
         [(a f) (mplusG (g a) (λF () (bindG (f) g)))]))

; apply an arbitrary number of goals to `e`, short-circuiting if any of them fails.
(define-syntax bindG*
  (syntax-rules ()
    [(_ e) e]
    [(_ e g0 g ...) (bindG* (bindG e g0) g ...)]))

; produces a function that takes `a` and produces an `inc` (which provides laziness) wrapped around
; a stream of the provided clauses as goals applied to `a`.
(define-syntax conde
  (syntax-rules ()
    [(_ (g0 g ...) (g1 ĝ ...) ...)
     (λG (a) (inc (mplusG* (bindG* (g0 a) g ...) (bindG* (g1 a) ĝ ...) ...)))]))

; extend the substitution s with the pair (x . v)
(define (ext-s x v s)
  (cons `(,x . ,v) s))

; oc stands for "operator constraint"
(define (oc->proc oc)
  (car oc))
(define (oc->rator oc)
  (car (cdr oc)))
(define (oc->rands oc)
  (cdr (cdr oc)))
(define (oc->prefix oc)
  (car (oc->rands oc)))

; Not portable to r6rs, but easy to read in the world of Racket
(struct variable (name)
  #:transparent
  #:guard (λ (name _)
            (unless (symbol? name)
              (error "variable names must be symbols"))
            name))

(define var variable)
(define var? variable?)
(define eq-var? eq?)

; the empty substitution (a list of no pairs)
(define empty-s '())
(define lhs car)
(define rhs cdr)

; Find the value associated with `w` in `s`, which could be a variable. So to speak, this is a
; shallow walk.
;
; For example, `(walk x (list (y . z) (x . y) (z . 4)))` would find that `x` is
; bound to `y`.
(define (walk u s)
  (cond
    [(not (var? u)) u]
    [(assq u s)
     =>
     (λ (pair) (walk (rhs pair) s))]
    [else u]))

; Find the value associated with `u` in `s`. If the value is a variable, then look up its value
; (recursively) in the original substitution. This is a deep walk.
;
; For example, `(walk x (list (y . z) (x . y) (z . 4)))` would find that `x` is bound to `y`. It
; would then start at the beginning and see that `y` is bound to `z`. Then, it would start at the
; beginning and go to the end and find that `z` is bound to 4.
(define (walk* w s)
  (let ([v (walk w s)])
    (cond
      [(var? v) v]
      [(pair? v) (cons (walk* (car v) s) (walk* (cdr v) s))]
      [else v])))

; detects if x occurs in the result of walking s on v. If so, there is a cycle
; and divergence could result, so return #f.
(define (occurs x v s)
  (let ([v (walk v s)])
    (cond
      [(var? v) (eq-var? v x)]
      [(pair? v) (or (occurs x (car v) s) (occurs x (cdr v) s))]
      [else #f])))

; Take a list of bindings `e` and add them to `s`.
(define (unify e s)
  (cond
    ; if `e` is empty, just return the substitution `s` unchanged.
    [(null? e) s]
    ; otherwise, deconstruct `e` with the pattern `((,u . ,v) . ,e) and do the following:
    [else
     (let loop ([u (caar e)]
                [v (cdar e)]
                [e (cdr e)])
       ; walk `u` and `v` in `s`, shadowing their original bindings with their respective results
       (let ([u (walk u s)]
             [v (walk v s)])
         (cond
           ; if `u` and `v` are the same (pointer equality), recur on the remainder of `e`
           [(eq? u v) (unify e s)]
           ; if `u` is a variable (not a value and not a tree), check that it doesn't occur when
           ; looking up `v` in `s`. If it doesn't, unify `u` and `v` - NB this works regardless of
           ; the form of `v`.
           [(var? u) (and (not (occurs u v s)) (unify e (ext-s u v s)))]
           ; if `v` is a variable, then do the same as the previous case in reverse.
           ; occurs is still applicable because `u` could be a tree.
           [(var? v) (and (not (occurs v u s)) (unify e (ext-s v u s)))]
           ; if both are trees, recur
           [(and (pair? u) (pair? v)) (loop (car u) (car v) `((,(cdr u) . ,(cdr v)) . ,e))]
           ; otherwise, check for _structural_ equality on `u` and `v`.
           ; I'm not certain when this case is ever useful, TBH.
           [(equal? u v) (unify e s)]
           ; failing all of these cases, `u` and `v` cannot be unified. Fail.
           [else #f])))]))

; called #s in the papers
(define succeed (== #f #f))
; called #u in the papers
(define fail (== #f #t))

; this appears to be the same as the `exist` defined in Will's dissertation
(define-syntax fresh
  (syntax-rules ()
    [(_ (x ...) g0 g ...) (λG (a) (inc (let* ([x (var 'x)] ...) (bindG* (g0 a) g ...))))]))

(define size-s length)

(define (reify-s v s)
  (let ([v (walk v s)])
    (cond
      [(var? v) (ext-s v (reify-n (size-s s)) s)]
      [(pair? v) (reify-s (cdr v) (reify-s (car v) s))]
      [else s])))

; produce a symbol representing a reified logic variable of the form `_.n`
(define (reify-n n)
  (string->symbol (string-append "_." (number->string n))))

; a thunk wrapping an empty stream
(define empty-f (λF () (mzeroG)))

(define (reify x)
  (fresh ()
         ((enforce-constraints) x)
         (λG (a : s d c)
             ; why make a choice here instead of a unit? `empty-f` is literally just a λ wrapped
             ; around the empty stream
             ; Maybe it's this? "We wrap the result of (reify x s) in a list so that the case∞ in
             ; take can distinguish a singleton a∞ from the other three a∞ types."
             (choiceG (let* ([v (walk* x s)]
                             [r (reify-s v empty-s)])
                        (cond
                          [(null? r) v]
                          [else
                           (let ([v (walk* v r)])
                             (cond
                               [(null? c) v]
                               [else (((reify-constraints) v r) a)]))]))
                      empty-f))))

; Before using `n` as an integer, we use `and` to ensure that it is not `#f`
; Take gathers up to `n` elements from a stream and returns them in a list.
(define (take n f)
  (cond
    [(and n (zero? n)) '()]
    [else
     (case∞ (f)
            ; if the stream is empty, return an empty
            [() '()]
            ; if the stream is an `inc`, invoke it and `take` `n` elements from it
            [(f) (take n f)]
            ; if the stream is a `unit`, make it into a list of length 1
            [(a) (cons a '())]
            ; if it's a `choice`, then extract the value and recur (exactly as one expects from
            ; `take`).
            [(a f) (cons a (take (and n (- n 1)) f))])]))

(define empty-d '())
(define empty-c '())
(define empty-package (package empty-s empty-d empty-c))

(define-syntax run
  (syntax-rules ()
    [(_ n (x) g0 g ...) (take n (λF () ((fresh (x) g0 g ... (reify x)) empty-package)))]))
(define-syntax run*
  (syntax-rules ()
    [(_ (x) g0 g ...) (run #f (x) g0 g ...)]))

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
