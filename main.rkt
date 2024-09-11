#lang racket

(require "ckanren.rkt" "minikanren.rkt")


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

(define anyo
  (λ (g)
     (conde
       [g]
       [(anyo g)])))

(define (use-FD)
  (process-prefix process-prefix-FD)
  (enforce-constraints enforce-constraints-FD)
  (reify-constraints reify-constraints-FD))

(use-FD)

(run* (q) (=/=fd q 2) (domfd q '(1 2 3 4 5)))
