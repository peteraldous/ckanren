#lang racket

(require "ckanren.rkt"
         "minikanren.rkt")

(define (map-sum f)
  (letrec ([loop (λ (ls)
                   (cond
                     [(null? ls) fail]
                     [else (conde [(f (car ls))] [(loop (cdr ls))])]))])
    loop))

(define anyo (λ (g) (conde [g] [(anyo g)])))

(define (use-FD)
  (process-prefix process-prefix-FD)
  (enforce-constraints enforce-constraints-FD)
  (reify-constraints reify-constraints-FD))

(use-FD)

(run* (q) (=/=fd q 2) (domfd q '(1 2 3 4 5)))

(run* (q)
      (fresh (x y z)
             (infd z '(1 3 5 6 7 8))
             (== x y)
             (infd y '(3 4 5))
             (== q `(,x ,y ,z))
             (infd z '(5 6 9))
             (infd x '(1 2 3))))
