#lang racket

(provide (all-defined-out))

; from https://github.com/michaelballantyne/faster-minikanren/blob/master/private-unstable.rkt

(define (find f l)
  (cond
    [(memf f l)
     =>
     car]
    [else #f]))

(define (remp f l)
  (filter-not f l))

(define (list-sort less-than lst)
  (sort lst less-than))

(define (call-with-string-output-port f)
  (define p (open-output-string))
  (f p)
  (get-output-string p))

(define exists ormap)

(define for-all andmap)

(define memp memf)
