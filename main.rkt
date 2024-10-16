#lang racket

(require "ckanren.rkt"
         "minikanren.rkt")

(define anyo (λ (g) (conde [g] [(anyo g)])))

(use-FD)

(define term-count 8)
#;(define term-count 3)
(define terms (inclusive-range 1 term-count))
(define term-max-credits 18)
(define term-min-credits 12)

(define-syntax one-course
  (syntax-rules ()
    [(_ (course credits))
     (let ([term (var 'term)])
       (fresh (term)
              (== course `('course . (,term . ,credits)))
              (domfd term terms)
              (domfd credits (inclusive-range 1 term-max-credits))))]))

(define-syntax courses-goal
  (syntax-rules ()
    [(_ (course credit) ...) (fresh () (one-course (course credit)) ...)]))

(define (prerequisite pre post)
  (fresh (pre-term post-term _pre-name _post-name _pre-credits _post-credits)
         (== pre `(,_pre-name . (,pre-term . ,_pre-credits)))
         (== post `(,_post-name . (,post-term . ,_post-credits)))
         (<fd pre-term post-term)))

(define (add-credits credits term-index inits result)
  (fresh (pre-total pre-totals post-total post-totals)
         (domfd post-total (inclusive-range 1 term-max-credits))
         (domfd term-index terms)
         (== inits `(,pre-total . ,pre-totals))
         (conde [(== term-index 1) (+fd pre-total credits post-total) (== post-totals pre-totals)]
                [(fresh (next-term-index)
                        (domfd next-term-index terms)
                        (+fd next-term-index 1 term-index)
                        (add-credits credits next-term-index pre-totals post-totals)
                        (== post-total pre-total))])
         (== result `(,post-total . ,post-totals))))

(define (credit-totals schedule totals)
  (term-totals schedule (build-list term-count (λ (_) 0)) totals))

; not intended to be part of the public API; use `credit-totals`
(define (term-totals schedule inits totals)
  (conde [(== schedule '()) (== inits totals)]
         [(fresh (_name term credits schedule-rest mid-result)
                 (== schedule `((,_name . (,term . ,credits)) . ,schedule-rest))
                 (add-credits credits term inits mid-result)
                 (term-totals schedule-rest mid-result totals))]))

#|
(run 1
     (result)
     (fresh (cs-1400 cs-1410 cs-2420 schedule totals)
            (courses-goal (cs-1400 3) (cs-1410 3) (cs-2420 3))
            (prerequisite cs-1400 cs-1410)
            (prerequisite cs-1410 cs-2420)
            (credit-totals schedule totals)
            (== schedule (list cs-1400 cs-1410 cs-2420))
            (== result `(,schedule ,totals))))
|#

(run 1
     (result)
     (fresh (engl-1010 engl-2010
                       math-1210
                       hist-1700
                       phil-2050
                       hlth-1100
                       comm-1020
                       comm-2110
                       fa-dist
                       bio-dist
                       phys-dist
                       biol-1610
                       biol-1615
                       ; core
                       cs-1400
                       cs-1410
                       cs-2300
                       cs-2370
                       cs-2420
                       cs-2450
                       cs-2550
                       cs-2600
                       cs-2810
                       cs-305g
                       cs-3060
                       cs-3100
                       cs-3240
                       cs-3520
                       stat-2050
                       ; emphasis
                       cs-3370
                       cs-3310
                       cs-3450
                       cs-4380
                       cs-4450
                       cs-4470
                       cs-4490
                       ; electives
                       cs-3410
                       cs-3320
                       cs-3530
                       cs-3660
                       cs-3720
                       schedule
                       totals)
            (courses-goal ; general education
             (engl-1010 3)
             (engl-2010 3)
             (math-1210 4)
             (hist-1700 3)
             (phil-2050 3)
             (hlth-1100 2)
             (comm-1020 3)
             (comm-2110 3)
             (fa-dist 3)
             (bio-dist 3)
             (phys-dist 3)
             (biol-1610 4)
             (biol-1615 1)
             ; core
             (cs-1400 3)
             (cs-1410 3)
             (cs-2300 3)
             (cs-2370 3)
             (cs-2420 3)
             (cs-2450 3)
             (cs-2550 3)
             (cs-2600 3)
             (cs-2810 3)
             (cs-305g 3)
             (cs-3060 3)
             (cs-3100 3)
             (cs-3240 3)
             (cs-3520 3)
             (stat-2050 4)
             ; emphasis
             (cs-3370 3)
             (cs-3310 3)
             (cs-3450 3)
             (cs-4380 3)
             (cs-4450 3)
             (cs-4470 3)
             (cs-4490 3)
             ; electives
             (cs-3410 3)
             (cs-3320 3)
             (cs-3530 3)
             (cs-3660 3)
             (cs-3720 3))
            (prerequisite engl-1010 engl-2010)
            (prerequisite cs-1400 cs-1410)
            (prerequisite cs-1410 cs-2300)
            (prerequisite cs-1410 cs-2370)
            (prerequisite cs-1410 cs-2420)
            (prerequisite cs-2300 cs-2450)
            (prerequisite cs-2420 cs-2450)
            (prerequisite cs-1410 cs-2550)
            (prerequisite cs-2810 cs-2600)
            (prerequisite cs-1400 cs-2810)
            (prerequisite cs-1400 cs-305g)
            (prerequisite engl-2010 cs-305g)
            (prerequisite cs-2370 cs-3060)
            (prerequisite cs-2420 cs-3060)
            (prerequisite cs-2450 cs-3060)
            (prerequisite cs-2810 cs-3060)
            (prerequisite cs-2420 cs-3100)
            (prerequisite cs-2450 cs-3100)
            (prerequisite cs-2300 cs-3240)
            (prerequisite cs-2420 cs-3240)
            (prerequisite cs-2810 cs-3240)
            (prerequisite cs-3310 cs-2450)
            (prerequisite math-1210 cs-3320)
            (prerequisite cs-2370 cs-3370)
            (prerequisite cs-2450 cs-3370)
            (prerequisite cs-2810 cs-3370)
            (prerequisite cs-2450 cs-3410)
            (prerequisite cs-3370 cs-3450)
            (prerequisite cs-2450 cs-3520)
            (prerequisite cs-3520 cs-3530)
            (prerequisite cs-2420 cs-3660)
            (prerequisite cs-2450 cs-3660)
            (prerequisite cs-2550 cs-3660)
            (prerequisite cs-3520 cs-3720)
            (credit-totals schedule totals)
            (== schedule
                (list engl-1010
                      engl-2010
                      math-1210
                      hist-1700
                      phil-2050
                      hlth-1100
                      comm-1020
                      comm-2110
                      fa-dist
                      bio-dist
                      phys-dist
                      biol-1610
                      biol-1615
                      ; core
                      cs-1400
                      cs-1410
                      cs-2300
                      cs-2370
                      cs-2420
                      cs-2450
                      cs-2550
                      cs-2600
                      cs-2810
                      cs-305g
                      cs-3060
                      cs-3100
                      cs-3240
                      cs-3520
                      stat-2050
                      ; emphasis
                      cs-3370
                      cs-3310
                      cs-3450
                      cs-4380
                      cs-4450
                      cs-4470
                      cs-4490
                      ; electives
                      cs-3410
                      cs-3320
                      cs-3530
                      cs-3660
                      cs-3720))
            (== result `(,schedule ,totals))))
