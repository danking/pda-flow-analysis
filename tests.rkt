#lang racket
(require "cfa2.rkt" "bp.rkt")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests

(define-struct state (s flow) #:transparent)

(define (simple-min-headroom)
  (let* ([push? (match-lambda
                  [(state s flow)
                   (set-member? (set 1 3 4) s)])]
         [pop? (match-lambda
                 [(state s flow)
                  (set-member? (set 6 7 10) s)])]
         [join (match-lambda*
                 [(list (state s1 f1) (state s1 f2))
                  (state s1 (min f1 f2))])]
         [gte (match-lambda*
                [(list (state s1 f1) (state s1 f2))
                 (>= f1 f2)])]
         [state-similar? (match-lambda*
                           [(list (state s1 _)
                                  (state s2 _))
                            (= s1 s2)])]
         [state-equal? (match-lambda*
                         [(list (state s1 f1)
                                (state s2 f2))
                          (and (state-similar? (state s1 f1)
                                               (state s2 f2))
                               (= f1 f2))])]
         [next-flow (lambda (s flow)
                      (let ((st (state s flow)))
                        (cond [(push? st) (sub1 flow)]
                              [(pop? st)  (add1 flow)]
                              [else flow])))]
         [succ-node (lambda (node)
                      (hash-ref (hasheq 1 (set 2)
                                        2 (set 3)
                                        3 (set 4)
                                        4 (set 5)
                                        5 (set 6)
                                        6 (set 7)
                                        7 (set 8)
                                        8 (set 9)
                                        9 (set 10)
                                        10 (set))
                                node))]
         [succ-states (match-lambda
                        [(state s flow)
                         (for/set ([s~ (in-set (succ-node s))])
                           (state s~ (next-flow s flow)))])]
         [pop-succ-states (lambda (push pop)
                            (succ-states pop))])
    (FlowAnalysis (state 1 3)
                  push? pop? state-equal?
                  join gte state-similar?
                  succ-states pop-succ-states)))

(define (simple-min-needed)
  (let* ([push? (match-lambda
                  [(state s flow)
                   (set-member? (set 1 3 4) s)])]
         [pop? (match-lambda
                 [(state s flow)
                  (set-member? (set 6 7 10) s)])]
         [join (match-lambda*
                 [(list (state s1 f1) (state s1 f2))
                  (state s1 (min f1 f2))])]
         [gte (match-lambda*
                [(list (state s1 f1) (state s1 f2))
                 (<= f1 f2)])]
         [state-similar? (match-lambda*
                           [(list (state s1 _)
                                  (state s2 _))
                            (= s1 s2)])]
         [state-equal? (match-lambda*
                         [(list (state s1 f1)
                                (state s2 f2))
                          (and (state-similar? (state s1 f1)
                                               (state s2 f2))
                               (= f1 f2))])]
         [next-flow (lambda (s flow)
                      (let ((st (state s flow)))
                        (cond [(push? st) (sub1 flow)]
                              [(pop? st)  (add1 flow)]
                              [else flow])))]
         [prev-node (lambda (node)
                      (hash-ref (hasheq 1 (set)
                                        2 (set 1)
                                        3 (set 2)
                                        4 (set 3)
                                        5 (set 4)
                                        6 (set 5)
                                        7 (set 6)
                                        8 (set 7)
                                        9 (set 8)
                                        10 (set 9))
                                node))]
         [prev-states (match-lambda
                        [(state s flow)
                         (for/set ([s~ (in-set (prev-node s))])
                           (state s~ (next-flow s flow)))])]
         [pop-prev-states (lambda (push pop)
                            (prev-states pop))])
    (FlowAnalysis (state 10 0)
                  pop? push? state-equal?
                  join gte state-similar?
                  prev-states pop-prev-states)))

(require rackunit
         rackunit/text-ui)

(define-test-suite cfa2-tests
  (test-case
   "CFA2 simple-min-headroom"
   (define Paths (CFA2 (simple-min-headroom)))
   (check-equal? Paths
                 (set (BP (state 1 3) (state 2 2))
                      (BP (state 1 3) (state 3 2))
                      (BP (state 3 2) (state 4 1))
                      (BP (state 4 1) (state 5 0))
                      (BP (state 4 1) (state 6 0))
                      (BP (state 3 2) (state 7 1))
                      (BP (state 1 3) (state 8 2))
                      (BP (state 1 3) (state 9 2))
                      (BP (state 1 3) (state 10 2)))))
  (test-case
   "CFA2 simple-min-needed"
   (define Paths (CFA2 (simple-min-needed)))
   (check-equal? Paths
                 (set (BP (state 10 0) (state 9 1))
                      (BP (state 10 0) (state 8 1))
                      (BP (state 10 0) (state 7 1))
                      (BP (state 7 1)  (state 6 2))
                      (BP (state 6 2)  (state 5 3))
                      (BP (state 6 2)  (state 4 3))
                      (BP (state 7 1)  (state 3 2))
                      (BP (state 10 0) (state 2 1))
                      (BP (state 10 0) (state 1 1))))))

(run-tests cfa2-tests)
