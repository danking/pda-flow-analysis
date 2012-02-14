#lang racket
(require "cfa2.rkt")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests

(define-struct flow-state (astate flow) #:transparent)
(define-struct abstract-state (node re st) #:transparent)
(define-struct node (uid) #:transparent)
(define-struct (push-node node) (symbol) #:transparent)
(define-struct (pop-node node) (reg) #:transparent)
(define-struct (noop-node node) () #:transparent)

(define (simple-min-headroom)
  (define (push? flow-state)
    (push-node? (abstract-state-node (flow-state-astate flow-state))))
  (define (pop? flow-state)
    (pop-node? (abstract-state-node (flow-state-astate flow-state))))
  (define join
    (match-lambda*
      [(list (flow-state s1 f1) (flow-state s1 f2))
       (flow-state s1 (min f1 f2))]))
  (define gte
    (match-lambda*
      [(list (flow-state s1 f1) (flow-state s1 f2))
       (<= f1 f2)]))

  (define state-similar? (match-lambda*
                           [(list (flow-state s1 _)
                                  (flow-state s2 _))
                            (equal? s1 s2)]))
  (define state-equal? equal?)

  (define (uid->node uid)
    (hash-ref (hasheq 1 (push-node 1 'a)
                      2 (noop-node 2)
                      3 (push-node 3 'b)
                      4 (push-node 4 'c)
                      5 (noop-node 5)
                      6 (pop-node 6 'r1)
                      7 (pop-node 7 'r2)
                      8 (noop-node 8)
                      9 (noop-node 9)
                      10 (pop-node 10 'r3))
              uid))
  (define (succ-node node)
    (for/set ([uid (in-set
                    (hash-ref (hasheq 1 (set 2)
                                      2 (set 3)
                                      3 (set 4)
                                      4 (set 5)
                                      5 (set 6 2)
                                      6 (set 7)
                                      7 (set 8)
                                      8 (set 9)
                                      9 (set 10)
                                      10 (set 10))
                              (node-uid node)))])
      (uid->node uid)))
  (define succ-states
    (match-lambda
      [(abstract-state node env astack)
       (for/set ([s~ (in-set (succ-node node))])
         (match node
           [(push-node _ symbol)
            (abstract-state s~ env symbol)]
           [_ (abstract-state s~ env astack)]))]))
  (define (pop-succ-states push pop)
    (match-define (abstract-state _ _ stack-before-push)
                  push)
    (match-define (abstract-state (pop-node uid reg) env stack-after-push)
                  pop)

    (for/set ([node (in-set (succ-node (pop-node uid reg)))])
      (abstract-state node
                      (hash-set env reg stack-after-push)
                      stack-before-push)))

  (define (next-flow fstate)
    (match-define (flow-state _ flow) fstate)

    (cond [(push? fstate) (max (sub1 flow) 0)]
          [(pop? fstate)  (add1 flow)]
          [else flow]))

  (define (succ-states/flow fstate)
    (match-define (flow-state astate fv) fstate)

    (for/set ([astate~ (in-set (succ-states astate))])
      (flow-state astate~ (next-flow fstate))))

  (define (pop-succ-states/flow push-fstate pop-fstate)
    (match-define (flow-state push-astate _) push-fstate)
    (match-define (flow-state pop-astate _) pop-fstate)

    (for/set ([astate~ (in-set (pop-succ-states push-astate pop-astate))])
      (flow-state astate~ (next-flow pop-fstate))))

  (FlowAnalysis (flow-state (abstract-state (uid->node 1) (hash) 'ε) 5)
                push? pop? state-equal?
                join gte state-similar?
                succ-states/flow pop-succ-states/flow))

(CFA2 (simple-min-headroom))

(require rackunit
         rackunit/text-ui)
#;
(define-test-suite cfa2-tests
  (test-case
   "CFA2 simple-min-headroom"
   (define Paths (CFA2 (simple-min-headroom)))
   (check-true (set=? (set (BP (state 1 3) (state 2 2))
                           (BP (state 1 3) (state 3 2))
                           (BP (state 3 2) (state 4 1))
                           (BP (state 4 1) (state 5 0))
                           (BP (state 4 1) (state 6 0))
                           (BP (state 3 2) (state 7 1))
                           (BP (state 1 3) (state 8 2))
                           (BP (state 1 3) (state 9 2))
                           (BP (state 1 3) (state 10 2)))
                      Paths))))
#;
(run-tests cfa2-tests)