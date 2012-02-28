#lang racket
(require "cfa2.rkt")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Structures

(define-struct flow-state (astate flow) #:transparent)
(define-struct abstract-state (node re st) #:transparent)
(define-struct node (uid) #:transparent)
(define-struct (push-node node) (symbol) #:transparent)
(define-struct (pop-node node) (reg) #:transparent)
(define-struct (noop-node node) () #:transparent)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Common Fucntions
;;
;; functions which are used by more than one flow analysis

(define (push? flow-state)
  (push-node? (abstract-state-node (flow-state-astate flow-state))))
(define (pop? flow-state)
  (pop-node? (abstract-state-node (flow-state-astate flow-state))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Minimum Headroom
;;
;; computes the minimum amount of headroom which will be accesible before
;; execution of the given state
(define (min-headroom)
  (define join
    (match-lambda*
      [(list (flow-state s1 f1) (flow-state s1 f2))
       (flow-state s1 (min f1 f2))]))
  (define gte
    (match-lambda*
      [(list (flow-state s1 f1) (flow-state s1 f2))
       (<= f1 f2)]
      [(list (flow-state _ _) (flow-state _ _)) #f]))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Previous States
;;
;; Computes the reverse state graph
(define (prev-states)
  (define join
    (match-lambda*
      [(list (flow-state s1 f1) (flow-state s1 f2))
       (flow-state s1 (set-union f1 f2))]))
  (define gte
    (match-lambda*
      [(list (flow-state s1 f1) (flow-state s1 f2))
       (subset? f2 f1)]
      [(list (flow-state _ _) (flow-state _ _)) #f]))

  (define (succ-states/flow fstate)
    (match-define (flow-state astate fv) fstate)

    (for/set ([astate~ (in-set (succ-states astate))])
      (flow-state astate~ (set astate))))

  (define (pop-succ-states/flow push-fstate pop-fstate)
    (match-define (flow-state push-astate _) push-fstate)
    (match-define (flow-state pop-astate _) pop-fstate)

    (for/set ([astate~ (in-set (pop-succ-states push-astate pop-astate))])
      (flow-state astate~ (set pop-astate))))

  (define initial-abstract-state (abstract-state (uid->node 1) (hash) 'ε))

  (FlowAnalysis (flow-state initial-abstract-state (set))
                push? pop? state-equal?
                join gte state-similar?
                succ-states/flow pop-succ-states/flow))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Minimum Needed
;;
;; A backwards flow analysis which computes the minimum amount of headroom which
;; will be needed after execution of this
(define (min-needed)
  (define reverse-state-graph
    (hash
     (abstract-state (push-node 3 'b) '#hash() 'c)
     (set (abstract-state (noop-node 2) '#hash() 'c))
     (abstract-state (noop-node 2) '#hash() 'c)
     (set (abstract-state (noop-node 5) '#hash() 'c))
     (abstract-state (noop-node 8) '#hash((r2 . b) (r1 . c)) 'a)
     (set (abstract-state (pop-node 7 'r2) '#hash((r1 . c)) 'b))
     (abstract-state (push-node 4 'c) '#hash() 'b)
     (set
      (abstract-state (push-node 3 'b) '#hash() 'c)
      (abstract-state (push-node 3 'b) '#hash() 'a))
     (abstract-state (push-node 3 'b) '#hash() 'a)
     (set (abstract-state (noop-node 2) '#hash() 'a))
     (abstract-state (pop-node 10 'r3) '#hash((r2 . b) (r1 . c)) 'a)
     (set (abstract-state (noop-node 9) '#hash((r2 . b) (r1 . c)) 'a))
     (abstract-state (noop-node 2) '#hash() 'a)
     (set (abstract-state (push-node 1 'a) '#hash() 'ε))
     (abstract-state (noop-node 9) '#hash((r2 . b) (r1 . c)) 'a)
     (set (abstract-state (noop-node 8) '#hash((r2 . b) (r1 . c)) 'a))
     (abstract-state (pop-node 6 'r1) '#hash() 'c)
     (set (abstract-state (noop-node 5) '#hash() 'c))
     (abstract-state (pop-node 7 'r2) '#hash((r1 . c)) 'b)
     (set (abstract-state (pop-node 6 'r1) '#hash() 'c))
     (abstract-state (push-node 1 'a) '#hash() 'ε)
     (set)
     (abstract-state (noop-node 5) '#hash() 'c)
     (set (abstract-state (push-node 4 'c) '#hash() 'b))))

  (define join
    (match-lambda*
      [(list (flow-state s1 f1) (flow-state s1 f2))
       (flow-state s1 (min f1 f2))]))
  (define gte
    (match-lambda*
      [(list (flow-state s1 f1) (flow-state s1 f2))
       (<= f1 f2)]
      [(list (flow-state _ _) (flow-state _ _)) #f]))

  (define (next-flow fstate)
    (match-define (flow-state _ flow) fstate)

    (cond [(push? fstate) (add1 flow)]
          [(pop? fstate)  (max (sub1 flow) 0)]
          [else flow]))

  (define (prev-states st)
    (hash-ref reverse-state-graph st))
  (define (push-prev-states pop push)
    (hash-ref reverse-state-graph push))

  (define (prev-states/flow fstate)
    (match-define (flow-state astate fv) fstate)

    (for/set ([astate~ (in-set (prev-states astate))])
      (flow-state astate~ (next-flow fstate))))

  (define (push-prev-states/flow pop-fstate push-fstate)
    (prev-states/flow push-fstate))

  (FlowAnalysis (flow-state (abstract-state (pop-node 10 'r3) '#hash((r2 . b)
                                                                     (r1 . c))
                                            'a)
                            0)
                push? pop? state-equal?
                join gte state-similar?
                prev-states/flow push-prev-states/flow))

(require rackunit
         rackunit/text-ui
         "utilities.rkt")


(define-test-suite cfa2-tests
  (test-case
   "CFA2 min-headroom"
   (define Paths (CFA2 (min-headroom)))
   (check-equal?  (bpset->fv-hash Paths
                                  (lambda (fstate)
                                    (match fstate
                                      ((flow-state astate fv) (values astate fv))))
                                  min
                                  +inf.0)
                  (hash
                   (abstract-state (push-node 1 'a) '#hash() 'ε)
                   5.0
                   (abstract-state (noop-node 2) '#hash() 'c)
                   0.0
                   (abstract-state (noop-node 2) '#hash() 'a)
                   4.0
                   (abstract-state (push-node 3 'b) '#hash() 'c)
                   0.0
                   (abstract-state (push-node 3 'b) '#hash() 'a)
                   4.0
                   (abstract-state (push-node 4 'c) '#hash() 'b)
                   0.0
                   (abstract-state (noop-node 5) '#hash() 'c)
                   0.0
                   (abstract-state (pop-node 6 'r1) '#hash() 'c)
                   0.0
                   (abstract-state (pop-node 7 'r2) '#hash((r1 . c)) 'b)
                   1.0
                   (abstract-state (noop-node 8) '#hash((r1 . c) (r2 . b)) 'a)
                   4.0
                   (abstract-state (noop-node 8) '#hash((r1 . c) (r2 . b)) 'c)
                   2.0
                   (abstract-state (noop-node 9) '#hash((r1 . c) (r2 . b)) 'a)
                   4.0
                   (abstract-state (noop-node 9) '#hash((r1 . c) (r2 . b)) 'c)
                   2.0
                   (abstract-state (pop-node 10 'r3) '#hash((r1 . c) (r2 . b) (r3 . b)) 'a)
                   4.0
                   (abstract-state (pop-node 10 'r3) '#hash((r1 . c) (r2 . b)) 'c)
                   2.0
                   (abstract-state (pop-node 10 'r3) '#hash((r1 . c) (r2 . b) (r3 . b)) 'c)
                   4.0
                   (abstract-state (pop-node 10 'r3) '#hash((r1 . c) (r2 . b) (r3 . c)) 'b)
                   3.0
                   (abstract-state (pop-node 10 'r3) '#hash((r1 . c) (r2 . b)) 'a)
                   4.0))))

(run-tests cfa2-tests)
