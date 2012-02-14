#lang racket

(define-syntax-rule (apply-to-values p generator)
  (call-with-values (lambda () generator) p))

(define-struct BP (open node) #:transparent)
;; BP : OpenState × State


;; W : [SetOf BP]
;; Paths : [SetOf BP]

(define-struct Analysis
  (initial-state NextStates NextStatesAcross open? close? state-equal? flow-analysis))
;; An Analysis is a
;;   (Analysis [State -> [SetOf State]]
;;             [State -> Boolean]
;;             [State -> Boolean]
;;             [State State -> Boolean])
;;             [FlowAnalysis State])

(define-struct FlowAnalysis
  (join gte FlowTransfer FlowTransferAcross initial-flow-value default-flow-value))

;; the states in the BPs of  the Worklist and Paths 
(define-struct StateWithFlow (state fi))

;; CFA2 : Analysis
;;        ->
;;        Paths
(define (CFA2 analysis)
  (match-define (Analysis initial-state NextStates _ open? close? state-equal?
                          (FlowAnalysis _ gte FlowTransfer _ initial-flow-value default-flow-value))
                analysis)

  (define (loop W Paths FlowInfo)
    (define (get-flow-info s)
      (hash-ref FlowInfo s default-flow-value))

    (if (set-empty? W)
        (values Paths FlowInfo)
        (let-values (((task W) (set-get-one/rest W)))
          (apply-to-values
           loop
           (match task
             ((BP open (? close? close))
              (for/fold ([W W]
                         [Paths Paths]
                         [FlowInfo FlowInfo])
                        ([call (in-set Paths)]
                         #:when (match call
                                  ((BP gf open~)
                                   (state-equal? open open~))))
                (match call
                  ((BP grandfather-open _)
                   (PropagateAcross grandfather-open open close W Paths FlowInfo analysis)))))
             ((BP open1 (? open? open2))
              (if (for/or ([sum (in-set Paths)])
                          (match sum
                            ((BP open~ close~)
                             (and (state-equal? open2 open~)
                                  (close? close~)
                                  (gte (flow-value-old (get-flow-info open2))
                                       (flow-value-new (get-flow-info open2)))))))
                  (for/fold
                      ([W W]
                       [Paths Paths]
                       [FlowInfo FlowInfo])
                      ([sum (in-set Paths)]
                       #:when
                       (match sum
                         ((BP open~ close~)
                          (and (state-equal? open2 open~)
                               (close? close~)))))
                    (match sum
                      ((BP open~ close~)
                       (PropagateAcross open1 open2 close~ W Paths FlowInfo analysis))))
                  (PropagateOpen open2 W Paths FlowInfo)))
             ((BP open node)
              (propagate-loop open (NextStates node) (FlowTransfer node)
                              W Paths FlowInfo analysis)))))))
 (apply-to-values loop
                   (propagate-loop initial-state
                                   (NextStates initial-state)
                                   (set)
                                   (set))))


;; Propogate : OpenState State FI W Paths FlowInfo analysis -> W Paths
(define (Propagate open node fi W Paths FlowInfo analysis)
  (match-define (Analysis _ _ _ open? _ _
                          (FlowAnalysis join _ _ _ _ _)) analysis)
  (if (set-member? Paths (BP open node))
      (values W Paths)
      (values (set-add W (BP open node))
              (set-add Paths (BP open node))
              (hash-set FlowInfo node
                        (if (open? node)
                            (flow-value (join fi
                                              (flow-value-new
                                               (hash-ref FlowInfo node)))
                                        (flow-value-new
                                         (hash-ref FlowInfo node)))
                            (join fi (hash-ref FlowInfo node)))))))

;; PropogateAcross : State State State W Paths Analysis -> W Paths
(define (PropagateAcross grandfather-open open close W Paths analysis)
  (match-define (Analysis _ _ NextStatesAcross _ _ _
                          (FlowAnalysis join _ _ _ _ _)) analysis)
  (propagate-loop grandfather-open (NextStatesAcross open close) W Paths))

;; propagate-loop : State [SetOf State] W Paths -> W Paths
(define (propagate-loop push succs W Paths)
  (for/fold ([W W]
             [Paths Paths])
            ([s (in-set succs)])
    (let-values (((W~ Paths~) (Propagate push s W Paths)))
      (values (set-union W W~)
              (set-union Paths Paths~)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests

(define (reachability)
  (define-struct State (node env astack) #:transparent)
  (define-struct PushNode (value id) #:transparent)
  (define-struct PopNode (var id) #:transparent)
  (define-struct Noop (id) #:transparent)


  (define push?
    (match-lambda ((State node _ _)
                   (PushNode? node))))
  (define pop?
    (match-lambda ((State node _ _)
                   (PopNode? node))))
  (define state-equal? equal?)
  (define (succ-nodes node)
    (hash-ref (hash (PushNode 'a 0) (set (Noop 1))
                    (Noop 1) (set (PushNode 'b 2))
                    (PushNode 'b 2) (set (PushNode 'c 3))
                    (PushNode 'c 3) (set (Noop 4))
                    (Noop 4) (set (PopNode 'var1 5) (PushNode 'b 2))
                    (PopNode 'var1 5) (set (PopNode 'var2 6))
                    (PopNode 'var2 6) (set (Noop 7))
                    (Noop 7) (set (Noop 8))
                    (Noop 8) (set (PopNode 'var3 9))
                    (PopNode 'var3 9) (set (PopNode 'var3 9)))
              node))
  (define (succ-states state)
    (match-let (((State node env astack) state))
      (match node
        ((PushNode value _) (for/set ([succ-node (succ-nodes node)])
                              (State succ-node env value)))
        (_ (for/set ([succ-node (succ-nodes node)])
             (State succ-node env astack))))))
  (define (pop-succ-states push pop)
    (match-let (((State push-node _ previous-stack) push)
                ((State pop-node env current-stack) pop))
      (match-let (((PopNode var _) pop-node))
        (for/set ([succ-node (succ-nodes pop-node)])
          (State succ-node
                 (update-env env var current-stack)
                 previous-stack)))))
  (define (update-env env var val)
    (hash-set env var (set-add (hash-ref env var (set)) val)))
  (Analysis (State (PushNode 'a 0) (hash) 'ε)
            succ-states
            pop-succ-states
            push?
            pop?
            state-equal?))

(CFA2 (reachability))

(define simple-reachability
  (let* ([push? (lambda (s)
                  (set-member? (set 1 3 4) s))]
         [pop? (lambda (s)
                 (set-member? (set 6 7 10) s))]
         [state-equal? (lambda (s1 s2)
                         (= s1 s2))]
         [succ-states (lambda (s)
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
                                  s))]
         [pop-succ-states (lambda (push pop)
                            (succ-states pop))])
    (Analysis 1 succ-states pop-succ-states push? pop? state-equal?)))

(CFA2 simple-reachability)


(require rackunit
         rackunit/text-ui)

(define-test-suite cfa2-tests
  (test-case
   "CFA2 simple-reachability"
   (define Paths (CFA2 simple-reachability))
   (check-true (set=? (set (Open 1) (Open 3) (Open 4) (BP 1 8) (BP 3 4)
                           (BP 4 5) (BP 1 9) (BP 1 2) (BP 1 3)
                           (BP 4 6) (BP 1 10) (BP 3 7))
                      Paths))))

(run-tests cfa2-tests)
