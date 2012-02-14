#lang racket

(define (set-get-one/rest s)
  (let ((e (for/first ((e (in-set s))) e)))
    (values e (set-remove s e))))

(define-syntax-rule (apply-to-values p generator)
  (call-with-values (lambda () generator) p))

(define-struct BP (open node) #:transparent)
;; BP : OpenState × State


;; W : [SetOf BP]
;; Paths : [SetOf BP]

(define-struct FlowAnalysis
  (initial-state open? close? state-equal?
                 join gte state-similar?
                 NextStates/Flow NextStatesAcross/Flow))
;; A FlowAnalysis is a
;;   (FlowAnalysis FState
;;                 [FState -> Boolean]
;;                 [FState -> Boolean]
;;                 [FState FState -> Boolean]
;;                 [FState FState -> FState]
;;                 [FState FState -> Boolean]
;;                 [FState FState -> Boolean]
;;                 [FState -> FState]
;;                 [FState FState -> Fstate])


;; CFA2 : Analysis
;;        ->
;;        Paths
(define (CFA2 flow-analysis)
  (match-define (FlowAnalysis initial-state open? close?
                              state-equal? _ gte state-similar?
                              NextStates/Flow _)
                flow-analysis)

  (define (loop W Paths)
    (if (set-empty? W)
        Paths
        (let-values (((task W) (set-get-one/rest W)))
          (apply-to-values
           loop
           (match task
             ((BP open (? close? close))
              (for/fold ([W W]
                         [Paths Paths])
                  ([call (in-set Paths)]
                   #:when (match call
                            ((BP gf open~)
                             (state-equal? open open~))))
                (match call
                  ((BP grandfather-open _)
                   (PropagateAcross grandfather-open open close W Paths flow-analysis)))))
             ((BP open1 (? open? open2))
              (if (for/or ([sum (in-set Paths)])
                    (match sum
                      ((BP open~ close~)
                       (and (close? close~)
                            (state-similar? open2 open~) ; is this redundant with gte?
                            (gte open~ open2)))))
                  (for/fold
                      ([W W]
                       [Paths Paths])
                      ([sum (in-set Paths)]
                       #:when
                       (match sum
                         ((BP open~ close~)
                          (and (close? close~)
                               (state-similar? open2 open~) ; is this redundant with gte?
                               (gte open~ open2)))))
                    (match sum
                      ((BP open~ close~)
                       (PropagateAcross open1 open~ close~ W Paths flow-analysis))))
                  (propagate-loop open2 (NextStates/Flow open2)
                                  W Paths flow-analysis)))
             ((BP open node)
              (propagate-loop open (NextStates/Flow node)
                              W Paths flow-analysis)))))))
  (apply-to-values loop
                   (propagate-loop initial-state
                                   (NextStates/Flow initial-state)
                                   (set)
                                   (set)
                                   flow-analysis)))

;; Propogate : OpenFState FState W Paths FlowAnalysis -> W Paths
(define (Propagate open node W Paths flow-analysis)
  (match-define (FlowAnalysis _ _ _ _ join gte state-similar? _ _) flow-analysis)
  (if (for/or ([bp (in-set Paths)])
        (match bp
          ((BP open~ node~)
           (and (state-similar? open open~)
                (state-similar? node node~)))))
      (for/first ([bp (in-set Paths)])
        (match bp
          ((BP open~ node~)
           (if (and (gte open~ open)
                    (gte node~ node))
               (values W Paths)
               (let ((old-pair (BP open~ node~))
                     (new-pair (BP (join open~ open)
                                   (join node~ node))))
                 (values (set-add (set-remove W old-pair) new-pair)
                         (set-add (set-remove Paths old-pair) new-pair)))))))
      (values (set-add W (BP open node))
              (set-add Paths (BP open node)))))

;; PropogateAcross : FState FState State W Paths FlowAnalysis -> W Paths
(define (PropagateAcross grandfather-open open close W Paths flow-analysis)
  (match-define (FlowAnalysis _ _ _ _ _ _ _ _ NextStatesAcross/Flow) flow-analysis)
  (propagate-loop grandfather-open (NextStatesAcross/Flow open close) W Paths flow-analysis))

;; propagate-loop : FState [SetOf FState] W Paths FlowAnalysis -> W Paths
(define (propagate-loop push succs W Paths flow-analysis)
  (for/fold ([W W]
             [Paths Paths])
            ([s (in-set succs)])
    (let-values (((W~ Paths~) (Propagate push s W Paths flow-analysis)))
      (values (set-union W W~)
              (set-union Paths Paths~)))))

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

(CFA2 (simple-min-headroom))

(require rackunit
         rackunit/text-ui)

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

(run-tests cfa2-tests)
