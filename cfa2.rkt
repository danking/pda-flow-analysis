#lang racket
(provide FlowAnalysis BP CFA2)

(define (set-get-one/rest s)
  (let ((e (for/first ((e (in-set s))) e)))
    (values e (set-remove s e))))

(define-syntax my-for/first
  (syntax-rules ()
    ((for/first ((id clause) when-clauses ...)
       body)
     (let ((id (for/first ((id clause) when-clauses ...) id)))
       body))))

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
      (my-for/first ([bp (in-set Paths)]
                     #:when (match bp
                              ((BP open~ node~)
                               (and (state-similar? open open~)
                                    (state-similar? node node~)))))
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


