#lang racket
(require "../racket-utils/set-utilities.rkt")
(provide FlowAnalysis BP CFA2)

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
                              state-equal? join gte state-similar?
                              NextStates/Flow NextStatesAcross/Flow)
                flow-analysis)

  (define (bp-similar? bp1 bp2)
    (match-define (BP open1 node1) bp1)
    (match-define (BP open2 node2) bp2)
    (and (state-similar? open1 open2)
         (state-similar? node1 node2)))

  (define (bp-gte bp1 bp2)
    (match-define (BP open1 node1) bp1)
    (match-define (BP open2 node2) bp2)
    (and (bp-similar? bp1 bp2)
         (gte open1 open2)
         (gte node1 node2)))

  (define (bp-join bp1 bp2)
    (match-define (BP open1 node1) bp1)
    (match-define (BP open2 node2) bp2)
    (unless (bp-similar? bp1 bp2)
      (error 'bp-join "must supply two similar states"))
    (BP (join open1 open2)
        (join node1 node2)))

  (define (set-add/fv s bp)
    (match-define (BP open node) bp)

    (let ((set-bp (for/first ([bp~ (in-set s)]
                              #:when (bp-similar? bp~ bp))
                    bp~)))
      (cond [(false? set-bp) (set-add s bp)]
            [(bp-gte set-bp bp) s]
            [else (set-add (set-remove s set-bp)
                           (bp-join set-bp bp))])))

  (define (loop W Paths Summaries Callers)
    (if (set-empty? W)
        Paths
        (let-values (((task W) (set-get-one/rest W)))
          (match task
            ((BP open (? close? close))
             (let-values (((W Paths)
                           (for/fold ([W W]
                                      [Paths Paths])
                                     ([call (in-set Callers)]
                                      #:when (match call
                                               ((BP gf open~)
                                                (state-similar? open open~))))
                             (match call
                               ((BP grandfather-open _)
                                (PropagateAcross grandfather-open open close
                                                 W Paths))))))

               (loop W Paths (set-add/fv Summaries task) Callers)))
            ((BP open1 (? open? open2))
             (let-values (((W Paths)
                           (let ((relevant-summaries
                                  (for/fold ([relevant-summaries (set)])
                                      ([summary (in-set Summaries)]
                                       #:when (match summary
                                                ((BP open~ close~)
                                                 (gte open~ open2))))
                                    (set-add relevant-summaries summary))))
                             (if (set-empty? relevant-summaries)
                                 (propagate-loop open2 (NextStates/Flow open2)
                                                 W Paths)
                                 (for/fold ([W W]
                                            [Paths Paths])
                                     ([summary (in-set relevant-summaries)])
                                   (match summary
                                     ((BP open~ close~)
                                      (PropagateAcross open1 open~ close~ W Paths))))))))
               (loop W Paths Summaries (set-add/fv Callers task))))
            ((BP open node)
             (let-values (((W Paths)
                           (propagate-loop open (NextStates/Flow node)
                                           W Paths)))
               (loop W Paths Summaries Callers)))))))

  ;; Propogate : OpenFState FState W Paths -> W Paths
  (define (Propagate open node W Paths)
    (define bp (BP open node))

    (let ((set-bp (for/first ([bp~ (in-set Paths)]
                              #:when (bp-similar? bp~ bp))
                    bp~)))
      (cond [(false? set-bp)    (values (set-add W bp) (set-add Paths bp))]
            [(bp-gte set-bp bp) (values W Paths)]
            [else (let ((joined-bp (bp-join set-bp bp)))
                    (values (set-add (set-remove W set-bp) joined-bp)
                            (set-add (set-remove Paths set-bp) joined-bp)))])))

  ;; PropogateAcross : FState FState State W Paths -> W Paths
  (define (PropagateAcross grandfather-open open close W Paths)
    (propagate-loop grandfather-open (NextStatesAcross/Flow open close) W Paths))

  ;; propagate-loop : FState [SetOf FState] W Paths -> W Paths
  (define (propagate-loop push succs W Paths)
    (for/fold ([W W]
               [Paths Paths])
        ([s (in-set succs)])
      (Propagate push s W Paths)))

  (let-values (((W Paths)
                (propagate-loop initial-state
                                (NextStates/Flow initial-state)
                                (set)
                                (set))))
    (loop W Paths (set) (set))))
