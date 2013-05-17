#lang racket
(require ; "../racket-utils/set-utilities.rkt"
         "../racket-utils/similar-sets.rkt"
         "../racket-utils/multi-access-sets.rkt"
         "../racket-utils/option.rkt"
         "../racket-utils/partitioned-sets.rkt"
         (prefix-in basic- racket/set))
(provide FlowAnalysis BP CFA2)

(define-struct BP (open node) #:transparent)
;; BP : OpenState × State

;; W : [SetOf BP]
;; Paths : [SetOf BP]

(define-struct FlowAnalysis
  (initial-state open? close? state-equal?
                 join gte state-similar? state-hash-code
                 NextStates/Flow NextStatesAcross/Flow))
;; A FlowAnalysis is a
;;   (FlowAnalysis FState
;;                 [FState -> Boolean]
;;                 [FState -> Boolean]
;;                 [FState FState -> Boolean]
;;                 [FState FState -> FState]
;;                 [FState FState -> Boolean]
;;                 [FState FState -> Number]
;;                 [FState -> FState]
;;                 [FState FState -> Fstate])


;; CFA2 : Analysis
;;        ->
;;        Paths
(define (CFA2 flow-analysis #:debug [debug 0])
  (match-define (FlowAnalysis initial-state open? close?
                              state-equal? join gte state-similar? state-hash-code
                              NextStates/Flow NextStatesAcross/Flow)
                flow-analysis)

  (define (bp-equal? bp1 bp2)
    (match-define (BP open1 node1) bp1)
    (match-define (BP open2 node2) bp2)
    (and (state-equal? open1 open2)
         (state-equal? node1 node2)))

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

  (define (bp-hash-code bp)
    (match-define (BP open node) bp)
    (+ (state-hash-code open) (state-hash-code node)))

  (define empty-W/Paths-set
    (set bp-join bp-equal? bp-similar? bp-hash-code))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Callers Set
  (define (get-callers Callers open)
    (pset-equivclass-partition Callers (BP #f open)))

  (define (similar-callee? bp1 bp2)
    (match-define (BP open1 node1) bp1)
    (match-define (BP open2 node2) bp2)

    (state-similar? node1 node2))

  (define empty-Callers-set
    (make-partitioned-set similar-callee?
                          (compose state-hash-code BP-node)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Summaries Set
  (define (get-summaries Summaries open)
    (pset-equivclass-partition Summaries (BP open #f)))

  (define (similar-caller? bp1 bp2)
    (match-define (BP open1 node1) bp1)
    (match-define (BP open2 node2) bp2)

    (state-similar? open1 open2))

  (define empty-Summaries-set
    (make-partitioned-set similar-caller?
                          (compose state-hash-code BP-open)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define (loop W Paths Summaries Callers)
    (match (set-get-one/rest W)
      ((none) (values Paths Summaries Callers))
      ((some (list task W))
       (dprint "[loop] investigating: ~v\n" task)
       (match task
         ((BP open (? close? close))
          (log-info "summary ~a to ~a" open close)
          (let-values (((W Paths)
                        (for/fold ([W W]
                                   [Paths Paths])
                                  ([call (get-callers Callers open)])
                          (match call
                            ((BP grandfather-open _)
                             (PropagateAcross grandfather-open open close
                                              W Paths))))))

            (loop W Paths (pset-add Summaries task) Callers)))
         ((BP open1 (? open? open2))
          (log-info "call ~a to ~a" open1 open2)
          (let-values (((W Paths)
                        (let ((summaries (get-summaries Summaries open2)))
                          (if (basic-set-empty? summaries)
                              (begin (log-info "No summaires found for ~a to ~a"
                                               open1 open2)
                                     (propagate-loop open2 (NextStates/Flow open2)
                                                     W Paths))
                              (for/fold ([W W]
                                         [Paths Paths])
                                  ([summary summaries])
                                (match summary
                                  ((BP open~ close~)
                                   (PropagateAcross open1 open~ close~ W Paths))))))))
            (loop W Paths Summaries (pset-add Callers task))))
         ((BP open node)
          (log-info "step ~a to ~a" open node)
          (let-values (((W Paths)
                        (propagate-loop open (NextStates/Flow node)
                                        W Paths)))
            (loop W Paths Summaries Callers)))))))

  ;; Propogate : OpenFState FState W Paths -> W Paths
  (define (Propagate open node W Paths)
    (let ((bp (BP open node)))
      (match (set-get-similar Paths bp)
        ((some similar-bp)
         (if (bp-gte similar-bp bp)
             (begin (log-info "nothing changed ~a to ~a" open node)
                    (values W Paths))
             (values (set-add W bp) (set-add Paths bp))))
        (_ (values (set-add W bp) (set-add Paths bp))))))

  ;; PropogateAcross : FState FState State W Paths -> W Paths
  (define (PropagateAcross grandfather-open open close W Paths)
    (propagate-loop grandfather-open (NextStatesAcross/Flow open close) W Paths))

  ;; propagate-loop : FState [SetOf FState] W Paths -> W Paths
  (define (propagate-loop push succs W Paths)
    (for/fold ([W W]
               [Paths Paths])
        ([s succs])
      (Propagate push s W Paths)))

  (define (dprint . args)
    (when (> debug 0)
      (apply printf args)
      (flush-output)))

  (let-values (((W Paths)
                (propagate-loop initial-state
                                (NextStates/Flow initial-state)
                                empty-W/Paths-set
                                empty-W/Paths-set)))
    (loop W Paths empty-Summaries-set empty-Callers-set)))
