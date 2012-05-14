#lang racket
(require ; "../racket-utils/set-utilities.rkt"
         "../racket-utils/similar-sets.rkt"
         "../racket-utils/option.rkt"
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
;;                 [FState FState -> Boolean]
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

  (define empty-W/Paths-set (set bp-join equal? bp-similar? bp-hash-code))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Common to Callers and Summaries
  (define (basic-set-union/singletons-are-sets v1 v2)
    (match (list v1 v2)
      ((list (BP _ _) (BP _ _)) (basic-seteq v1 v2))
      ((or (list (and bp (BP _ _)) a-basic-set)
           (list a-basic-set       (and bp (BP _ _))))
       (basic-set-add a-basic-set bp))
      ((list basic-set1 basic-set2) (basic-set-union basic-set1 basic-set2))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Callers Set
  (define (similar-callee? bp1 bp2)
    (match (list bp1 bp2)
      ((list (BP _ callee1) (BP _ callee2))
       (state-similar? callee1 callee2))))

  (define (callers-hash-code bp)
    (match-define (BP _ callee) bp)
    (equal-hash-code callee))

  (define (get-callers Callers open)
    (match (set-get-similar Callers (BP #f open))
      ((some callers) (if (basic-set-eq? callers) callers (basic-seteq callers)))
      ((none)         (basic-seteq))))

  (define empty-Callers-set (set basic-set-union/singletons-are-sets
                                 equal?
                                 similar-callee?
                                 callers-hash-code))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Summaries Set
  (define (similar-open? bp1 bp2)
    (match (list bp1 bp2)
      ((list (BP open1 _) (BP open2 _))
       (state-similar? open1 open2))))

  (define (summaries-hash-code bp)
    (match-define (BP open _) bp)
    (equal-hash-code open))

  (define (get-summaries Summaries open)
    (match (set-get-similar Summaries (BP open #f))
      ((some similar-summaries)
       (some (for/fold ([gte-summaries (basic-set)])
                       ([summary (if (basic-set-eq? similar-summaries) similar-summaries (basic-seteq similar-summaries))]
                        #:when (match summary
                                 ((BP open2 _) (gte open2 open))))
               (basic-set-add gte-summaries summary))))
      ((none) (none))))

  (define empty-Summaries-set (set basic-set-union/singletons-are-sets
                                   equal?
                                   similar-open?
                                   summaries-hash-code))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define (set-add/fv s bp)
    (set-add s bp))

  (define (loop W Paths Summaries Callers)
    (match (set-get-one/rest W)
      ((none) Paths)
      ((some (list task W))
       (dprint "[loop] investigating: ~a\n" task)
       (match task
         ((BP open (? close? close))
          (let-values (((W Paths)
                        (for/fold ([W W]
                                   [Paths Paths])
                                  ([call (get-callers Callers open)])
                          (match call
                            ((BP grandfather-open _)
                             (PropagateAcross grandfather-open open close
                                              W Paths))))))

            (loop W Paths (set-add Summaries task) Callers)))
         ((BP open1 (? open? open2))
          (let-values (((W Paths)
                        (match (get-summaries Summaries open2)
                          ((none) (propagate-loop open2 (NextStates/Flow open2)
                                                  W Paths))
                          ((some relevant-summaries)
                           (for/fold ([W W]
                                      [Paths Paths])
                                     ([summary relevant-summaries])
                             (match summary
                               ((BP open~ close~)
                                (PropagateAcross open1 open~ close~ W Paths))))))))
            (loop W Paths Summaries (set-add Callers task))))
         ((BP open node)
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
             (values W Paths)
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
