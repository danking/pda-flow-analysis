#lang racket
(require "../racket-utils/similar-sets.rkt"
         "../racket-utils/option.rkt"
         "../racket-utils/partitioned-sets.rkt"
         "../semantics/flow.rkt"
         "bp.rkt"
         ;; TODO this should be some built-in module
         "../../../lattice/lattice.rkt"
         (prefix-in basic- racket/set))
(provide FlowAnalysis CFA2)

;; W : [SetOf BP]
;; Paths : [SetOf BP]

;; A [FlowAnalysis FState FV] is a
;;   (FlowAnalysis FState
;;                 [FState -> Boolean]
;;                 [FState -> Boolean]
;;                 [FState FState -> Boolean]
;;                 [Semi-Lattice FV]
;;                 [FState -> FState]
;;                 [FState FState -> Fstate])
(define-struct FlowAnalysis
  (initial-state open? close?
                 lattice
                 NextStates/Flow NextStatesAcross/Flow))
;;
;; open? identifies states which initiate balanced paths (and, consequently,
;; cannot be intermediary nodes of balanced paths, i.e. if BP = (start, n1, n2,
;; ..., end) then forall i, ni cannot be open?)
;;
;; close? identifies states which terminate balanced paths (and, consequently,
;; also cannot be intermediary nodes of balanced paths)


;; CFA2 : [FlowAnalysis FState FV]
;;        ->
;;        Paths
;;        Summaries
;;        Callers
(define (CFA2 flow-analysis)
  (match-define (FlowAnalysis initial-state open? close?
                              fstate-semi-lattice
                              NextStates/Flow NextStatesAcross/Flow)
                flow-analysis)

  (define bp-lattice
    (pointwise-semi-lattice BP
                            (BP-open fstate-semi-lattice)
                            (BP-node fstate-semi-lattice)))

  (define (equal?/ignore-fv x y [recur equal?])
    (and (recur (flow-state-astate (BP-open x)) (flow-state-astate (BP-open y)))
         (recur (flow-state-astate (BP-node x)) (flow-state-astate (BP-node y)))))

  (define (equal-hash-code/ignore-fv x [recur equal-hash-code])
    (+ (recur (flow-state-astate (BP-open x)))
       (recur (flow-state-astate (BP-node x)))))

  (define empty-W/Paths-set
    (set (semi-lattice-join bp-lattice)
         equal?
         equal?/ignore-fv
         equal-hash-code/ignore-fv))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Callers Set
  (define (get-callers Callers open)
    (pset-equivclass-partition Callers (BP #f open)))

  (define (comparable-callee? bp1 bp2)
    (match-define (BP open1 callee1) bp1)
    (match-define (BP open2 callee2) bp2)

    ((semi-lattice-comparable? fstate-semi-lattice) callee1 callee2))

  (define empty-Callers-set
    (make-partitioned-set comparable-callee?
                          (compose (semi-lattice-comparable?-hash-code fstate-semi-lattice)
                                   BP-node)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Summaries Set
  (define (get-summaries Summaries open)
    (pset-equivclass-partition Summaries (BP open #f)))

  (define (comparable-caller? bp1 bp2)
    (match-define (BP open1 node1) bp1)
    (match-define (BP open2 node2) bp2)

    ((semi-lattice-comparable? fstate-semi-lattice) open1 open2))

  (define empty-Summaries-set
    (make-partitioned-set comparable-caller?
                          (compose (semi-lattice-comparable?-hash-code
                                    fstate-semi-lattice)
                                   BP-open)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define (loop W Paths Summaries Callers)
    (match (set-get-one/rest W)
      ((none) (values Paths Summaries Callers))
      ((some (list task W))
       (log-info "[loop] investigating: ~v\n" task)
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
                              (begin (log-info "No summaries found for ~a to ~a"
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
         (if ((semi-lattice-gte? bp-lattice) similar-bp bp)
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

  (let-values (((W Paths)
                (propagate-loop initial-state
                                (NextStates/Flow initial-state)
                                empty-W/Paths-set
                                empty-W/Paths-set)))
    (loop W Paths empty-Summaries-set empty-Callers-set)))
