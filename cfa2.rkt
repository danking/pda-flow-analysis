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

;; `CFA2' is an flow analysis algorithm for push down automata. A push down
;; automata is a finite state machine with a stack.
;;
;; Some states modify the stack. WLOG, These states may only add one
;; stack-element to the top of the stack or remove one stack-element from the
;; top of the stack.
;;
;; The states of a push down automata can be partitioned into three sets: Opens,
;; Closes, and Other.
;;
;; The Open and Close states are defined differently depending on the
;; analysis. For a forward analysis the Open states are the states which "push"
;; one stack-element onto the stack and the Close states are the states which
;; "pop" one stack-element off of the stack. For a backward analysis the Open
;; and Close sets are interchanged such that Opens are "pops" and Closes are
;; "pushes".
;;
;; A bit more precisely,
;;
;;   An Open state is a set of stack-modifying states which all change the size
;;   of the stack in the same way.
;;
;;   A Close state is the set of stack-modifying states which modify the stack
;;   size in the way the Open states do not. (equivalently, the Close set is the
;;   set of stack-modifying states which are not contained in the Open set)
;;
;; The definition of a Balanced Path is central to the algorithm's
;; idea. Conceptually, a Balanced Path is an execution path from X to Y in which
;; the stack at state X is "maintained" from X to Y, i.e., the elements on the
;; stack at X are never pop'd off by any intermening states, and the stack at
;; state Y is equivalent to the stack at state X.
;;
;; One might also think of a Balanced Path as an execution path from X to Y
;; which does not get stuck when the stack at state X is empty and which leaves
;; the stack empty again at state Y.
;;
;;
;; The notion can be defined recursively:
;;
;; Balanced Path
;; -------------
;;
;; A path (n0, n1, n2, ..., nj) is a Balanced Path iff n0 ∈ Open and
;; (n1, n2, ..., nj) is an Empty-Stack to Empty-Stack Path.
;;
;;
;; Empty-Stack to Empty-Stack (ES-ES) Path
;; ---------------------------------------
;;
;; 1. The empty path, (), is an Empty-Stack to Empty-Stack (ES-ES) Path.
;;
;; 2. A path (n1, n2) is an Empty-Stack to Empty-Stack (ES-ES) Path
;;    iff n1 ∈ Open and n2 ∈ Close
;;
;; 3. A path (n1, n2, ..., nj-1, nj) is an ES-ES Path iff
;;
;;    - n2 ∉ (Open ∪ Close), and
;;    - (n2, ..., nj) is an Empty-Stack to Empty-Stack Path
;;
;;   OR
;;
;;    - n2 ∈ Open,
;;    - nj ∈ Close, and
;;    - (n2, ..., nj-1) is an Empty-Stack to Empty-Stack Path.
;;
;;
;; These definitions are lifted to flow states by ignoring the associated flow
;; value.


;; W : [SetOf BP]
;;   if (x,y) is in the W, or workset, then there is a balanced path from x to y
;;   whose implications have not yet been propagated.
;;
;; Paths : [SetOf BP]
;;   if (x,y) is in the paths set then there is a balanced path from x to y.
;;
;; Summaries : [SetOf BP]
;;   if (x,y) is in the summaries set then there is a balanced path from x to y
;;   and y is a close state.
;;
;; Callers : [SetOf BP]
;;   if (x,y) is in the callers set then there is a balanced path frmo x to y
;;   and y is a open state.


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
