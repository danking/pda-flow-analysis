#lang racket
(require "../racket-utils/partitioned-sets.rkt"
         "../semantics/flow.rkt"
         "bp.rkt"
         ;; TODO this should be some built-in module
         "../lattice/lattice.rkt")
(provide FlowAnalysis CFA2)
(module+ test (require rackunit))

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
;;   (FlowAnalysis [SetOf FState]
;;                 [FState -> Boolean]
;;                 [FState -> Boolean]
;;                 [FState FState -> Boolean]
;;                 [Semi-Lattice FV]
;;                 [FState FState -> Boolean]
;;                 [FState -> Number]
;;                 [FState -> FState]
;;                 [FState FState -> Fstate])
(define-struct FlowAnalysis
  (initial-states open? close?
                  lattice same-sub-lattice? sub-lattice-hash-code
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
  (match-define (FlowAnalysis initial-states open? close?
                              fstate-semi-lattice
                              fstate-same-sub-lattice?
                              fstate-sub-lattice-hash-code
                              NextStates/Flow NextStatesAcross/Flow)
                flow-analysis)

  (define bp-lattice
    (pointwise-semi-lattice BP
                            (BP-open fstate-semi-lattice)
                            (BP-node fstate-semi-lattice)))

  (define (bp-same-sub-lattice? bp1 bp2 [recur equal?])
    (and (fstate-same-sub-lattice? (BP-open bp1) (BP-open bp2) recur)
         (fstate-same-sub-lattice? (BP-node bp1) (BP-node bp2) recur)))

  (define (bp-pset-add/join bp-pset bp)
    (pset-add/join bp-pset bp bp-lattice))


  ;; note that we use (equal-hash-code (list ...)) to delegate choosing a good
  ;; way of combining hash codes to Racket
  (define (bp-sub-lattice-hash-code bp [recur equal-hash-code])
    (equal-hash-code (list (fstate-sub-lattice-hash-code (BP-open bp) recur)
                           (fstate-sub-lattice-hash-code (BP-node bp) recur))))

  (define empty-W/Paths-set
    (make-partitioned-set bp-same-sub-lattice?
                          bp-sub-lattice-hash-code))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Callers Set

  ;; get-callers : Callers FState -> [SetOf FState]
  ;;
  ;; {(o1,o2) | open ⊒ o2 ∧ (o1,o2) ∈ Callers }
  ;;
  ;; The callers set is used to propagate multiple paths of execution through
  ;; the same, newly created summary. The paths of execution must call to an
  ;; open node which is subsumed by the open node of the summary. If we
  ;; propagated a call to a more general open, then the less general summary
  ;; will not propagate all the information. This results in an unsafe
  ;; approximation.
  ;;
  (define (get-callers Callers open)
    (for/set ((call (pset-equivclass-partition Callers (BP #f open)))
              #:when ((semi-lattice-gte? fstate-semi-lattice) open (BP-node call)))
      call))

  (define (comparable-callee? bp1 bp2 [recur equal?])
    (match-define (BP open1 callee1) bp1)
    (match-define (BP open2 callee2) bp2)

    (fstate-same-sub-lattice? callee1 callee2 recur))

  (define empty-Callers-set
    (make-partitioned-set comparable-callee?
                          (lambda (bp [recur equal-hash-code])
                            (fstate-sub-lattice-hash-code (BP-node bp) recur))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Summaries Set

  ;; get-summaries : Summaries FState -> [SetOf FState]
  ;;
  ;; {(s-open,s-close) | s-open ⊒ open ∧ (s-open,s-close) ∈ Summaries }
  ;;
  ;; The summaries set is used to propagate multiple paths of execution through
  ;; a empty-stack-to-empty-stack path. If the called-to open is subsumed by the
  ;; summary's open, then we needn't reinvestigate this
  ;; empty-stack-to-empty-stack path.
  ;;
  (define (get-summaries Summaries open)
    (for/set ((summary (pset-equivclass-partition Summaries (BP open #f)))
              #:when ((semi-lattice-gte? fstate-semi-lattice) (BP-open summary)
                                                              open))
      summary))

  (define (comparable-caller? bp1 bp2 [recur equal?])
    (match-define (BP open1 node1) bp1)
    (match-define (BP open2 node2) bp2)

    (fstate-same-sub-lattice? open1 open2 recur))

  (define empty-Summaries-set
    (make-partitioned-set comparable-caller?
                          (lambda (bp [recur equal-hash-code])
                            (fstate-sub-lattice-hash-code (BP-open bp) recur))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define (loop W Paths Summaries Callers)
    (if (pset-empty? W)
        (values Paths Summaries Callers)
        (let-values
            (((task W) (pset-get-one/rest W)))
          (log-info "[loop] investigating: ~v\n" task)
          (match task
            ((BP open (? close? close))
             (log-info "summary ~a to ~a" open close)
             (let-values
                 (((W Paths)
                   (for/fold ([W W]
                              [Paths Paths])
                       ([call (in-set (get-callers Callers open))])
                     (match call
                       ((BP grandfather-open _)
                        (PropagateAcross grandfather-open open close
                                         W Paths))))))

               (loop W Paths (bp-pset-add/join Summaries task) Callers)))
            ((BP open1 (? open? open2))
             (log-info "call ~a to ~a" open1 open2)
             (let-values
                 (((W Paths)
                   (let ((summaries (get-summaries Summaries open2)))
                     (if (set-empty? summaries)
                         (begin (log-info "No summaries found for ~a to ~a"
                                          open1 open2)
                                (propagate-loop open2 (NextStates/Flow open2)
                                                W Paths))
                         (for/fold ([W W]
                                    [Paths Paths])
                             ([summary (in-set summaries)])
                           (match summary
                             ((BP open~ close~)
                              (PropagateAcross open1 open~ close~ W Paths))))))))
               (loop W Paths Summaries (bp-pset-add/join Callers task))))
            ((BP open node)
             (log-info "step ~a to ~a" open node)
             (let-values
                 (((W Paths)
                   (propagate-loop open (NextStates/Flow node)
                                   W Paths)))
               (loop W Paths Summaries Callers)))))))

  ;; Propogate : OpenFState FState W Paths -> W Paths
  (define (Propagate open node W Paths)
    (define bp (BP open node))
    (define Paths-equivclass (pset-equivclass-partition Paths bp))
    (define W-equivclass (pset-equivclass-partition W bp))

    (if (pset-greater-or-equal-is-member? Paths bp bp-lattice)
        (values W Paths)
        (values (bp-pset-add/join W bp)
                (bp-pset-add/join Paths bp))))

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
                (for/fold ((W empty-W/Paths-set)
                           (Paths empty-W/Paths-set))
                          ((initial-state (in-set initial-states)))
                  (propagate-loop initial-state
                                  (NextStates/Flow initial-state)
                                  W
                                  Paths))))
    (loop W Paths empty-Summaries-set empty-Callers-set)))

;; tri-partition-set : [X -> Boolean]
;;                     [X -> Boolean]
;;                     [SetOf X]
;;                     ->
;;                     [SetOf X]
;;                     [SetOf X]
;;                     [SetOf X]
;;
;; Partition the set such that all values for which the first-group? predicate
;; holds are in the first set, all the elements for which the second-group?
;; predicate holds are in the second set, and all other elements are in the
;; third set.
(define (tri-partition-set first-group? second-group? s)
  (for/fold
      ((first (set))
       (second (set))
       (third (set)))
      ((element (in-set s)))
    (cond [(first-group? element)
           (values (set-add first element) second third)]
          [(second-group? element)
           (values first (set-add second element) third)]
          [else
           (values first second (set-add third element))])))

(module+ test
  (let-values (((symbols strings others)
                (tri-partition-set symbol? string? '(a 1 "foo" 2 ds "bar" 3 4 "baz" 21))))
    (check-equal? symbols (set 'a 'ds))
    (check-equal? strings (set "foo" "bar" "baz"))
    (check-equal? others (set 1 2 3 4 21))))

;; pset-add/join : [PartitionedSet X] X [Semi-Lattice X] -> [PartitionedSet X]
;;
;; Adds v to pset if nothing in v is greater than or equal to it and removes
;; anything from the set which is less than it.
;;
(define (pset-add/join pset v v-lattice)
  (define equivclass (pset-equivclass-partition pset v))
  (define gte? (semi-lattice-gte? v-lattice))

  (let-values
      (((greater-or-eq lesser incomparable)
        (tri-partition-set (lambda (x) (gte? x v))
                           (lambda (x) (gte? v x))
                           equivclass)))
    (cond [(not (set-empty? greater-or-eq)) pset]
          [(not (set-empty? lesser))
           (pset-add (pset-subtract-set pset lesser) v)]
          [else (pset-add pset v)])))

;; pset-greater-or-equal-is-member? : [PartitionedSet X] X [Semi-Lattice X] -> Boolean
;;
;; NB: Elements which are not in the same partition should be incomparable in
;; the lattice.
;;
;; Determines if any element of pset is greater than or equal to v according to
;; v-lattice.
(define (pset-greater-or-equal-is-member? pset v v-lattice)
  (define equivclass (pset-equivclass-partition pset v))
  (define gte? (semi-lattice-gte? v-lattice))

  (for/or ((v~ (in-set equivclass))) (gte? v~ v)))

;; pset-subtract-set : [PartitionedSet X] [SetOf X] -> [PartitionedSet X]
;;
(define (pset-subtract-set pset set)
  (for/fold
      ((pset pset))
      ((element (in-set set)))
    (pset-remove pset element)))
