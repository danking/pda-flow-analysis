#lang racket
(require "../racket-utils/partitioned-sets.rkt"
         "../semantics/flow.rkt"
         "bp.rkt"
         "log-harness.rkt"
         ;; TODO this should be some built-in module
         "../lattice/lattice.rkt")
(provide FlowAnalysis PDA2)
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


;; W : [SetOf [BP FlowState]]
;;   if (x,y) is in the W, or workset, then there is a balanced path from x to y
;;   whose implications have not yet been propagated.
;;
;; Paths : [SetOf [BP FlowState]]
;;   if (x,y) is in the paths set then there is a balanced path from x to y.
;;
;; Summaries : [SetOf [BP FlowState]]
;;   if (x,y) is in the summaries set then there is a balanced path from x to y
;;   and y is a close state.
;;
;; Callers : [SetOf [BP FlowState]]
;;   if (x,y) is in the callers set then there is a balanced path frmo x to y
;;   and y is a open state.

;; It is often desirable to carry around some state which is global to the entire
;; analysis. For example, widening the store asks for a store to be kept
;; globally. For this reason we augment the analysis as follows.
;;
;; A [FlowAnalysis FlowState, Configuration] is a
;;
;;   (FlowAnalysis [SetOf FlowState]
;;                 Configuration
;;                 (FlowState -> Boolean)
;;                 (FlowState -> Boolean)
;;                 [Semi-Lattice FlowStates]
;;                 (FlowState FlowState -> Boolean)
;;                 (FlowState -> Natural)
;;                 (FlowState FlowState Configuration
;;                   -> [Values [SetOf FlowState] Configuration])
;;                 (FlowState FlowState FlowState Configuration
;;                   -> [Values [SetOf FlowState] Configuration])
;;                 (FlowState -> String))

(define-struct FlowAnalysis
  (initial-states initial-configuration
   open? close?
   flow-state-lattice
   same-sub-lattice? sub-lattice-hash-code
   flow-state-successors flow-state-successors-across
   flowstate-debug-string))

;; open? identifies states which initiate balanced paths (and, consequently,
;; cannot be intermediary nodes of balanced paths, i.e. if BP = (start, n1, n2,
;; ..., end) then forall i, ni cannot be open?)
;;
;; close? identifies states which terminate balanced paths (and, consequently,
;; also cannot be intermediary nodes of balanced paths)


;; PDA2 : [FlowAnalysis FState]
;;        ->
;;        Paths
;;        Summaries
;;        Callers
(define (PDA2 flow-analysis)
  (match-define (FlowAnalysis initial-states initial-configuration
                              open? close?
                              fstate-semi-lattice
                              fstate-same-sub-lattice?
                              fstate-sub-lattice-hash-code
                              flow-state-successors
                              flow-state-successors-across
                              flowstate-debug-string)
                flow-analysis)

  (define fstate-gte? (semi-lattice-gte? fstate-semi-lattice))

  (define bp-lattice
    (pointwise-semi-lattice BP
                            (BP-open fstate-semi-lattice)
                            (BP-node fstate-semi-lattice)))

  (define (bp-same-sub-lattice? bp1 bp2 [recur equal?])
    (and (fstate-same-sub-lattice? (BP-open bp1) (BP-open bp2) recur)
         (fstate-same-sub-lattice? (BP-node bp1) (BP-node bp2) recur)))

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

  ;; MatchingCallers : Callers FState -> [SetOf FState]
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
  (define (MatchingCallers Callers open)
    (for/set ((call (pset-equivclass-partition Callers (BP #f open)))
              #:when (fstate-gte? open (BP-node call)))
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

  ;; MatchingSummaries : Summaries FState -> [SetOf FState]
  ;;
  ;; {(s-open,s-close) | s-open ⊒ open ∧ (s-open,s-close) ∈ Summaries }
  ;;
  ;; The summaries set is used to propagate multiple paths of execution through
  ;; a empty-stack-to-empty-stack path. If the called-to open is subsumed by the
  ;; summary's open, then we needn't reinvestigate this
  ;; empty-stack-to-empty-stack path.
  ;;
  (define (MatchingSummaries Summaries open)
    (for/set ((summary (pset-equivclass-partition Summaries (BP open #f)))
              #:when (fstate-gte? (BP-open summary) open))
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

  (define-syntax-rule (splat-loop w-paths-configuration Summaries Callers)
    (let-values (((W Paths Configuration) w-paths-configuration))
      (loop W Paths Configuration Summaries Callers)))

  (define (loop W Paths Configuration Summaries Callers)
    (log-info* "Magnitudes: (W Paths Summaries Callers) = (~a ~a ~a ~a)"
               (pset-count W) (pset-count Paths)
               (pset-count Summaries) (pset-count Callers))
    (if (pset-empty? W)
        (values Paths Configuration Summaries Callers)
        (let-values
            (((task W) (pset-get-one/rest W)))
          (match task
            ((BP open (? close? close))
             (log-info* "summary: ")
             (log-info* (flowstate-debug-string open))
             (log-info* (flowstate-debug-string close))
             (splat-loop (PropagateCallers (MatchingCallers Callers open)
                                           close
                                           W
                                           Paths
                                           Configuration)
                         (pset-add Summaries (BP open close))
                         Callers))
            ((BP open1 (? open? open2))
             (log-info* "call: ")
             (log-info* (flowstate-debug-string open1))
             (log-info* (flowstate-debug-string open2))
             (splat-loop (MaybePropagateSummaries (MatchingSummaries Summaries
                                                                     open2)
                                                  open2
                                                  open1
                                                  W
                                                  Paths
                                                  Configuration)
                         Summaries
                         (pset-add Callers (BP open1 open2))))
            ((BP open node)
             (log-info* "path: ")
             (log-info* (flowstate-debug-string open))
             (log-info* (flowstate-debug-string node))
             (splat-loop (Propagate open node W Paths Configuration)
                         Summaries
                         Callers))))))

  ;; PropagateCallers : [SetOf [BP FState]] FState W Paths Configuration
  ;;                    ->
  ;;                    W Paths Configuration
  ;;
  (define (PropagateCallers callers close W Paths Configuration)
    (for/fold ((W W)
               (Paths Paths)
               (Configuration Configuration))
        ((call (in-set callers)))
      (match-let (((BP gp open) call))
        (PropagateAcross gp open close W Paths Configuration))))

  ;; MaybePropagateSummaries : [SetOf [BP FState]]
  ;;                           FState
  ;;                           FState
  ;;                           W Paths Configuration
  ;;                           ->
  ;;                           W Paths Configuration
  ;;
  ;; if there are no summaries, we must instead explore the new BP
  (define (MaybePropagateSummaries summaries open gp W Paths Configuration)
    (if (set-empty? summaries)
        (Enter open W Paths Configuration)
        (PropagateSummaries summaries gp W Paths Configuration)))

  ;; PropagateSummaries : [SetOf [BP FState]] FState W Paths Configuration
  ;;                      ->
  ;;                      W Paths Configuration
  ;;
  (define (PropagateSummaries summaries gp W Paths Configuration)
    (for/fold ((W W)
               (Paths Paths)
               (Configuration Configuration))
        ((summary (in-set summaries)))
      (match-let (((BP open close) summary))
        (PropagateAcross gp open close W Paths Configuration))))

  ;; Enter : FState W Paths Configuration -> W Paths Configuration
  ;;
  (define (Enter open W Paths Configuration)
    (Propagate open open W Paths Configuration))

  ;; Propagate : FState W Paths Configuration -> W Paths Configuration
  ;;
  (define (Propagate open node W Paths Configuration)
    (let-values (((succs Configuration)
                  (flow-state-successors open node Configuration)))
      (AddAll W Paths Configuration open succs)))

  ;; PropagateAcross : FState FState FState W Paths Configuration
  ;;                   ->
  ;;                   W Paths Configuration
  ;;
  (define (PropagateAcross gp open node W Paths Configuration)
    (let-values (((succs Configuration)
                  (flow-state-successors-across gp open node Configuration)))
      (AddAll W Paths Configuration gp succs)))

  ;; AddAll : W Paths Configuration FState FState
  ;;
  (define (AddAll W Paths Configuration open succs)
    (for/fold ((W W)
               (Paths Paths)
               (Configuration Configuration))
        ((succ (in-set succs)))
      (let ((bp (BP open succ)))
        (if (AlreadySubsumedInSet? Paths bp)
            (values W Paths Configuration)
            (values (JoiningSetAdd W bp)
                    (pset-add Paths bp)
                    Configuration)))))

  ;; AlreadySubsumedInSet? : [PartitionedSet X] X -> Boolean
  ;;
  ;; NB: Elements which are not in the same partition should be incomparable in
  ;; the lattice.
  ;;
  ;; Determines if any element of pset is greater than or equal to v according to
  ;; v-lattice.
  (define (AlreadySubsumedInSet? pset v)
    (define equivclass (pset-equivclass-partition pset v))
    (define gte? (semi-lattice-gte? bp-lattice))

    (for/or ((v~ (in-set equivclass))) (gte? v~ v)))

  (define JoiningSetAdd (curry pset-add/join bp-lattice))

  (splat-loop (for/fold ((W empty-W/Paths-set)
                         (Paths empty-W/Paths-set)
                         (Configuration initial-configuration))
                  ((initial-state initial-states))
                (Enter initial-state W Paths Configuration))
              empty-Summaries-set
              empty-Callers-set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utilities

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

;; pset-add/join : [Semi-Lattice X] [PartitionedSet X] X -> [PartitionedSet X]
;;
;; Adds v to pset if nothing in v is greater than or equal to it and removes
;; anything from the set which is less than it.
;;
(define (pset-add/join v-lattice pset v)
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

;; pset-subtract-set : [PartitionedSet X] [SetOf X] -> [PartitionedSet X]
;;
(define (pset-subtract-set pset set)
  (for/fold
      ((pset pset))
      ((element (in-set set)))
    (pset-remove pset element)))
