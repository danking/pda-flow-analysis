#lang racket

(define-syntax (with-for/fold stx)
 (syntax-case stx ()
   [(_ (([fold-targets fold-i] ...) clauses body1 body ...)
       context-body1 context-body ...)
    #`(let-values ([(fold-targets ...)
                    (for/fold/derived #,stx ([fold-targets fold-i] ...) clauses body1 body ...)])
        context-body1 context-body ...)]))

(define (WorkListTask? x)
  (or (Path? x) (Entry? x)))
(define-struct Path (push node) #:transparent)
(define-struct Entry (push) #:transparent)
;; Path : State × State × Any
;; Entry : State × Any
;; fi should be the result of fn-1(fn-2(...f0(⊥))) where fj is the transfer
;; function for node j in the path 0...n. 0 is the source node and n is the
;; Path-node or Entry-push node


(define-struct Summary (push pop fi) #:transparent)
(define-struct Call (push1 push2) #:transparent)
;; Summary : State × State × FlowDatum
;; Call : State × State

;; W : [SetOf WorkListTask]
;; Paths : [SetOf WorkListTask]
;; Summaries : [SetOf Summary]
;; Callers : [SetOf Call]

(define-struct Analysis
  (initial-state succ-states pop-succ-states push? pop? state-equal? flow-analysis))
;; An [Analysis State] is a
;;   (Analysis [State -> [SetOf State]]
;;             [State -> Boolean]
;;             [State -> Boolean]
;;             [State State -> Boolean]
;;             [FlowAnalysis State])
(define-struct FlowAnalysis
  (join gte transfer pop-transfer initial-flow-value))
;; A [FlowAnalysis State] is a
;;   (FlowAnalysis [FlowDatum FlowDatum -> FlowDatum]
;;                 [FlowDatum FlowDatum -> Boolean]
;;                 [State FlowInfo -> FlowDatum]
;;                 [State State FlowInfo-> FlowDatum]
;;                 FlowDatum)


;; CFA2 : Analysis
;;        ->
;;        Paths
;;        Summaries
;;        Callers
(define (CFA2 analysis)
  (match-define (Analysis initial-state
                          succ-states
                          _
                          push?
                          pop?
                          state-equal?
                          (FlowAnalysis _ flow-gte flow-transfer _ initial-flow-value))
                analysis)
  (define (loop W Paths Summaries Callers FlowInfo)
    (define (get-flow-info node)
      (hash-ref FlowInfo node initial-flow-value))
    (if (set-empty? W)
        (values Paths Summaries Callers FlowInfo)
        (let-values (((task W) (set-get-one/rest W)))
          (match task
            ((Path push (? pop? pop))
             (with-for/fold (([W W]
                              [Paths Paths]
                              [FlowInfo FlowInfo])
                             ([call (in-set Callers)]
                              #:when (match call
                                       ((Call _ push2) (state-equal? push push2))))
                             (match call
                               ((Call grandfather-push _)
                                (PropagatePop grandfather-push push pop W Paths FlowInfo analysis))))
               (loop W
                     Paths
                     (set-add Summaries (Summary push
                                                 pop
                                                 (get-flow-info push)))
                     Callers
                     FlowInfo)))
            ((Path push1 (? push? push2))
             (let-values
                 (((W Paths FlowInfo)
                   (cond [(for/or ([sum (in-set Summaries)])
                                  (match sum
                                    ((Summary push _ _) (state-equal? push push2))))
                          (for/fold
                              ([W W]
                               [Paths Paths]
                               [FlowInfo FlowInfo])
                              ([sum (in-set Summaries)]
                               #:when
                               (match sum
                                 ((Summary push _ _) (state-equal? push push2))))
                            (match sum
                              ((Summary _ pop fi)
                               (cond [(flow-gte fi (get-flow-info push2))
                                      (PropagatePop push1 push2 pop W Paths FlowInfo analysis)]
                                     [else (PropagateEntry push2 W Paths FlowInfo)]))))]
                         [else (PropagateEntry push2 W Paths FlowInfo)])))
               (loop W Paths Summaries (set-add Callers (Call push1 push2)) FlowInfo)))
            ((Path push node)
             (let-values (((W Paths FlowInfo)
                           (propagate-loop push (succ-states node) (flow-transfer node (get-flow-info node))
                                           W Paths FlowInfo analysis)))
               (loop W Paths Summaries Callers FlowInfo)))
            ((Entry push)
             (let-values (((W Paths FlowInfo)
                           (propagate-loop push (succ-states push) (flow-transfer push (get-flow-info push))
                                           W Paths FlowInfo analysis)))
               (loop W Paths Summaries Callers FlowInfo)))))))
  (loop (set (Entry initial-state))
        (set (Entry initial-state))
        (set)
        (set)
        (hash initial-state initial-flow-value)))


;; Propagate : State State Any W Paths FlowInfo Analysis -> W Paths FlowInfo
(define (Propagate push node fi W Paths FlowInfo analysis)
  (match-define (Analysis _ _ _ _ _ _ (FlowAnalysis join _ _ _ initial-flow-value)) analysis)
  (define (get-flow-info node)
    (hash-ref FlowInfo node initial-flow-value))
  (if (not (set-member? Paths (Path push node)))
      (UpdatePathsWAndFI push node fi W Paths FlowInfo analysis)
      (if (not (equal? (join (get-flow-info node) fi)
                       (get-flow-info node)))
          (UpdatePathsWAndFI push node (join (get-flow-info node) fi)
                             W Paths FlowInfo analysis)
          (values W Paths FlowInfo))))

(define (UpdatePathsWAndFI push node fi W Paths FlowInfo analysis)
  (match-define (Analysis _ _ _ _ _ _ (FlowAnalysis join _ _ _ initial-flow-value)) analysis)
  (values (set-add W (Path push node))
          (set-add Paths (Path push node))
          (hash-set FlowInfo node (join (hash-ref FlowInfo node initial-flow-value) fi))))

;; PropagateEntry : State W Paths FlowInfo -> W Paths FlowInfo
;; push must be a push state
(define (PropagateEntry push W Paths FlowInfo)
  (if (set-member? Paths (Entry push))
      (values W Paths FlowInfo)
      (values (set-add W (Entry push))
              (set-add Paths (Entry push))
              FlowInfo)))

;; PropagatePop : State State State W Paths FlowInfo Analysis -> W Paths FlowInfo
(define (PropagatePop grandfather-push push pop W Paths FlowInfo analysis)
  (match-define (Analysis _ _ pop-succ-states _ _ _ (FlowAnalysis _ _ _ pop-transfer _)) analysis)
  (propagate-loop grandfather-push
                  (pop-succ-states push pop)
                  (pop-transfer pop (hash-ref FlowInfo pop)
                                grandfather-push (hash-ref FlowInfo grandfather-push))
                  W Paths FlowInfo analysis))

;; propagate-loop : State [SetOf State] Any W Paths FlowInfo Analysis -> W Paths FlowInfo
(define (propagate-loop push succs fi W Paths FlowInfo analysis)
  (for/fold ([W W]
             [Paths Paths]
             [FlowInfo FlowInfo])
            ([s (in-set succs)])
    (let-values (((new-W new-Paths new-FlowInfo) (Propagate push s fi W Paths FlowInfo analysis)))
      (values new-W
              new-Paths
              new-FlowInfo))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests

(define (reachability/min-headroom)
  (define-struct State (node env astack) #:transparent)
  (define-struct PushNode (value id) #:transparent)
  (define-struct PopNode (var id) #:transparent)
  (define-struct StackEnsure (hdrm id) #:transparent)
  (define-struct Noop (id) #:transparent)


  (define push?
    (match-lambda ((State node _ _)
                   (PushNode? node))))
  (define pop?
    (match-lambda ((State node _ _)
                   (PopNode? node))))
  (define state-equal? equal?)
  (define (succ-nodes node)
    (hash-ref (hash (PushNode 'a 0) (set (StackEnsure 5 1))
                    (StackEnsure 5 1) (set (PushNode 'b 2))
                    (PushNode 'b 2) (set (PushNode 'c 3))
                    (PushNode 'c 3) (set (Noop 4))
                    (Noop 4) (set (PopNode 'var1 5) (StackEnsure 5 1))
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
                 (hash-set env var current-stack)
                 previous-stack)))))

  (define flow-join min)
  (define flow->= <=)
  (define (flow-transfer state fi)
    (printf "state: ~a, fi: ~a\n" state fi)
    (match-let (((State node _ _) state))
      (match node
        ((PushNode _ _)
         (cond [(= fi +inf.0) 0]
               [else (max (sub1 fi) 0)]))
        ((PopNode _ _) (add1 fi))
        ((StackEnsure hdrm _) (max hdrm fi))
        ((Noop _) fi))))
  (define (flow-pop-transfer pop pop-fi grandfather-push gfather-fi)
    (add1 pop-fi))

  (Analysis (State (PushNode 'a 0) (hash) 'ε)
            succ-states
            pop-succ-states
            push?
            pop?
            state-equal?
            (FlowAnalysis flow-join
                          flow->=
                          flow-transfer
                          flow-pop-transfer
                          +inf.0)))

(CFA2 (reachability/min-headroom))
