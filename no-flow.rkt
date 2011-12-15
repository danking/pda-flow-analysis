#lang racket

(define (WorkListTask? x)
  (or (Path? x) (Summary? x) (Call? x)))
(define-struct Path (push node) #:transparent)
(define-struct Summary (push pop) #:transparent)
(define-struct Call (push1 push2) #:transparent)
;; Path : State × State
;; Summary : State × State
;; Call : State × State

;; W : [SetOf WorkListTask]
;; Paths : [SetOf Path]
;; Summaries : [SetOf Summary]
;; Callers : [SetOf Call]

(define-struct Analysis
  (initial-state succ-states pop-succ-states push? pop? state-equal?))
;; An Analysis is a
;;   (Analysis [State -> [SetOf State]]
;;             [State -> Boolean]
;;             [State -> Boolean]
;;             [State State -> Boolean])


;; CFA2 : State
;;        Analysis
;;        ->
;;        Paths
;;        Summaries
;;        Callers
(define (CFA2 analysis)
  (match-define (Analysis initial-state succ-states _ _ _ state-equal?) analysis)
  (define (loop W Paths Summaries Callers)
    (if (set-empty? W)
        (values Paths Summaries Callers)
        (let-values (((task W) (set-get-one/rest W)))
          (match task
            ((Path push node)
             (let-values (((W Paths)
                           (propagate-loop push (succ-states node) W Paths analysis)))
               (loop W Paths Summaries Callers)))
            ((Summary push pop)
             (let-values
                 (((W Paths)
                   (for/fold ([W W]
                              [Paths Paths])
                       ([call (in-set Callers)]
                        #:when (match call
                                 ((Call _ push2) (state-equal? push push2))))
                     (match call
                       ((Call grandfather-push _)
                        (PropagatePop grandfather-push push pop W Paths analysis))))))
               (loop W Paths (set-add Summaries (Summary push pop)) Callers)))
            ((Call push1 push2)
             (let-values
                 (((W Paths)
                   (if (for/or ([sum (in-set Summaries)])
                               (match sum
                                 ((Summary push _) (state-equal? push push2))))
                       (for/fold
                           ([W W]
                            [Paths Paths])
                           ([sum (in-set Summaries)]
                            #:when
                            (match sum
                              ((Summary push _) (state-equal? push push2))))
                         (match sum
                           ((Summary _ pop)
                            (propagate-loop push1 (succ-states pop) W Paths analysis))))
                       (Propagate push2 push2 W Paths analysis))))
               (loop W Paths Summaries (set-add Callers (Call push1 push2)))))))))
  (loop (set (Path initial-state initial-state))
        (set)
        (set)
        (set)))


;; Propogate : State State W Paths Analysis -> W Paths
(define (Propagate push node W Paths analysis)
  (match-define (Analysis _ _ _ push? pop? state-equal?) analysis)
  (if (set-member? Paths (Path push node))
      (values W Paths)
      (cond [(and (push? node) (not (state-equal? push node)))
             (values (set-add W (Call push node))
                     Paths)]
            [(pop? node)
             (values (set-add W (Summary push node))
                     (set-add Paths (Path push node)))]
            [else
             (values (set-add W (Path push node))
                     (set-add Paths (Path push node)))])))

;; PropogatePop : State State State W Paths Analysis -> W Paths
(define (PropagatePop grandfather-push push pop W Paths analysis)
  (match-define (Analysis _ _ pop-succ-states _ _ _) analysis)
  (propagate-loop grandfather-push (pop-succ-states push pop) W Paths analysis))

;; propagate-loop : State [SetOf State] W Paths Analysis -> W Paths
(define (propagate-loop push succs W Paths analysis)
  (for/fold ([W W]
             [Paths Paths])
            ([s (in-set succs)])
    (let-values (((new-W new-Paths) (Propagate push s W Paths analysis)))
      (values (set-union new-W W)
              (set-union new-Paths Paths)))))


(define (reachability)
  (define-struct State (node env astack) #:transparent)
  (define-struct PushNode (value id) #:transparent)
  (define-struct PopNode (var id) #:transparent)
  (define-struct Noop (id) #:transparent)


  (define push?
    (match-lambda ((State node _ _)
                   (PushNode? node))))
  (define pop?
    (match-lambda ((State node _ _)
                   (PopNode? node))))
  (define state-equal? equal?)
  (define (succ-nodes node)
    (hash-ref (hash (PushNode 'a 0) (set (Noop 1))
                    (Noop 1) (set (PushNode 'b 2))
                    (PushNode 'b 2) (set (PushNode 'c 3))
                    (PushNode 'c 3) (set (Noop 4))
                    (Noop 4) (set (PopNode 'var1 5) (PushNode 'b 2))
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
                ((State pop-node env _) pop))
      (match-let (((PopNode var _) pop-node))
        (for/set ([succ-node (succ-nodes pop-node)])
          (State succ-node
                 (update-env env var previous-stack)
                 previous-stack)))))
  (define (update-env env var val)
    (hash-set env var val))
  (Analysis (State (PushNode 'a 0) (hash) 'ε)
            succ-states
            pop-succ-states
            push?
            pop?
            state-equal?))

(CFA2 (reachability))
