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
;; Path : State × State
;; Entry : State

(define-struct Summary (push pop) #:transparent)
(define-struct Call (push1 push2) #:transparent)
;; Summary : State × State
;; Call : State × State

;; W : [SetOf WorkListTask]
;; Paths : [SetOf WorkListTask]
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
  (match-define (Analysis initial-state succ-states _ push? pop? state-equal?) analysis)
  (define (loop W Paths Summaries Callers)
    (if (set-empty? W)
        (values Paths Summaries Callers)
        (let-values (((task W) (set-get-one/rest W)))
          (match task
            ((Path push (? pop? pop))
             (with-for/fold (([W W]
                              [Paths Paths])
                             ([call (in-set Callers)]
                              #:when (match call
                                       ((Call _ push2) (state-equal? push push2))))
                             (match call
                               ((Call grandfather-push _)
                                (PropagatePop grandfather-push push pop W Paths analysis))))
               (loop W Paths (set-add Summaries (Summary push pop)) Callers)))
            ((Path push1 (? push? push2))
             (define-values (W Paths)
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
                        (PropagatePop push1 push2 pop W Paths analysis))))
                   (PropagateEntry push2 W Paths analysis)))
             (loop W Paths Summaries (set-add Callers (Call push1 push2))))
            ((Path push node)
             (define-values (W Paths)
               (propagate-loop push (succ-states node) W Paths analysis))
             (loop W Paths Summaries Callers))
            ((Entry push)
              (define-values (W Paths)
                (propagate-loop push (succ-states push) W Paths analysis))
              (loop W Paths Summaries Callers))))))
  (loop (set (Entry initial-state))
        (set (Entry initial-state))
        (set)
        (set)))


;; Propogate* : WorkListItem W Paths Analysis -> W Paths
(define (Propagate* element W Paths analysis)
  (match-define (Analysis _ _ _ push? pop? state-equal?) analysis)
  (if (set-member? Paths element)
      (values W Paths)
      (values (set-add W element) (set-add Paths element))))

;; Propogate : State State W Paths Analysis -> W Paths
(define (Propagate push node W Paths analysis)
  (Propagate* (Path push node) W Paths analysis))

;; Propogate : State W Paths Analysis -> W Paths
;; push must be a push state
(define (PropagateEntry push W Paths analysis)
  (Propagate* (Entry push) W Paths analysis))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests

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
                ((State pop-node env current-stack) pop))
      (match-let (((PopNode var _) pop-node))
        (for/set ([succ-node (succ-nodes pop-node)])
          (State succ-node
                 (update-env env var current-stack)
                 previous-stack)))))
  (define (update-env env var val)
    (hash-set env var (set-add (hash-ref env var (set)) val)))
  (Analysis (State (PushNode 'a 0) (hash) 'ε)
            succ-states
            pop-succ-states
            push?
            pop?
            state-equal?))

(CFA2 (reachability))

(define simple-reachability
  (let* ([push? (lambda (s)
                  (set-member? (set 1 3 4) s))]
         [pop? (lambda (s)
                 (set-member? (set 6 7 10) s))]
         [state-equal? (lambda (s1 s2)
                         (= s1 s2))]
         [succ-states (lambda (s)
                        (hash-ref (hasheq 1 (set 2)
                                          2 (set 3)
                                          3 (set 4)
                                          4 (set 5)
                                          5 (set 6)
                                          6 (set 7)
                                          7 (set 8)
                                          8 (set 9)
                                          9 (set 10)
                                          10 (set))
                                  s))]
         [pop-succ-states (lambda (push pop)
                            (succ-states pop))])
    (Analysis 1 succ-states pop-succ-states push? pop? state-equal?)))

(CFA2 simple-reachability)


(require rackunit
         rackunit/text-ui)

(define-test-suite cfa2-tests
  (test-case
   "CFA2 simple-reachability"
   (define-values (Paths Summaries Callers) (CFA2 simple-reachability))
   (check-true (set=? (set (Entry 1) (Entry 3) (Entry 4) (Path 1 8) (Path 3 4)
                           (Path 4 5) (Path 1 9) (Path 1 2) (Path 1 3)
                           (Path 4 6) (Path 1 10) (Path 3 7))
                      Paths))
   (check-true (set=? (set (Summary 4 6) (Summary 1 10) (Summary 3 7))
                      Summaries))
   (check-true (set=? (set (Call 3 4) (Call 1 3))
                      Callers))))

(run-tests cfa2-tests)
