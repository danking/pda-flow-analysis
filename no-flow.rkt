#lang racket

(define-syntax-rule (apply-to-values p generator)
  (call-with-values (lambda () generator) p))

(define (WorkListTask? x)
  (or (BP? x) (Open? x)))
(define-struct BP (open node) #:transparent)
(define-struct Open (open) #:transparent)
;; BP : State × State
;; Entry : State


;; W : [SetOf WorkListTask]
;; Paths : [SetOf WorkListTask]

(define-struct Analysis
  (initial-state NextStates NextStatesAcross open? close? state-equal?))
;; An Analysis is a
;;   (Analysis [State -> [SetOf State]]
;;             [State -> Boolean]
;;             [State -> Boolean]
;;             [State State -> Boolean])


;; CFA2 : Analysis
;;        ->
;;        Paths
(define (CFA2 analysis)
  (match-define (Analysis initial-state NextStates _ open? close? state-equal?) analysis)
  (define (loop W Paths)
    (if (set-empty? W)
        Paths
        (let-values (((task W) (set-get-one/rest W)))
          (apply-to-values
           loop
           (match task
             ((BP open (? close? close))
              (for/fold ([W W]
                         [Paths Paths])
                        ([call (in-set Paths)]
                         #:when (match call
                                  ((BP gf open~)
                                   (and (open? gf)
                                        (state-equal? open open~)))
                                  ((Open _) #f)))
                (match call
                  ((BP grandfather-open _)
                   (PropagateAcross grandfather-open open close W Paths analysis)))))
             ((BP open (? open? open2))
              (if (for/or ([sum (in-set Paths)])
                          (match sum
                            ((BP open~ close~)
                             (and (state-equal? open2 open~)
                                  (close? close~)))
                            ((Open _) #f)))
                  (for/fold
                      ([W W]
                       [Paths Paths])
                      ([sum (in-set Paths)]
                       #:when
                       (match sum
                         ((BP open~ close~)
                          (and (state-equal? open2 open~)
                               (close? close~)))
                         ((Open _) #f)))
                    (match sum
                      ((BP open~ close~)
                       (PropagateAcross open open2 close~ W Paths analysis))))
                  (PropagateOpen open2 W Paths)))
             ((BP open node)
              (propagate-loop open (NextStates node) W Paths))
             ((Open open)
              (propagate-loop open (NextStates open) W Paths)))))))
 (loop (set (Open initial-state))
       (set (Open initial-state))))


;; Propogate* : WorkListItem W Paths -> W Paths
(define (Propagate* element W Paths)
  (if (set-member? Paths element)
      (values W Paths)
      (values (set-add W element) (set-add Paths element))))

;; Propogate : State State W Paths -> W Paths
(define (Propagate open node W Paths)
  (Propagate* (BP open node) W Paths))

;; PropogateOpen : State W Paths Analysis -> W Paths
;; push must be an open state
(define (PropagateOpen open W Paths)
  (Propagate* (Open open) W Paths))

;; PropogateAcross : State State State W Paths Analysis -> W Paths
(define (PropagateAcross grandfather-open open close W Paths analysis)
  (match-define (Analysis _ _ NextStatesAcross _ _ _) analysis)
  (propagate-loop grandfather-open (NextStatesAcross open close) W Paths))

;; propagate-loop : State [SetOf State] W Paths -> W Paths
(define (propagate-loop push succs W Paths)
  (for/fold ([W W]
             [Paths Paths])
            ([s (in-set succs)])
    (let-values (((W~ Paths~) (Propagate push s W Paths)))
      (values (set-union W W~)
              (set-union Paths Paths~)))))

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
   (define Paths (CFA2 simple-reachability))
   (check-true (set=? (set (Open 1) (Open 3) (Open 4) (BP 1 8) (BP 3 4)
                           (BP 4 5) (BP 1 9) (BP 1 2) (BP 1 3)
                           (BP 4 6) (BP 1 10) (BP 3 7))
                      Paths))))

(run-tests cfa2-tests)
