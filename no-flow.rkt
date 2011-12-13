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
                       (for/fold ([W W]
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

(define reachability
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
                                          10 (set 11))
                                  s))]
         [pop-succ-states (lambda (push pop)
                            (succ-states pop))])
    (Analysis 1 succ-states pop-succ-states push? pop? state-equal?)))

(CFA2 reachability)
