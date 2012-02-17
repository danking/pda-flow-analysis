;; bpset->fv-hash : [SetOf BP] [FV FV -> FV] -> [Hash AState FV]
;; this needs to be in the scope that contains BP, note that join must be a
;; join on flow values not on states
(define (bpset->fv-hash bps join)
  (for/fold ((hsh (hash)))
      ((bp (in-set bpset)))
    (match-define (BP openfstate fstate) bp)
    (define (add-to-hash fstate hsh)
      (match-define (flow-state astate fv) fstate)
      (hash-set hsh astate (join (hash-ref hsh astate +inf.0)
                                 fv)))

    (add-to-hash openfstate (add-to-hash fstate hsh))))

;; sorts by UID
(define (fv-hash->sorted-list hsh)
  (sort (hash->list hsh)
        (lambda (a b)
          (match-define (abstract-state (node uid-a) _ _) (car a))
          (match-define (abstract-state (node uid-b) _ _) (car b))
          (< uid-a uid-b))))

;; set-add* : [Set X] X ... -> [Set X]
(define (set-add* s . vs)
  (for/fold ((s s)) ((v vs))
    (set-add s v)))

(define-syntax (for/set~ stx)
  (syntax-case stx ()
    [(_ clauses . body)
     #'(for/fold/derived stx ((accum-set (set))) clauses
                         (call-with-values (lambda () . body)
                           (curry set-add* accum-set)))]))
