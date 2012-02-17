#lang racket
(require "cfa2.rkt")
(provide (all-defined-out))

;; bpset->fv-hash : [SetOf BP]
;;                  [FState -> AState FV]
;;                  [FV FV -> FV]
;;                  ->
;;                  [Hash AState FV]
;; the splitter should return two values when given a flow-state, the abstract
;; state and the flow value.
(define (bpset->fv-hash bpset splitter join)
  (for/fold ((hsh (hash)))
      ((bp (in-set bpset)))
    (match-define (BP openfstate fstate) bp)
    (define (add-to-hash fstate hsh)
      (define-values (astate fv) (splitter fstate))
      (hash-set hsh astate (join (hash-ref hsh astate +inf.0)
                                 fv)))

    (add-to-hash openfstate (add-to-hash fstate hsh))))

;; sorts by UID
(define (fv-hash->sorted-list hsh get-uid)
  (sort (hash->list hsh)
        (lambda (a b)
          (< (get-uid a)
             (get-uid b)))))

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
