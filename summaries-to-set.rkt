#lang racket
(require (only-in "../../racket-utils/similar-sets.rkt"
                  get-basic-set)
         (only-in "../../racket-utils/set-utilities.rkt"
                  for/set-union)
         "../racket-utils/option.rkt")
(provide summaries->set
         get-summaries)

(define (summaries->set sums)
  (for/set-union ((x (get-basic-set sums)))
    (if (set? x) (for/set ((x x)) x) (set x))))

(define (get-summaries Summaries open)
  (match (set-get-similar Summaries (BP open #f))
    ((some similar-summaries)
     (some (for/fold ([gte-summaries (basic-set)])
               ([summary (if (basic-set? similar-summaries) similar-summaries (basic-seteq similar-summaries))]
                #:when (match summary
                         ((BP open2 _) (gte open2 open))))
             (basic-set-add gte-summaries summary))))
    ((none) (none))))
