#lang racket

(provide (struct-out BP) BP->pair)

;; BP : OpenState × State
(define-struct BP (open node) #:transparent)

;; BP->pair : BP -> [List OpenState x State]
(define (BP->pair bp)
  (list (BP-open bp) (BP-node bp)))
