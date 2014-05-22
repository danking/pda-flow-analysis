#lang racket
(require racket/date)
(provide log-info*)

(define-syntax-rule (log-info* format-string values ...)
  (parameterize ([date-display-format 'iso-8601])
    (log-info (string-append (date->string (current-date) #t)
                             " "
                             format-string)
              values ...)))
