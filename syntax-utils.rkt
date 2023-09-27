#lang racket/base
(provide push*!)

(require (for-syntax syntax/parse racket/base))
(require syntax/stx)


; SYNTAX (push*! id expr)
;   The result of `expr` must be a list of identifiers.
;   The identifiers pushed onto the list held by `id`.
(define-syntax (push*! stx)
  (syntax-parse stx
    [(_ id:id e:expr)
     #'(let ([vs e])
         (for ([v (in-list (stx->list vs))])
           (set! id (cons v id))))]))

; > (define x '())
; > (push*! x #'(a b c))
; > x
; '(#'c #'b #'a)


