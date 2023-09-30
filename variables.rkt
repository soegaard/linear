#lang racket/base
(provide (all-defined-out))

(require racket/format
         racket/match
         racket/list
         racket/string)

;;; VARIABLE REPRESENTATION

; Each variable is attached a serial number.
; Dendencies are sorted after decreasing(?) serial number.
(define next-serial!
  (let ([next-serial 0])
    (λ ()
      (begin0 next-serial
              (set! next-serial (+ next-serial 1))))))

(define (custom-write-variable x port mode)
  ; mode = #t    write
  ; mode = #f    display
  ; mode = 0, 1  quoting depth for print mode
  (define output (if (independent? x) (~a (name x)) (~ x)))
  (case mode
    [(#t)  (write   output port)]
    [(#f)  (display output port)]
    [(0 1) (print   output port)]))

(struct variable (serial name state)
  #:transparent
  #:mutable
  #:methods gen:custom-write [(define write-proc custom-write-variable)]
  )

(struct state                    ()                            #:transparent #:mutable)
(struct undefined-state   state  ()                            #:transparent #:mutable) ; 1. Variables start here, when declared.
; Numeric
(struct independent-state state  (dependencies equation tuple) #:transparent #:mutable) ; 2. Once indepedent, it never becomes undefined again.
(struct dependent-state   state  (dependency tuple)            #:transparent #:mutable) ; 3. Once dependent,  it almost never becomes independent again.
(struct known-state       state  (value)                       #:transparent #:mutable) ; 4. Once known,      it never becomes dependent again.
; Tuples
(struct tuple-state       state  (tuple)                       #:transparent #:mutable)

; Known:       The value of the variable is known (and stored in the variable).
; Dependent:   The `dependencies` expresses the variable in terms as a weighted
;              sum of independent variables plus a constant.
; Independent: Value unknown and can't be computed yet.
;              - equation is the variable in which the variable was introduced
;              - dependencies is a list of dependency, in which the independent variable is part of
;              - if non-#f, the independent variable is an element of this tuple
;                (if a variable becomes known and is the last remaining unknown element
;                 of the tuple, the tuple itself becomes known)
; Undefined:   Haven't appeared before.

; A depedent variable can turn back into an indepedent variable,
; if one of the variables it depends on turn into an undefined.

(define (serial [x #f])  (if (variable? x) (variable-serial x) (next-serial!)))
(define (name x)         (variable-name x))

(define (undefined? v)     (undefined-state?   (variable-state v)))
(define (known? v)         (known-state?       (variable-state v)))
(define (dependent? v)     (dependent-state?   (variable-state v)))
(define (independent? v)   (independent-state? (variable-state v)))
(define (tuple-var? v)     (and (variable? v) (tuple-state? (variable-state v))))

(define (numeric? x)       (or (number? x) (and (variable? x) (not (tuple-var? x)))))

(define (value v)          (known-state-value              (variable-state v)))
(define (equation v)
  (cond [(dependency? v)  (dependency-cvs v)]
        [(independent? v) (independent-state-equation     (variable-state v))]
        [(dependent? v)   (equation (dependent-state-dependency (variable-state v)))]        
        [else             (error 'equation)]))
(define (dependencies v)   (independent-state-dependencies (variable-state v)))
(define (the-dependency v) (dependent-state-dependency     (variable-state v)))

(define (equations iv) (map dependency-cvs (dependencies iv)))

(define one      (variable (serial) 'one      (known-state 1)))

(define (independent! v deps eq [tuple #f]) (set-variable-state! v (independent-state deps eq tuple)))
(define (dependent!   v dep     [tuple #f]) (set-variable-state! v (dependent-state dep tuple)))
(define (known!       v k)                  (set-variable-state! v (known-state k)))

(struct dependency (variable cvs) #:transparent #:mutable)
(define (the-variable d) (dependency-variable d))

(define (independent-add-dependency! v d)
  (independent! v (cons d (dependencies v)) (equation v)))


;;; FORMATTING

(define (format-variable v)
  (cond
    [(dependent?   v) (format-dependency (the-dependency v))]
    [(undefined?   v) (~a (name v) " (undefined)")]
    [(known?       v) (~a (name v) " = " (value v))]
    [(independent? v) (format-dependencies (dependencies v))]
    [(tuple-var?   v) (~a "<vector-variable>")]
    [(variable?    v) (cond
                        [(vector? (name v)) "some vector variable"]
                        [(tuple-var? v)     "some tuple variable"]
                        [else               "some variable"])]
    [else (displayln v) (error)]))

(define (format-dependency d)
  (match-define (dependency v eq) d)
  (~a (name v) " = " (format-cvs eq)))
  
(define (format-dependencies ds)
  (string-append* (add-between (map format-dependency ds) "\n  ")))

(define (format-eq eq)
  (~a (format-cvs eq) " = 0"))

(define (format-cvs cvs)
  (define (format-constant k)
    (cond
      [(zero? k)     ""]
      [(negative? k) (~a     k)]
      [else          (~a "+" k)]))
  (define (format-term c v)
    (cond
      [(= c  1)      (~a "+"   (name v))]
      [(= c -1)      (~a "-"   (name v))]
      [(negative? c) (~a     c (name v))]
      [else          (~a "+" c (name v))]))
  (define (format-cv cv)
    (define c (car cv))
    (define v (cdr cv))
    (cond
      [(eqv? v 1) (format-constant c)]
      [else       (format-term c v)]))
  (cond
    [(null? cvs) 0]
    [else        (string-trim (string-append* (map format-cv cvs)) "+" )]))

(define (~ x)
  (cond
    [(variable? x)        (format-variable x)]
    [(dependency? x)      (format-dependency x)]
    [(list? x)            (format-cvs x)]    
    [else                 (~a x)]))


;;; LINEAR COMBINATIONS (EQUATIONS)

;(struct combination (coefs vars constant) #:transparent #:mutable)
; represents either the equation:
;   c_0 v_0 + ... + c_n v_n + constant = 0
; or the linear combination
;   c_0 v_0 + ... + c_n v_n + constant 
; depending on context.

;(define (coefficents c) (combination-coefs     c))
;(define (variables   c) (combination-vars      c))
;(define (constant    c) (combination-constant  c))
