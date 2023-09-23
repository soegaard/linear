#lang racket
;; WORK IN PROGRESS
;;  [ ] introducing general arithmetic on expressions that might contain variables
;;      [ ]  add*  (soon to be `add`) needs to handle "linear equations" too.
;;  [ ] introduce "combination" for a linear combination.
;;  [ ] Question: Make the constant field a term with a "one variable" ?

;; BIGGER PICTURE
;;   - allow pairs (or vectors) in equations.
;;
;;  [ ] Current experiment: Use plus and minus instead of + and -
;;      to define the binary operations. Also allow vectors as linear terms.
;;      If all terms are vectors, this works as expected.

;;  [ ] But ... how to implement `xpart` ?
;;      Maybe let xpart = #(x whatever) ,
;;      where whatever is some anonymous variable.

;; TODO: Allow linear-term to return a list of cvs.
;;       This allows (vector x y) to be rewritten as (+ (* x one-zero) (* y zero-one)).

(require racket/stxparam racket/splicing)
(require (for-syntax racket/base syntax/parse racket/syntax syntax/stx))
(require (for-syntax (for-syntax syntax/parse racket/base)))

;;; UTILITIES

(begin-for-syntax
  ; SYNTAX (push*! id expr)
  ;   The result of `expr` must be a list of identifiers.
  ;   The identifiers pushed onto the list held by `id`.
  (define-syntax (push*! stx)
    (syntax-parse stx [(_ id:id e:expr)
                       #'(let ([vs e])
                           (for ([v (in-list (stx->list vs))])
                             (set! id (cons v id))))])))

;;; DEBUG

; The flag `debug-mode` affects the way variables are printed.

(define debug-mode #f)
(define (toggle-debug-mode) (set! debug-mode (not debug-mode)))

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

(struct variable                    (serial name state)     #:transparent #:mutable
  ;#:methods gen:custom-write [(define write-proc custom-write-variable)]
  )
(struct state                       ()                      #:transparent #:mutable)
(struct undefined-variable   state  ()                      #:transparent #:mutable) ; 1. Variables start here, when declared.
; Numeric
(struct independent-variable state  (dependencies equation) #:transparent #:mutable) ; 2. Once indepedent, it never becomes undefined again.
(struct dependent-variable   state  (dependency)            #:transparent #:mutable) ; 3. Once dependent,  it almost never becomes independent again.
(struct known-variable       state  (value)                 #:transparent #:mutable) ; 4. Once known,      it never becomes dependent again.
; Tuples
(struct tuple-variable       state  (tuple)                 #:transparent #:mutable)

; Known:       The value of the variable is known (and stored in the variable).
; Dependent:   The `dependencies` expresses the variable in terms as a weighted
;              sum of independent variables plus a constant.
; Independent: Value unknown and can't be computed yet.
;              - equation is the variable in which the variable was introduced
;              - dependencies is a list of dependency, in which the independent variable is part of
; Undefined:   Haven't appeared before.

; A depedent variable can turn back into an indenpedent variable,
; if one of the variables it depends on turn into an undefined.

(define (serial [x #f])  (if (variable? x) (variable-serial x) (next-serial!)))
(define (name x)         (variable-name x))

(define (undefined? v)     (undefined-variable?   (variable-state v)))
(define (known? v)         (known-variable?       (variable-state v)))
(define (dependent? v)     (dependent-variable?   (variable-state v)))
(define (independent? v)   (independent-variable? (variable-state v)))

(define (value v)          (known-variable-value              (variable-state v)))
(define (equation v)
  (cond [(dependency? v)  (dependency-equation v)]
        [(independent? v) (independent-variable-equation     (variable-state v))]
        [(dependent? v)   (equation (dependent-variable-dependency (variable-state v)))]        
        [else             (error 'equation)]))
(define (dependencies v)   (independent-variable-dependencies (variable-state v)))
(define (the-dependency v) (dependent-variable-dependency     (variable-state v)))

(define (equations iv) (map dependency-equation (dependencies iv)))

(define one      (variable (serial) 'one      (known-variable 1)))
(define one-zero (variable (serial) "#(1 0)"  (known-variable 2)))
(define zero-one (variable (serial) "#(0 1)"  (known-variable 3)))

(define (independent! v deps eq) (set-variable-state! v (independent-variable deps eq)))
(define (dependent!   v deps)    (set-variable-state! v (dependent-variable deps)))
(define (known!       v k)       (set-variable-state! v (known-variable k)))

(struct dependency (variable equation) #:transparent #:mutable)
(define (the-variable d) (dependency-variable d))

(define (independent-add-dependency! v d)
  (independent! v (cons d (dependencies v)) (equation v)))

;;; TUPLES

;; We will use vectors to represent constants.
;; That is vectors will allways contains number, never numeric variables.
;; Tuples on the other hand are allowed to contain numbers, numberic variables
;; and linear sums.

(struct tuple (elements) #:transparent #:mutable
  #:constructor-name make-tuple
  #:omit-define-syntaxes)
; where
;   elements is a vector of numbers or numeric variables

(define (tuple . xs)          (make-tuple (list->vector xs)))
(define (elements t)          (tuple-elements t))
(define (tuple-length t)      (vector-length (tuple-elements t)))
(define (tuple-length= t1 t2) (= (tuple-length t1) (tuple-length t2)))

(define (tuple-ref t i)
  (unless (tuple? t) (raise-arguments-error 'ref "tuple expected" "tuple" t))
  (define es (tuple-elements t))
  (define n  (vector-length es))
  (unless (<= 0 i (- n 1)) (raise-arguments-error 'ref "index out of range" "tuple" t "index" i))
  (vector-ref es i))

(define (list->tuple xs)   (tuple (list->vector xs)))
(define (vector->tuple xs) (tuple (vector-copy xs)))

(define tuple-map
  (case-lambda
    [(f t)        (define xs (elements t))
                  (make-tuple (vector-map f xs))]
    [(f t1 t2)    (define xs (elements t1))
                  (define ys (elements t2))
                  (make-tuple (vector-map f xs ys))]
    [(f t1 t2 t3) (define xs (elements t1))
                  (define ys (elements t2))
                  (make-tuple (vector-map f xs ys))]
    [(f . ts)     (define xss (map elements ts))
                  (make-tuple (apply vector-map f xss))]))

  

;;; GENERAL ARITHMETIC

(define (general-length x)
  (cond
    [(vector? x) (vector-length x)]
    [(tuple?  x) (tuple-length  x)]
    [else
     (raise-arguments-error 'general-length "expected vector or tuple" "x" x)]))

(define (general-map f x y)
  (define xs
    (cond
      [(and (vector? x) (vector? y)) (vector-map f x y)]
      [(and (vector? x) (tuple?  y)) (vector-map f x (elements y))]
      [(and (tuple?  x) (vector? y)) (vector-map f (elements x) y)]
      [(and (tuple?  x) (tuple? y))  (vector-map f (elements x) (elements y))]
      [else (raise-arguments-error 'general-map "expected vectors or tuple" "x" x "y" y)]))
  (make-tuple xs))

(define (length= x y) (= (general-length x) (general-length y)))


(define add*
  (case-lambda
    [(x y) (cond
             [(and (number? x) (number? y))               (+ x y)]
             [(and (vector? x) (vector? y) (length= x y)) (vector-map  add x y)]
             [(and (number? x) (vector? y))               (vector-map  add (λ (yi) (+ x  yi)) y)]
             [(and (vector? x) (number? y))               (vector-map  add (λ (xi) (+ xi y))  x)]
             [(and (tuple?  x) (tuple?  y) (length= x y)) (tuple-map   add x y)]
             [(and (vector? x) (tuple?  y) (length= x y)) (general-map add x y)])]
    [(x)   x]))
    



;;; EQUATIONS

(struct linear-equation (coefs vars constant) #:transparent #:mutable)
; represents the equation:
;   c_0 v_0 + ... + c_n v_n + constant = 0 

  
(define (constant-equation? eq)
  (match-define (linear-equation cs vs k) eq)
  (and (empty? cs) (empty? vs)))


(define (format-dependency d)
  (match-define (dependency v eq) d)
  (~a (name v) " = " (format-eq-as-expression eq)))
  
(define (format-dependencies ds)
  (string-append* (add-between (map format-dependency ds) "\n  ")))

(define (format-variable v)
  (cond
    [(dependent?   v) (format-dependency (the-dependency v))]
    [(undefined?   v) (~a (name v) " (undefined)")]
    [(known?       v) (~a (name v) " = " (value v))]
    [(independent? v) (format-dependencies (dependencies v))]
    [else (error)]))

(define (format-eq eq)
  (~a (format-eq-as-expression eq) " = 0"))

(define (format-eq-as-expression eq)
  (define (format-term c v)
    (cond
      [(= c  1)      (~a "+"   (name v))]
      [(= c -1)      (~a "-"   (name v))]
      [(negative? c) (~a     c (name v))]
      [else          (~a "+" c (name v))]))
  (define (format-constant k)
    (cond
      [(negative? k) (~a     k)]
      [else          (~a "+" k)]))
  (match-define (linear-equation cs vs k) eq)
  (string-trim (string-append (string-append* (map format-term cs vs))
                              (format-constant k))
               "+"))

(define (~ x)
  (cond
    [(variable? x)        (format-variable x)]
    [(linear-equation? x) (format-eq x)]
    [(dependency? x)      (format-dependency x)]
    [else                 (~a x)]))


(define (merge xs ys compare<=)
  (define (loop xs ys)
    (cond
      [(empty? xs) ys]
      [(empty? ys) xs]
      [else (define x (car xs))
            (define y (car ys))
            (if (compare<= x y)
                (cons x (loop (rest xs) ys))
                (cons y (loop xs (rest ys))))]))
  (loop xs ys))

(define (uniqify-sorted xs compare join vanish?)
  (define vanished '())
  (define (loop xs)
    (cond
      [(empty? xs) '()]
      [else (define x   (car xs))
            (define xs* (cdr xs))
            (cond
              [(empty? xs*) xs]
              [else (define x* (car xs*))
                    (cond
                      [(compare x x*)
                       (define j (join x x*))
                       (cond
                         [(vanish? j) (set! vanished (cons (cdr x) vanished))
                                      (loop (cdr xs*))]
                         [else        (loop (cons j (cdr xs*)))])]
                      [else
                       (cons x (loop xs*))])])]))
  (values (loop xs)
          vanished))
                            
(define (make-termwise-binary-operator binop [unary #f])
  (define (termwise eq1 eq2)
    ; A `cv` is a (cons c v), where c is a coeffecient (number) and v is a variable
    (define (vanish? cv)      (zero? (car cv)))
    (define (compare cv1 cv2) (<= (serial (cdr cv1)) (serial (cdr cv2))))
    (define (serial= xs ys)   (= (serial (cdr xs)) (serial (cdr ys))))
    (define (join cv1 cv2)    (cons (binop (car cv1) (car cv2)) (cdr cv1))) ; assumes v1=v2
    (match-define (linear-equation cs1 vs1 k1) eq1)
    (match-define (linear-equation cs2 vs2 k2) eq2)
    (define cs+vs1     (map cons cs1 vs1))
    (define cs+vs2     (if unary (map cons (map unary cs2) vs2) (map cons cs2 vs2)))
    (define cs+vs/dups (merge cs+vs1 cs+vs2 compare)) ; merge corresponds to addition
    (define-values (cs+vs vanished)
      (uniqify-sorted cs+vs/dups serial= join vanish?))
    (define cs         (map car cs+vs))
    (define vs         (map cdr cs+vs))
    (values (linear-equation cs vs (binop k1 k2))
            vanished))
  termwise)

(define (remove2 remove-pred xs ys)
  (define vanished '())
  ; Assumes xs and ys have the same length.
  (define (loop xs ys)
    (cond
      [(empty? xs)                     (values xs ys)]
      [(remove-pred (car xs) (car ys)) (set! vanished (cons (list (car xs) (car ys)) vanished))
                                       (loop (cdr xs) (cdr ys))]
      [else                            (define-values (xs* ys*) (loop (cdr xs) (cdr ys)))
                                       (values (cons (car xs) xs*) (cons (car ys) ys*))]))
  (define-values (xs* ys*) (loop xs ys))
  (values xs* ys* vanished))

(define (filter2 keep-pred xs ys)
  (define (loop xs ys)
    (cond
      [(empty? xs)                   (values xs ys)]
      [(keep-pred (car xs) (car ys)) (define-values (xs* ys*) (loop (cdr xs) (cdr ys)))
                                     (values (cons (car xs) xs*) (cons (car ys) ys*))]
      [else                          (loop (cdr xs) (cdr ys))]))
  (loop xs ys))

(define (find2 pred xs ys)
  (define (loop xs ys)
    (cond
      [(empty? xs)              (values #f #f)]
      [(pred (car xs) (car ys)) (values (car xs) (car ys))]
      [else                     (loop (cdr xs) (cdr ys))]))
  (loop xs ys))


(define (map-coeffs f eq) ; -> (values linear-equation vanished-variables)
  ; Map f over the coefficients and the constant in the equation.
  ; If any coeffecients become zero (vanish) return a list of
  ; vanished variables as the second return value.
  (match-define (linear-equation cs vs k) eq)
  (define (remove? c v) (zero? c))
  (define fcs (map f cs))
  (define-values (cs* vs* vanished) (remove2 remove? fcs vs))
  (values (linear-equation cs* vs* (f k))
          (map cadr vanished)))

; find-independent : linear-equation -> (values coef independent-variable)
;       or         : linear-equation -> (value #f #f)
;   Find the independent variable with the greatest absolute value.
(define (find-independent eq)
  (match-define (linear-equation cs vs k) eq)
  (define-values (ics ivs) (filter2 (λ (c v) (independent? v)) cs vs))
  (cond
    [(empty? ics) (values #f #f)]
    [else         (define max-abs (apply max (map abs ics)))
                  (define-values (c v) (find2 (λ (c v) (= (abs c) max-abs)) ics ivs))
                  (values c v)]))

(define (undefined-variables-in-equation eq)
  (match-define (linear-equation cs vs k) eq)
  (filter undefined? vs))

(define (dependent-variables-in-equation eq)
  (match-define (linear-equation cs vs k) eq)
  (filter dependent? vs))

(define (independent-variables-in-equation eq)
  (match-define (linear-equation cs vs k) eq)
  (filter independent? vs))

(define (find-dependent-variable eq)
  (match-define (linear-equation cs vs k) eq)
  (findf dependent? vs))

#;(define (add-dependency-to-independent-variable! v eq iv)
    (define (already? d) (eq? eq (dependency-equation d))
      (unless (findf already? (dependencies iv))
        (define s (variable-state iv))
        (define d (dependency v eq))
        (set-independent-variable-equations! s (cons d (dependencies iv))))))

(define (add-dependency-to-independent-variable! d iv)
  (define s (variable-state iv))
  (set-independent-variable-dependencies! s (cons d (dependencies iv))))


; remove-term : linear-equation variable -> linear-equation
;   Remove the term containing v, if there is one.
(define (remove-term eq v)
  (define s (serial v))
  (match-define (linear-equation cs vs k) eq)
  (define (loop cs vs)
    (cond
      [(empty? cs)             (values cs vs)]
      [(= (serial (car vs)) s) (values (cdr cs) (cdr vs))]
      [else                    (define-values (cs* vs*) (loop (cdr cs) (cdr vs)))
                               (values (cons (car cs) cs*) (cons (car vs) vs*))]))
  (define-values (cs* vs*) (loop cs vs))
  (linear-equation cs* vs* k))

; remove-term* : linear-equation variable -> (values linear-equation coef)
;   Remove the term containing v, if there is one.
;   Return both equation and the coefficient of the removed variable.
(define (remove-term* eq v)
  (define s (serial v))
  (match-define (linear-equation cs vs k) eq)
  (define c-removed #f)
  (define (loop cs vs)
    (cond
      [(empty? cs)             (values cs vs)]
      [(= (serial (car vs)) s) (set! c-removed (car cs))
                               (values (cdr cs) (cdr vs))]
      [else                    (define-values (cs* vs*) (loop (cdr cs) (cdr vs)))
                               (values (cons (car cs) cs*) (cons (car vs) vs*))]))
  (define-values (cs* vs*) (loop cs vs))
  (values (linear-equation cs* vs* k) c-removed))

(define (zero-vector? xs)
  (for/and ([x (in-vector xs)])
    (zero? x)))

(define (general-zero? x)
  (or (and (number? x) (zero? x))
      (and (vector? x) (zero-vector? x))))

(define (plus x [y #f])
  (case y
    [(#f) x]
    [else (cond
            [(and (number? x) (number? y))
             (+ x y)]    
            [(and (vector? x) (vector? y))
             (if (= (vector-length x) (vector-length y))
                 (vector-map + x y)
                 (raise-arguments-error 'plus
                                        "to add two vectors, they must have the same length"
                                        "vec1" x
                                        "vec2" y))]
            [(and (vector? x) (number? y))
             (vector-map (λ (z) (+ z y)) x)]
            [(and (number? x) (vector? y) )
             (vector-map (λ (z) (+ x z)) y)]
            [else
             (raise-arguments-error 'plus
                                    "expected either two numbers or two vectors"
                                    "number-or-vector1" x
                                    "number-or-vector2" y)])]))

(define (minus x [y #f])
  (case y
    [(#f) (cond
            [(number? x) (- x)]
            [(vector? x) (vector-map - x)]
            [else        (error 'minus)])]
    [else (cond
            [(and (number? x) (number? y))
             (- x y)]            
            [(and (vector? x) (vector? y))
             (if (= (vector-length x) (vector-length y))
                 (vector-map - x y)
                 (raise-arguments-error 'minus
                                        "to subtract two vectors, they must have the same length"
                                        "vec1" x
                                        "vec2" y))]
            [(and (vector? x) (number? y))
             (vector-map (λ (z) (- z y)) x)]
            [(and (number? x) (vector? y) )
             (vector-map (λ (z) (- x z)) y)]            
            [else
             (raise-arguments-error 'minus
                                    "expected either two numbers or two vectors"
                                    "number-or-vector1" x
                                    "number-or-vector2" y)])]))

(define (mult x [y #f])
  (case y
    [(#f) x]
    [else (cond
            [(and (number? x) (number? y))
             (* x y)]    
            [(and (vector? x) (vector? y))
             (if (= (vector-length x) (vector-length y))
                 (vector-map * x y)
                 (raise-arguments-error 'mult
                                        "to multiply two vectors, they must have the same length"
                                        "vec1" x
                                        "vec2" y))]
            [(and (number? x) (vector? y))
             (vector-map (λ (z) (* x z)) y)]
            [(and (vector? x) (number? y))
             (vector-map (λ (z) (* y z)) x)]
            [else
             (raise-arguments-error 'multiply
                                    "expected either two numbers or two vectors"
                                    "number-or-vector1" x
                                    "number-or-vector2" y)])]))


(define add
  (let ()
    (define termwise-add (make-termwise-binary-operator plus plus))
    (λ (eq1 eq2) (termwise-add eq1 eq2))))

(define subtract
  (let ()
    (define termwise-subtract (make-termwise-binary-operator minus minus))
    (λ (eq1 eq2) (termwise-subtract eq1 eq2))))

(define (scale k eq)
  (define-values (eq* vanished) (map-coeffs (λ (c) (mult k c)) eq))
  eq*)

(define (isolate eq c v)
  ; Assumes c*v is a term of eq.
  (define eq-cv (remove-term eq v))
  (scale (/ -1 c) eq-cv))

(define (reduce-known eq)
  (match-define (linear-equation cs vs k) eq)
  (define (loop cs vs known-k)
    (cond
      [(empty? cs) (values '() '() known-k)]
      [else        (define c (car cs))
                   (define v (car vs))
                   (cond
                     [(known? v) (define k (value v))
                                 (loop (cdr cs) (cdr vs) (plus (mult c k) known-k))]
                     [else       (define-values (cs* vs* k*) (loop (cdr cs) (cdr vs) known-k))
                                 (values (cons c cs*) (cons v vs*) k*)])]))
  (loop cs vs k))

(define (reduce-known! eq)
  (define-values (cs vs k) (reduce-known eq))
  (set-linear-equation-coefs!    eq cs)
  (set-linear-equation-vars!     eq vs)
  (set-linear-equation-constant! eq k))

(define (eliminate-dependent eq dv)
  (define-values (eq-dv c) (remove-term* eq dv))
  (cond
    [c (match-define (linear-equation cs  vs  k) eq-dv)
       (define-values (eq* van) (add eq-dv (scale c (equation dv))))
       eq*]
    [else
     eq]))

(define (eliminate-dependent! eq dv)
  (define req (eliminate-dependent eq dv))
  (set-linear-equation-coefs!    eq (linear-equation-coefs    req))
  (set-linear-equation-vars!     eq (linear-equation-vars     req))
  (set-linear-equation-constant! eq (linear-equation-constant req)))

(define (remove-all-dependent-variables! eq)
  (define dv (find-dependent-variable eq))
  (when dv
    (eliminate-dependent! eq dv)
    (remove-all-dependent-variables! eq)))

;(define (reduce-newly-known! deps)
;  (cond
;    [(empty? deps) (void)]
;    [else          (define d (first deps))
;                   (define e (equation d))
;                   (reduce-known! e)
;                   (cond
;                     [(constant-equation? e)
;                      ; now, the variable in d is known
;                      (define v  (the-variable d))
;                      (define k (linear-equation-constant e))
;                      (known! v k)

(define-syntax (== stx)
  (syntax-parse stx
    [(_ s1 s2)
     #:with error-loc (datum->syntax #f 1 stx)
     #'(void
        (let ()
          ; Rewrite s1=s2 to s1-s2=0.         
          (define-values (eq vanished) (subtract (linear-sum s1) (linear-sum s2)))
         ; Make undefined variables in the equation independent.
         (for ([u (undefined-variables-in-equation eq)])
           (independent! u '() (list eq))) ; no deps, eq the introducing equation
         ; Note: Remove all dependent variables from the equation.
         ;       Dependent variables will only depend on independent variables.
         ;(displayln (list "About to eliminate dependent variables" (~ eq)))
         ;(displayln eq)
         ;(displayln "---")
         (remove-all-dependent-variables! eq)
         #;(for ([dv (dependent-variables-in-equation eq)])
             ; (displayln (~a "eliminating dep: " (~ dv)))
             (eliminate-dependent! eq dv))
         ;(displayln (list "Are all dependent variables gone?" (~ eq)))
         ;(displayln eq)
         
         ; If any independent variables occur in the equation, they need to be
         ; added to set of equations associated with independent variables.
         #;(for ([iv (independent-variables-in-equation eq)])
             (add-equation-to-independent-variable! eq iv))

         ; If at this point new variables have become known, they need to
         ; be eliminated too.
         
         ; (displayln (list 'after-elimination-of-dependent-vars eq))
         (match-define (linear-equation cs vs k) eq)
         ; A constant equation with a non-zero constant represents k=0.
         ; Signal an error
         (when (and (empty? cs) (empty? vs)
                    (not (zero? k)))
           (raise-syntax-error '==
                               "this relation led to inconsistent equations"
                               #'error-loc))

         (define-values (c v) (find-independent eq))
         (cond
           ; We found an independent variable, make it dependent.
           [(and c v)
            ; The dependencies in which the indendent v is used.
            (define deps (dependencies v))
            ; Isolate v in eq to get an equation for v.
            (define deq (isolate eq c v))
            (cond
              [(constant-equation? deq)
               ; The value for v is now known.
               (known! v (linear-equation-constant deq))
               ; The dependencies where v occurs can now be reduced.
               (for ([d (in-list deps)])
                 (define e (equation d))
                 (reduce-known! e)
                 ; If the reduced equation is a constant,
                 ; then the dependent variable is (now also) known.
                 (when (constant-equation? e)
                   (define k (linear-equation-constant e))
                   (known! (the-variable d) k)))
               eq]
              [else
               ; The newly discovered dependency for v.
               (define new-dep (dependency v deq))
               ; The dependencies where the previously independent v occur.
               (define old-deps (dependencies v)) 
               ; Now v is dependent.
               (dependent! v new-dep)
               ; The new dependency might contain other independent variables.
               (for ([iv (independent-variables-in-equation deq)])
                 (independent-add-dependency! iv new-dep))
               ; Update dependencies featuring v.
               (for ([d (in-list deps)])
                 (define e (equation d))
                 (eliminate-dependent!  e v)
                 ; The elimination might introduce new independent variables in d.
                 ; If so d must be added to the dependencies of the newly introduced variables.
                 (for ([iv (independent-variables-in-equation e)])
                   (unless (memq d (dependencies iv))
                     (independent-add-dependency! iv d))))
               eq])]
           ; No independent variable
           [else
            (displayln "all variables are dependent or known")])))]
    [(_ s1 s2 s3 ...)
     #'(begin (== s1 s2)
              (== s2 s3 ...))]))

;; Mediation. Notation in MetaFont/MetaPost t[x1,x2].
(define (med t x1 x2)
  (+ x1 (* t (- x2 x1))))


(define-syntax (linear-sum stx)
  ; (displayln (syntax->datum stx))
  (syntax-parse stx
    #:literals (+ - med)
    ; Rewrite mediation.
    [(_linear-sum (med t t1 t2))
     (syntax/loc stx (linear-sum (+ (med t t1 t2))))]
    [(_linear-sum (+ term1 ... (med t t1 t2) term4 ...))
     ; (med t t1 t2) = t1 + t*(t2-t1) = t1 + t*t2 + t*(-t1)      
     (syntax/loc stx (linear-sum (+ term1 ... t1 (* t t2) (* (- t) t1)) term4 ...))]

    ; Rewrite differences to sums.
    [(_linear-sum (- term1 term2 term ...))
     (syntax/loc stx (linear-sum (+ term1 (- term2) (- term) ...)))]
    [(_linear-sum (+ term0 ... (- term1 term2 term ...) term3 ...))
     (syntax/loc stx (linear-sum (+ term0 ... term1 (- term2) (- term) ... term3 ...)))]
    ; Remove double negation.
    [(_linear-sum term ... (- (- term1)) term2 ...)
     (syntax/loc stx (linear-sum term ... term1 term2 ...))]
    
    ; At this point all terms of the form (- t1 t2) are gone.
    [(_linear-sum (+ term ...))
     #:with loc (datum->syntax #f 'loc (with-syntax ([(_ t) stx]) #'t))
     (syntax/loc #'loc
       (let ()
         (define (vanish? cv)      (general-zero? (car cv)))
         (define (compare cv1 cv2) (<= (serial (cdr cv1)) (serial (cdr cv2))))
         (define (serial= xs ys)   (= (serial (cdr xs)) (serial (cdr ys))))
         (define (join cv1 cv2)    (cons (plus (car cv1) (car cv2)) (cdr cv1))) ; assumes v1=v2

         (define terms                 (list (linear-term loc term) ...))
         (define terms/dups            (sort terms compare))
         (define-values (cvs vanished) (uniqify-sorted terms/dups serial= join vanish?))
         (define cs                    (map car cvs))
         (define vs                    (map cdr cvs))
         (cond
           ; note: compare with place `one` first, since it has the lowest serial 
           [(and (not (empty? vs)) (eq? (car vs) one))
            (define k (car cs))
            (linear-equation (cdr cs) (cdr vs) k)]
           [else
            (linear-equation cs vs 0)])))]
    ; Single term in sum.
    [(_linear-sum term)
     #:with loc (datum->syntax #f 'loc (with-syntax ([(_ t) stx]) #'t))
     (syntax/loc #'term
       (let ()
         (define cv (linear-term loc term))
         (cond
           [(eq? (cdr cv) one)
            (define k (car cv))
            (linear-equation '() '() k)]
           [else
            (linear-equation (list (car cv)) (list (cdr cv)) 0)])))]))


(define-syntax (linear-term stx)
  ; (displayln (list 'linear-term (syntax->datum stx)))
  (syntax-parse stx
    #:literals (* - first second)
    [(_linear-term loc (- (* e1 e2)))     #'(linear-term loc (* -1 e1 e2))]
    [(_linear-term loc (* (- e1) e2))     #'(linear-term loc (* -1 e1 e2))]
    [(_linear-term loc (* e1 (- e2)))     #'(linear-term loc (* -1 e1 e2))]
    [(_linear-term loc (* (- e1) (- e2))) #'(linear-term loc (*    e1 e2))]
    [(_linear-term loc (* e1 e2))         #'(linear-term loc (*  1 e1 e2))]
    [(_linear-term loc (* k e1 e2))
     #:with error-loc #'loc #;(with-syntax ([(_ t) stx]) (datum->syntax #f 1 #'t))
     #'(let ()
         (define v1 e1)
         (define v2 e2)
         (displayln (list 'v1 v1 'v2 v2))
         (define cv
           (cond
             [(and (number? v1) (number? v2))
              (cons (* k v1 v2) one)]
             [(and (number? v1) (variable? v2))
              (cons (* k v1) v2)]
             [(and (variable? v1) (number? v2))
              (cons (* k v2) v1)]
             [(and (number? v1) (vector? v2))
              (cons (vector-map (λ (x) (* k v1 x)) v2) one)]
             [(and (vector? v1) (number? v2))
              (cons (vector-map (λ (x) (* k v2 x)) v1) one)]
             ; TODO: variable * vector ?             
             ; todo: can we allow a known variable here?
             [else 
              (raise-syntax-error
               'linear-term
               "a product term must be between two numbers, or between a number and a variable"
               #'error-loc)]))
         cv)]
    [(_linear-term loc (- e))
     #'(let ()
         (define v e)
         (cond
           [(number? v)   (cons (- v) one)]
           [(vector? v)   (cons (vector-map - v) one)]
           [(variable? v) (cons -1 v)]
           [else
            (raise-syntax-error
               'linear-term
               "negation expects a variable or an expression that evaluates to a number"
               #'error-loc)]))]
    [(_linear-term loc e)
     (syntax/loc #'loc
       (let ()
         (define v e)
         (cond
           [(number? v)   (cons v one)]
           [(vector? v)   (cons v one)]
           [(variable? v) (cons 1 v)]
           [else
            (raise-syntax-error
             'linear-term
             "a numeric term must evaluate to a number or a variable"
             #'loc)])))]))
    





;;; DECLARED VARIABLES

(begin-for-syntax
  ;; Module Level Variables
  (define module-level-declared-variables '()) ; list of identifiers
  (define (add-module-level-variables! ids)
    (push*! module-level-declared-variables (stx->list ids)))
  ;; Local Variables
  ;; - each internal definition context is given an index
  (define intdefs (make-hasheq))
  ;; - each index is associated to a list of declared names
  (define local-variables (make-hash))
  
  (define (new-intdef? intdef)          (not (hash-has-key? intdefs intdef)))
  (define (index-of-intdef intdef)      (hash-ref! intdefs intdef (hash-count intdefs)))
  (define (get-local-variables index)   (hash-ref local-variables index))
  (define (add-local-variable! index id)
    (hash-update! local-variables index (λ (old-vars) (cons id old-vars)) '()))
  (define (add-local-variables! index vars)
    (for ([id (stx->list vars)]) (add-local-variable! index id))))

;; SYNTAX PARAMETER  variables
;;   When applied expands to a list with the declared variables in scope.
(define-syntax-parameter variables
  (λ (stx) (with-syntax ([(id ...) module-level-declared-variables])
             #''(id ...))))


;; SYNTAX (declare id ...)
;;   Declare that the variables id ... are "declared" variables.
(define-syntax (declare stx)
  (syntax-parse stx
    [(_declare id ...)
     (define ids (stx->list #'(id ...)))

     (define (get-outer-variables)
       (local-expand(with-syntax ([variables (syntax-local-get-shadower #'variables)])
                      #'(variables))
                    ctx '()))
     
     (define (do-define-ids)
       (with-syntax ([($id ...) (for/list ([id ids]) (format-id stx "$~a" id))])
         #'(begin
             (define $id (variable (serial) 'id (undefined-variable))) ...
             (define-syntax id (λ (stx)
                                 #'(let ()
                                     (define v $id)
                                     (cond
                                       [(known?        v) (value v)]
                                       [(undefined?    v) v]
                                       [(independent?  v) v]
                                       [(dependent?    v) v]
                                       [(tuple?        v) v]
                                       [else
                                        (displayln v)
                                        (error 'unknown)])))) ...)))
     
     ; - the expansion on `declare` depends on where it is used.
     (define ctx (syntax-local-context))
     (case ctx 
       [(module)
        (add-module-level-variables! ids)
        (do-define-ids)]
       [(expression)
        (raise-syntax-error 'declare "not allowed in an expression context" stx)]
       [else ; local context
        ; - find the local variables in outside this scope
        (define vars (get-outer-variables))
        ; - if we are in a new scope, we must reparameterize `variables`
        ; - if not simply add the new identifiers 
        (define new-scope? (new-intdef? ctx))
        (define index      (index-of-intdef ctx))
        (cond
          [new-scope?
           (add-local-variables! index #'(id ...))
           
           (with-syntax ([variables               (format-id stx "variables")]
                         [(_quote (outer-id ...)) vars]
                         [index                   index]
                         [....                     #'(... ...)]
                         [defs                     (do-define-ids)])

             #'(begin
                 defs
                 (define-syntax-parameter variables
                   (λ (stx)
                     (with-syntax ([(local-id ....) (get-local-variables index)])
                       #''(local-id .... outer-id ...))))))]
          [else
           (add-local-variables! index #'(id ...))
           (do-define-ids)])])]))

;;; Test

(module+ test

  (require rackunit)
  (check-equal? (let ()
                  (declare a)
                  (== a 1)
                  a)
                1)
  (check-equal? (let ()
                  (declare a b)
                  (== a 1)
                  (== b 2)
                  (list a b))
                '(1 2))
  (check-equal? (let ()
                  (declare a b)
                  (== a (+ b 1))
                  (== b 2)
                  (list a b))
                '(3 2))
  (check-equal? (let ()
                  (declare a b)
                  (== a (+ b 1))
                  (== (+ a b) 5)
                  (list a b))
                '(3 2))
  (check-equal? (let ()
                  (declare a b)
                  (== a (+ b 1))
                  (== a 5)
                  (list a b))
                '(5 4))
  (check-equal? (let ()
                  (declare a b)
                  (== (* 2 a) b)
                  (== b 8)
                  (list a b))
                '(4 8))
  (check-equal? (let ()
                  (declare a b)
                  (== a (* 2 b))
                  (== b 8)
                  (list a b))
                '(16 8))
  (check-equal? (let ()
                  (declare a b c)
                  (== (+ a b) c)
                  (== (+ b c) 5)
                  (== (+ a c) 4)
                  (list a b c))
                '(1 2 3))
  (check-equal? (let ()
                  (declare a b c)
                  (== a b c)
                  (== b 2)
                  (list a b c))
                '(2 2 2))
  (check-equal? (let ()
                  (declare a b c)
                  (== (- a) b (- (- c)))
                  (== b 2)
                  (list a b c))
                '(-2 2 2))
  (check-equal? (let ()
                  (declare a b c)
                  (== a 1/2)
                  (== b 2)
                  (== (med a b c) 7)
                  (list a b c))
                '(1/2 2 12)))

;(variables)                   ;                    ()
;(declare a b)
;(variables)                   ;             (a b    )
;(let ()
;  (declare c d)  
;  (displayln (variables))     ; (    i j c d a b g h)
;  (let ()
;    (declare e f)
;    (displayln (variables)))  ; (e f i j c d a b g h)
;  (declare i j)
;  (displayln (variables)))    ;     (i j c d a b g h)
;(variables)                   ;             (a b    )
;(declare g h)
;(variables)                   ;             (a b g h) 


; (== (+ a b) 4)   -> (+ (*  1 a) (* 1 b) -4)
; (== (- a b) 4)   -> (+ (* -1 a) (* 1 b) -4)
; (== (* 2 a) 4)   -> (+ (*  2 a)         -4)
; (== (+ a a b) 8) -> (+ (*  2 a) (* 1 b) -8)
; (== a 3)         -> (+ (*  1 a)         -3)   
; (== (* x a) 4)   -> (+ (*  x a)         -4)

; (:= a 3)



; (declare a b c d e)

;(define eq1 (linear-equation '(1   2  3 4)  (list a b c d) 6))
;(define eq2 (linear-equation '(10 20 -3 50) (list a b c e) 60))
;(add eq1 eq2)
;(subtract eq1 eq2)
;(map-coeffs (λ (x) (* 2 x)) eq1)

; > (declare a b c)
; a=undefined,      b=undefined, c=undefined
; > (== a (+ b 2))
; a=dependent(b+2), b=independent, c=undefined
; > (== b (+ c 3))
; a=dependent(b+2), b=dedendent(c+3), c=indepedent
; > (== c 2)
; a=dependent(b+2), b=dedendent(c+3), c=2
 
;(define (show)
;  (displayln (~ a))
;  (displayln (~ b))
;  (displayln (~ c)))

  
