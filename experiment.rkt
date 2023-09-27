#lang racket

(require "variables.rkt"
         racket/stxparam)

(require (for-syntax racket/syntax
                     syntax/parse
                     syntax/stx
                     "syntax-utils.rkt"))

; One dimensional linear equation

; equation  :=   (== sum sum ...)
; sum       :=   terms
;            |   (+ terms ...)
;            |   (- terms ...)
; terms     :=   term
;            |   (+ terms ...)
;            |   (- terms ...)
; term      :=   product
; product   :=   numeric
;            |   (* number ... numeric) ; order of factors not important
;            |   (- product)
;            |   (+ product)
; numeric   :=   number
;            |   variable
;            |   expression             ; that evaluates to a number or variable

;;; Representation
;;   - numeric   is a number or as a symbol
;;   - product   is represented as a (cons number symbol) or (cons number 1)
;;   - term      is represented as a product
;;   - terms     is represented as a list of product
;;   - sum       is represented as a list of product
;;   - equation  is represented as a list of list of product


;;; DECLARED VARIABLES

(begin-for-syntax
  ;; Module Level Variables
  (define module-level-declared-variables '()) ; list of identifiers
  (define (add-module-level-variables! ids)
    (push*! module-level-declared-variables
            (map syntax-local-introduce (stx->list ids))))
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
    (for ([id (stx->list vars)]) (add-local-variable! index id)))

  (define (declared? x)
    (define quoted-vars ((syntax-parameter-value #'show) 'ignored))
    (syntax-parse quoted-vars
      [(_quote vars-stx)
       (and (member x (syntax->list #'vars-stx) free-identifier=?))]
      [_ (error 'declared "unexpected")])))

;; SYNTAX PARAMETER  show
;;   When applied expands to a list with the declared variables in scope.
(define-syntax-parameter show
  (λ (stx) (with-syntax ([(id ...) module-level-declared-variables])
             #''(id ...))))

;; SYNTAX (declare id ...)
;;   Declare that the variables id ... are "declared" variables.
(define-syntax (declare stx)
  (syntax-parse stx
    [(_declare id ...)
     (define ids (stx->list #'(id ...)))

     (define (get-outer-variables)
       (local-expand(with-syntax ([show (syntax-local-get-shadower #'show)])
                      #'(show))
                    ctx '()))
     
     (define (do-define-ids)
       (with-syntax ([($id ...) (for/list ([id ids]) (format-id stx "$~a" id))])
         #'(begin
             (define $id (variable (serial) 'id (undefined-state))) ...
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
     
     ; - the expansion of `declare` depends on where it is used.
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
           
           (with-syntax ([show                    (format-id stx "show")]
                         [(_quote (outer-id ...)) vars]
                         [index                   index]
                         [....                     #'(... ...)]
                         [defs                     (do-define-ids)])

             #'(begin
                 defs
                 (define-syntax-parameter show
                   (λ (stx)
                     (with-syntax ([(local-id ....) (get-local-variables index)])
                       #''(local-id .... outer-id ...))))))]
          [else
           (add-local-variables! index #'(id ...))
           (do-define-ids)])])]))



(begin-for-syntax

  (define-syntax-class variable
    #:description "variable"
    #:opaque  ; note: error in terms of "variable" and not identifier
    (pattern var:identifier #:when (declared? #'var)))

  (define-syntax-class numeric
    #:description "numeric (number or variable)"
    #:opaque
    #:literals (unquote)
    (pattern v:variable)
    (pattern n:number)
    (pattern e:expr))

  (define-syntax-class product
    #:description "product"
    #:literals (* - +)
    (pattern p:numeric)
    ; a factor is a number, a (declared) variable, a nested product or an expression
    (pattern (* factor ...)) 
    (pattern (- p:product))
    (pattern (+ p:product)))

  (define-syntax-class term
    #:description "term"
    (pattern t:product))

  (define-syntax-class terms
    #:description "terms"
    #:literals (+ -)
    (pattern t:term)
    (pattern (+ tss:terms ...))
    (pattern (- tss:terms ...)))

  (define-syntax-class sum
    #:description "sum"
    #:literals (+ -)
    (pattern ts:terms)
    (pattern (+ tss:terms ...))
    (pattern (- tss:terms ...)))

  (define-syntax-class equation
    #:description "equation"
    #:literals (==)
    (pattern (== s:sum ss:sum ...)))
  )

;; SYNTAX (nice-top . id)
;;   Throw error with error location taken from `id`.
(define-syntax (nice-top stx)
  (syntax-case stx ()
    [(_top . x)
     (raise-syntax-error 'numeric "unbound identifier" #'x)]))

(define-syntax (with-top stx)
  (syntax-parse stx
    [(_ e:expr)
     (with-syntax ([#%top (syntax-local-introduce #'#%top)])
       #'(let-syntax ([#%top (make-rename-transformer #'nice-top)])
           e))]))


;; The following three macros will wrap user provided expressions.
;; The `with-top` makes sure that "unbound identifier" errors
;; report the correct error location.

(define-syntax (numeric stx)
  (syntax-parse stx
    [(_numeric n:numeric)
     (syntax-parse #'n
       [x:number         #'x]
       [v:variable       #''v]
       [e:expr
        (syntax/loc #'e
          (with-top (let ([v e])
                      (unless (or (number? v) (variable? v))
                        (raise-syntax-error 'numeric
                                            "expected a number or a variable"
                                            #'e))
                      v)))])]))

(define-syntax (number-expression stx)
  (syntax-parse stx
    [(_ e:expr)
     (syntax/loc #'e
       (with-top
           (let ([v e])
             (unless (number? v)
               (raise-syntax-error 'number-expression
                                   "expected a number"
                                   #'e))
             v)))]))


(define-syntax (product stx)
  (syntax-parse stx
    #:literals (* - +)
    [(_product (* f ...))
     ; A factor f can be either a number, a (declared) variable,
     ; a nested product of the form (* f ...) or an expression.
     (define (number-datum? f) (number? (syntax-e f)))
     (define (var? f)          (and (identifier? f) (declared? f)))
     (define (product? f)      (syntax-parse f #:literals (*) [(* f ...) #t] [_ #f]))
     (define (other? f)        (not (or (number-datum? f) (var? f) (product? f))))
     
     (define fs (syntax->list #'(f ...)))
     (define ns (filter number-datum? fs))
     (define vs (filter var?          fs))
     (define ps (filter product?      fs))
     (define es (filter other?        fs))
       
     (when (> (length vs) 1)
       (raise-syntax-error 'product
                           "at most one variable allowed in a product"
                           (cadr vs)))
     ; We can compute the product of the number datums at compile time
     (define ns-prod (apply * (map syntax-e ns)))

     (cond
       ; If there are nested products, flatten them.
       [(> (length ps) 0)
        (with-syntax ([n ns-prod] [(v ...) vs] [((_ f ...) ...) ps] [(e ...) es])
          (syntax/loc stx
            (product (* n v ... f ... ... e ...))))]

       ; One variable v0 present => no variables allowed in the expressions
       [(and (= (length vs) 1) (= (length es) 0))
        (with-syntax ([n ns-prod] [(v0 . more) vs])
          #'(cons n v0))]
       [(and (= (length vs) 1))
        (with-syntax ([n ns-prod] [(v0 . more) vs] [(e ...) es])
          #'(let ([ns (list (number-expression e) ...)])
              (cons (* n (apply * ns)) v0)))]
       ; No variable present => one variable allowed in the expressions
       [(and (= (length vs) 0) (= (length es) 0))
        (with-syntax ([n ns-prod])
          #'(cons n 1))]
       [(= (length vs) 0)
        (with-syntax ([n ns-prod] [(e ...) es])
          (syntax/loc stx
            (let ([xs (list (numeric e) ...)])
              (define ns (filter number?   xs))
              (define vs (filter variable? xs))
              (define m (apply * ns))
              (when (> (length vs) 1)
                (raise-syntax-error 'product
                                    "more than one expression evaluated to a variable"
                                    #'_product))
              (if (null? vs)
                  (cons (* n m) 1)
                  (cons (* n m) (car vs))))))])]
    
    [(_product (- p:product))                 #'(let ()
                                                  (define cv (product p))
                                                  (cons (* -1 (car cv)) (cdr cv)))]
    [(_product (+ p:product))                 #'(product p)]
    ; This needs to be last, s.t. (* 2 a) is not seen as an expression by `numeric`.
    [(_product n:numeric)
     (syntax-parse #'n
       [n:number   #'(cons n 1)]
       [v:variable #'(cons 1 'v)]
       [e:expr     #'(let ([v (numeric e)])
                       (if (number? v)
                           (cons v 1)
                           (cons 1 v)))])]))
     
(define-syntax (term stx)
  (syntax-parse stx
    [(_term p:product)  #'(product p)]))

(define (negate-coefficents cvs)
  (map (λ (cv) (cons (- (car cv)) (cdr cv))) cvs))
         
(define-syntax (terms stx)
  (syntax-parse stx    
    #:literals (+ -)
    [(_terms (+ tss:terms ...))           #'(append (terms tss) ...)]
    [(_terms (- t:term))                  #'(negate-coefficents (terms t))]
    [(_terms (- ts:terms tss:terms ...))  #'(append (terms ts)
                                                    (negate-coefficents (append (terms tss) ...)))]
    [(_terms t:term)                      #'(list (term t))]))

(define-syntax (sum stx)
  (syntax-parse stx
    #:literals (+ -)
    [(_sum (+ tss:terms ...))           #'(append (terms tss) ...)]
    [(_sum (- ts0:terms))               #'(negate-coefficents (terms ts0))]
    [(_sum (- ts0:terms tss:terms ...)) #'(append (terms ts0)
                                                  (negate-coefficents (append (terms tss) ...)))]
    [(_sum ts:terms)                    #'(terms ts)]))

(define-syntax (==1 stx)
  (syntax-parse stx
    [(_ s1:sum s2:sum)                  #'(canonical
                                           (append (sum s1)
                                                   (negate-coefficents (sum s2))))]))

(define-syntax (== stx)
  (syntax-parse stx
    #:literals (==)
    [(_== s1:sum)                     #'(list (==1 s1 0))]
    [(_== s1:sum s2:sum)              #'(list (==1 s1 s2))]
    [(_-- s1:sum s2:sum ss:sum ...)   #'(cons (==1 s1 s2)
                                              (== s2 ss ...))]))

(define (cv<= cv1 cv2)
  (variable<= (cdr cv1) (cdr cv2)))

(define (variable<= v1 v2)
  (or (eqv? v1 1)
      (and (not (eqv? v1 v2))
           (<= (serial v1) (serial v2)))))
; For symbols as variables:
#;(string<=? (symbol->string v1) (symbol->string v2))

(define (variable= v1 v2)
  (equal? v1 v2))

(define (sort-cvs cvs)
  (sort cvs cv<=))

(define (collect-cvs cvs)
  ; - collect adjacent terms with the same variable into one cv
  ; - remove terms with coefficient zero
  (cond
    [(null? cvs)       '()]
    [(null? (cdr cvs)) (define c (caar cvs))
                       (if (= c 0) '() cvs)]
    [else              (define cv1  (car cvs))
                       (define cv2  (cadr cvs))
                       (cond
                         [(variable= (cdr cv1) (cdr cv2))
                          (define c (+ (car cv1) (car cv2)))
                          (if (= c 0)
                              (collect-cvs (cddr cvs))
                              (collect-cvs (cons (cons c (cdr cv1))
                                                 (cddr cvs))))]
                         [else
                          (define c (car cv1))
                          (if (= c 0)
                              (collect-cvs (cdr cvs))
                              (cons cv1 (collect-cvs (cdr cvs))))])]))

(define (canonical cvs)
  (collect-cvs (sort-cvs cvs)))


(define (cvs-variables cvs)
  ; In sorted order according to variable<= .
  ; If there is a constant term, the first variable is 1.
  (map cdr cvs))

(define (cvs-coeffs cvs)
  ; If there is a constant term, the first coefficient is the constant.
  (map car cvs))

(define (cvs-constant cvs)
  (cond
    [(null? cvs) 0]
    [else        (define cv (car cvs))
                 (if (eqv? 1 (cdr cv))
                     (car cv)
                     0)]))

(define (cvs-zero? cvs)
  (null? cvs))

(define (cvs-add-cv cvs cv)
  ; - returns cvs in sorted order without 0 as coef.
  (cond
    [(null? cvs) (if (= (car cv) 0)
                     '()
                     (list cv))]
    [else        (define cv0 (car cvs))
                 (cond
                    [(variable= (cdr cv) (cdr cv0))   (define c (+ (car cv0) (car cv)))
                                                      (if (= c 0)
                                                          (cdr cvs)
                                                          (cons (cons c (cdr cv))
                                                                (cdr cvs)))]
                    [(variable<= (cdr cv) (cdr cv0))  (cons cv
                                                            cvs)]
                    [else                             (cons (car cvs)
                                                            (cvs-add-cv (cdr cvs) cv))])]))

(define (cvs-add-cvs cvs1 cvs2)
  ; - returns cvs in sorted order without 0 as coef.
  (cond
    [(null? cvs1)  cvs2]
    [(null? cvs2)  cvs1]
    [else          (define cv1 (car cvs1))
                   (define cv2 (car cvs2))
                   (cond
                     [(variable= (cdr cv1) (cdr cv2))
                      (define c (+ (car cv1) (car cv2)))
                      (if (= c 0)
                          (cvs-add-cvs (cdr cvs1) (cdr cvs2))
                          (cons (cons c (cdr cv1))
                                (cvs-add-cvs (cdr cvs1) (cdr cvs2))))]
                     [(variable<= (cdr cv1) (cdr cv2))
                      (cons cv1 (cvs-add-cvs (cdr cvs1) cvs2))]
                     [else
                      (cons cv2 (cvs-add-cvs  cvs1 (cdr cvs2)))])]))

(define (cvs-scale k cvs)
  (cond
    [(= k 0) '()]
    [(= k 1) cvs]
    [else    (let loop ([cvs cvs])
               (cond
                 [(null? cvs) '()]
                 [else        (define cv (car cvs))
                              (cons (cons (* k (car cv)) (cdr cv))
                                    (loop (cdr cvs)))]))]))

(define (cvs-subtract-cvs cvs1 cvs2)
  (cvs-add-cvs cvs1 (cvs-scale -1 cvs2)))

(define (cvs-remove-constant cvs)
  (cond
    [(null? cvs) '()]
    [else        (define cv (car cvs))
                 (if (= (cdr cv) 1)
                     (cdr cvs)
                     cvs)]))
      

(define (cvs-remove-term-with-variable cvs v)
  ; return two values:
  ;   first value:   #f of the variable v is not in cvs,
  ;                  otherwise c the coefficient in (cons c v)
  ;   second value:  cvs with the v term removed.
  (define c #f)
  (define cvs*
    (let loop ([cvs cvs])
      (cond
        [(null? cvs) '()]
        [else        (define cv (car cvs))
                     (cond
                       [(variable= (cdr cv) v)
                        (set! c (car cv))
                        (cdr cvs)]
                       [else
                        (cons cv (loop (cdr cvs)))])])))
  (values c cvs*))

(define (cvs-isolate cvs v)
  (define-values (c cvs-cv) (cvs-remove-term-with-variable cvs v))
  (cond
    ; v was found with coef c
    [c (when (= c 0)
         (error 'cvs-isolate "internal-error, invariant that c<>0 violated"))
       (define -c (- c))
       (map (λ (cv) (cons (/ (car cv) -c) (cdr cv)))
            cvs-cv)]
    ; v was not found
    [else
     #f]))

(define (cvs-substitute cvs v cvs2)
  ; insert v=cvs2 into cvs
  (define-values (c cvs-cv) (cvs-remove-term-with-variable cvs v))
  (cond
    [c (define cvcs2 (cvs-scale c cvs2))
       (cvs-add-cvs cvs-cv cvcs2)]
    [else
     cvs]))

(define (cvs-find-max-abs-coeff cvs)
  ; Find the cv which maximizes (abs c).
  ; The constant term is not relevant.
  (define cvs* (cvs-remove-constant cvs))
  (if (null? cvs*)
      #f
      (argmax (λ (cv) (abs (car cv))) cvs*)))
