#lang racket
;; TODO:
;;  - fix formatting

; > (declare-vector z)
; > (declare a b)
; > (== z (vector a 20))
; > (== z (vector 30 b))
; > z
; '#(30 20)
; > a
; 30
; > b
; #0=(variable 5 'b (dependent-state (dependency #0# (list (cons 1 (variable 3 "z.1" (known-state 20))))) #f))


(require "variables.rkt"
         syntax/stx
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
;            |   (med numeric numeric numeric)   ; (med a b c) = b+a*(c-b)
;            |   (+ terms ...)
;            |   (- terms ...)
; term      :=   product
; product   :=   numeric
;            |   (* number ... numeric)          ; order of factors not important
;            |   (- product)
;            |   (+ product)
; numeric   :=   number
;            |   variable
;            |   expression                      ; that evaluates to a number or variable

;;; Representation
;;   - numeric   is a number or as a variable
;;   - product   is represented as a (cons number variable) or (cons number 1)
;;   - term      is represented as a product
;;   - terms     is represented as a list of product
;;   - sum       is represented as a list of product
;;   - equation  is represented as a list of list of product

;; Mediation. Notation in MetaFont/MetaPost t[x1,x2].
(define (med t x1 x2)
  (+ x1 (* t (- x2 x1))))


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
    [(_declare (~alt id:id
                     [n:number vector-id:id ...]) 
               ...)
     ; Turn n ... into ((n ...) ...) (i.e. ns to nss)
     ; so we can use [vector-id n] ... in the template.
     (define ns    (syntax->list #'(n ...)))
     (define vidss (syntax->datum #'((vector-id ...) ...)))
     (define nss   (for/list ([n    (in-list ns)]
                              [vids (in-list vidss)])
                     (map (λ (x) n) vids)))
     (with-syntax ([((n ...) ...) nss])
       (syntax/loc stx
         (declare [id 1] ... [vector-id n] ... ...)))]
     
    [(_declare [id:id n:number] ...)
     (define ids (stx->list #'(id ...)))
     (define ns  (stx->list #'(n ...)))

     (define (get-outer-variables)
       (local-expand(with-syntax ([show (syntax-local-get-shadower #'show)])
                      #'(show))
                    ctx '()))
     (define (do-define-numeric-id id)
       (define $id (format-id stx "$~a" id))
       (with-syntax ([$id $id] [id id])
         #'(begin
             (define $id (variable (serial) 'id (undefined-state)))
             (define-syntax id (λ (stx)
                                 #'(let ()
                                     (define v $id)
                                     (cond
                                       [(known? v) (value v)]
                                       [else              v])))))))
     (define (get-$id-from-def def)
       (syntax-parse def
         [(_begin (_define $id _) . _) #'$id]))
          
     (define (do-define-id id n)
       (define m (syntax-e n))
       (cond
         [(= m 1) (do-define-numeric-id id)]
         [else    (define name  (symbol->string (syntax-e id)))
                  (define sym   (string->symbol name))
                  (define names (for/list ([i m])
                                  (string->symbol (string-append name (number->string i)))))
                  (displayln names)
                  (define ids   (for/list ([name names]) (datum->syntax id name id)))
                  (define defs  (for/list ([id   ids])   (do-define-numeric-id id)))
                  (define $ids  (map get-$id-from-def defs))
                  (define $$id  (format-id stx "$$~a" id))
                  (with-syntax ([(def    ...) defs]
                                [($id ...)    $ids]
                                [(name.i ...) names]
                                [(id.i   ...) ids]                                
                                [sym          sym]
                                [tuple        $$id]
                                [id           id])
                    #'(begin
                        ; define the elements variables
                        def ...
                        ; our
                        (define tuple (variable (serial) 'sym (tuple-state (vector id.i ...))))
                        (set-variable-state! $id (independent-state '() #f tuple))
                        ...
                        (define-syntax id (λ (stx)
                                            #'(let ()
                                                (define v tuple)
                                                (if (known? v)
                                                    (value v)
                                                    v))))))]))
     
     (define (do-define-ids)
       (define defines (map do-define-id ids ns))
       (with-syntax ([(def ...) defines])
         #'(begin
             def ...)))
     
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


;; (declare-vector   z1 z2 ...) declares vectors of dimension 2
;; (declare-vector n z1 z2 ...) declares vectors of dimension n

(define-syntax (declare-vector stx)
  (syntax-parse stx
    [(_declare-vector id:id ...)
     #'(declare-vector 2 id ...)]     
    [(_declare-vector n:integer id:id ...)
     (define ids (syntax->list #'(id ...)))
     (with-syntax ([($id ...) (for/list ([id ids]) (format-id stx "$~a" id))])
       #'(begin
           (define $id (new-tuple n 'id)) ...
           (define-syntax id (λ (stx)
                               #'(let ()
                                   (define v $id)
                                   (if (known? v)
                                       (value v)
                                       v)))) ...))]))

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
    #:literals (+ - med)
    (pattern (+ tss:terms ...))
    (pattern (- tss:terms ...))
    (pattern (med a:numeric b:numeric c:numeric))
    (pattern t:term))

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

(define (make-vector-variable v)
  (unless (vector? v)
    (error 'make-vector-variable "expected a vector, got: ~a" v))
  (variable (serial) v (undefined-state)))

(define-syntax (numeric stx)
  (syntax-parse stx
    [(_numeric n:numeric)
     (syntax-parse #'n
       [x:number         #'x]
       [v:variable       #'v]
       [e:expr
        (syntax/loc #'e
          (with-top (let ([v e])
                      (when (vector? v)
                        (set! v (make-vector-variable v)))
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
          #'(let ([v v0])
              ; If v0 is known, it will evaluate to a number.
              ; If v0 is unknown, it evaluates to a variable.              
              (cond
                [(number? v) (cvs-make-constant (* v n))]
                [else        (cons n v0)])))]
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
       [n:number   #'(cvs-make-constant n)]
       [v:variable #'(cvs-make-constant-or-variable v)]
       [e:expr     #'(cvs-make-constant-or-variable (numeric e))])]))
     
(define-syntax (term stx)
  (syntax-parse stx
    [(_term p:product)  #'(product p)]))

(define (negate-coefficents cvs)
  (map (λ (cv) (cons (- (car cv)) (cdr cv))) cvs))
         
(define-syntax (terms stx)
  (syntax-parse stx    
    #:literals (+ - med)
    [(_terms (+ tss:terms ...))               #'(append (terms tss) ...)]
    [(_terms (- t:term))                      #'(negate-coefficents (terms t))]
    [(_terms (- ts:terms tss:terms ...))      #'(append (terms ts)
                                                        (negate-coefficents (append (terms tss) ...)))]
    [(_terms (med a b c))                     (syntax/loc stx
                                                ; b+a(c-b) = b+ac-ab
                                                (terms (+ b (* a c) (* -1 a b))))]    
    [(_terms t:term)                          #'(let ([cv (term t)])
                                                  (if (null? cv) '() (list cv)))]))

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
    [(_== s1:sum)                     #'(resolve (list (==1 s1 0))  (list #'_==))]
    [(_== s1:sum s2:sum)              #'(resolve (list (==1 s1 s2)) (list #'_==))]
    [(_== s1:sum s2:sum ss:sum ...)   #'(resolve (cons (==1 s1 s2)
                                                       (== s2 ss ...))
                                                 (list #'_==))]))

(define (generate-ith-equations cvs i)
  (define (tuple-ref v i)
    (vector-ref (tuple-state-tuple (variable-state v)) i))
  
  (define cvs-unordered
    (let loop ([cvs cvs])
      (cond
        [(null? cvs) '()]
        [else        (define cv (car cvs))
                     (define c  (car cv))
                     (define v  (cdr cv))
                     (cond
                       [(equal? v 1)       (cons cv (loop (cdr cvs)))]
                       [(vector? (name v)) (define vi (vector-ref (name v) i))
                                           (cond
                                             [(number? vi) (cons (cons (* c vi) 1)
                                                                 (loop (cdr cvs)))]
                                             [else         (cons (cons c vi)
                                                                 (loop (cdr cvs)))])]
                       [(tuple-var? v)     (define vi (tuple-ref v i))
                                           (cond
                                             [(number? vi) (cons (cons (* c vi) 1)
                                                                 (loop (cdr cvs)))]
                                             [(known? vi)  (cons (cons (* c (value vi)) 1)
                                                                 (loop (cdr cvs)))]
                                             [else         (cons (cons c vi)
                                                                 (loop (cdr cvs)))])]                        
                       [else               (cons cv (loop (cdr cvs)))])])))
  (canonical cvs-unordered))

(define new-tuple
  (let ([i 0])
    (λ (n id)
      (define id0    (if (symbol? id) (symbol->string id) id))
      (define name   (string-append id0 #;(number->string i)))
      (define name.s (for/list ([j n])
                       (string-append id0 #;(number->string i) "." (number->string j))))
      
      (set! i (+ i 1))
      (define tuple (variable (serial) name #f))
      (define vec   (for/vector ([j n] [name.j name.s])
                      (variable (serial) name.j (independent-state '() #f tuple))))
      (define s     (tuple-state vec))
      (set-variable-state! tuple s)
      tuple)))

(define (maybe-known-tuple! t)
  ; If all elements are known, the tuple is also known.
  (when t
    (define ts (variable-state t))
    (define es (tuple-state-tuple ts))
    (cond
      [(for/and ([e (in-vector es)]) (known? e))
       (define v (for/vector ([e (in-vector es)]) (value e)))
       (known! t v)]
      [else
       (void)])))


(define (rewrite-vector-variables cvs stxloc)
  ; A literal vector arrives here as an undefined variable whose name is a vector.
  ; A tuple variable contains a vector of variables.
  (define (vector-variable? v)
    (and (variable? v)
         (or (vector? (name v))
             (tuple-var? v))))  
  (define (->vector v)
    (define n (name v))
    (cond
      [(vector? n)    n]
      [(tuple-var? v) (tuple-state-tuple (variable-state v))]
      [else           (error '->vector "got: ~a" v)]))
  
  (define  vars (cvs-variables cvs))
  (define vvars (filter vector-variable? vars))
  (define vecs  (map ->vector vvars))
  (cond
    ; If there are no vector variables, we simply return our equation.
    [(null? vvars) (list (list cvs stxloc))]
    ; Otherwise, we must make an equation from each vector index.
    [else          (define dims (map vector-length vecs))
                   (define dim (car dims))
                   (unless (apply = dims)
                     (raise-syntax-error
                      '== "all vectors must have the same length" stxloc))                   
                   (for/list ([i dim])
                     (list (generate-ith-equations cvs i)
                           stxloc))]))

(define (resolve cvss stxlocs)
  ;; 0. Rewrite equations with "vector variables" into multiple equations.
  (define rewritten
    (append*
     (for/list ([cvs (in-list cvss)] [stxloc (stx->list stxlocs)])
       (rewrite-vector-variables cvs stxloc))))
  (set! cvss    (map first  rewritten))
  (set! stxlocs (map second rewritten))

  ;; 1. Make undefined variables in the equation independent.
  (for ([cvs (in-list cvss)])
    (for ([u (cvs-undefined-variables cvs)])
      (independent! u '() (list cvs)))) ; no deps, remember the introducing equation

  ;; 2. Remove all dependent variables from the equations.
  ;;    Invariant:  Dependent variables will only depend on independent variables.
  (define cvss* (map cvs-eliminate-all-dependent cvss))

  ;; 3. A constant equation with a non-zero constant represents k=0 (e.g. 1=0).
  ;;    Signal an error.
  (for ([cvs cvss*] [stxloc (stx->list stxlocs)])
    (when (cvs-non-zero-constant? cvs)
      (raise-syntax-error '==
                          "this relation led to inconsistent equations"
                          stxloc)))

  ;; 4. If the equations contain an independent variable,
  ;;    we can isolate it and make it dependent.
  (for ([cvs cvss*])
    (define icv (cvs-find-independent cvs))
    (cond
      [icv
       ; We found an independent variable, make it dependent.
       (define c (car icv))
       (define v (cdr icv))
       ; The dependencies in which the indendent v is used.
       (define deps (dependencies v))
       ; And the tuple it is an element of (if any).
       (define tup  (independent-state-tuple (variable-state v)))
       ; Isolate v in eq to get an equation for v.
       (define v= (cvs-isolate cvs v))
       (cond
         ; If v is constant, we can make it known.
         [(cvs-constant? v=)
          (known! v (cvs-constant v=))
          (maybe-known-tuple! tup)
          ; The dependencies where v occurs can now be reduced.
          (for ([d (in-list deps)])
            (define e  (dependency-cvs d))
            (define re (cvs-reduce-known e))
            (set-dependency-cvs! d re)
            ; If the reduced equation is a constant,
            ; then the dependent variable is (now also) known.
            (when (cvs-constant? re)
              (define k  (cvs-constant re))
              (define dv (the-variable d))
              (define t  (dependent-state-tuple (variable-state dv)))
              (known! dv k)
              (maybe-known-tuple! t)))]
         ; If v is not a constant, then v must change from independent to dependent.
         [else
          ; The newly discovered dependency for v.
          (define new-dep (dependency v v=))
          ; Now v is dependent.
          (dependent! v new-dep tup)
          ; The new dependency might contain other independent variables.
          (for ([iv (cvs-independent-variables v=)])
            (independent-add-dependency! iv new-dep))
          ; Update dependencies featuring v.
          (for ([d (in-list deps)])
            (define e  (dependency-cvs d))
            (define re (cvs-eliminate-dependent e v))
            (set-dependency-cvs! d re)
            ; The elimination might introduce new independent variables in d.
            ; If so d must be added to the dependencies of the newly introduced variables.
            (for ([iv (cvs-independent-variables re)])
              (unless (memq d (dependencies iv))
                (independent-add-dependency! iv d))))])]
      ; No new independent variables.
      [else (void)]))
  (void 'done))



(define (cv<= cv1 cv2)
  (variable<= (cdr cv1) (cdr cv2)))

(define (variable<= v1 v2)
  (cond
    [(eqv? v1 1)                   #t]
    [(eqv? v2 1)                   #f]
    [else                          (<= (serial v1) (serial v2))]))

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

(define (remove-head-one xs)
  (cond
    [(null? xs)                 xs]
    [(equal? (cdar xs) 1) (cdr xs)]
    [else                      xs]))

(define (cvs-undefined-variables cvs)
  (filter undefined? (cvs-variables (remove-head-one cvs))))
(define (cvs-independent-variables cvs)
  (filter independent? (cvs-variables (remove-head-one cvs))))
(define (cvs-dependent-variables cvs)
  (filter dependent? (cvs-variables (remove-head-one cvs))))

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

(define (cvs-make-constant k)
  (if (= k 0) '() (cons k 1)))

(define (cvs-make-constant-or-variable v)
  (if (number? v)
      (cvs-make-constant v)
      (cons 1 v)))

(define (cvs-zero? cvs)
  (null? cvs))

(define (cvs-constant? cvs)
  (or (null? cvs)
      (and (null? (cdr cvs))
           (eqv? (cdar cvs) 1))))

(define (cvs-non-zero-constant? cvs)
  (and (not (null? cvs))
       (eqv?  (cdar cvs) 1)
       (null? (cdr cvs))))

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

(define (cvs-eliminate-dependent u dv)
  (cvs-substitute u dv (dependency-cvs (the-dependency dv))))

(define (cvs-eliminate-all-dependent u)
  (define dvs (cvs-dependent-variables u))
  (foldl (λ (dv u) (cvs-eliminate-dependent u dv))
         u dvs))

; cvs-find-independent : cvs -> (cons coef independent-variable)
;           or         : cvs -> #f
;   Find the independent variable with the greatest absolute value.
(define (cvs-find-independent cvs)
  (define (independent-term? cv)
    (define v (cdr cv))
    (and (not (eqv? v 1)) (independent? v)))
  (define icvs (filter independent-term? cvs))
  (if (null? icvs) #f (argmax car icvs)))

(define (known-variable? x)
  (and (variable? x)
       (known? x)))

(define (cvs-reduce-known cvs)
  (define k 0)
  (define cvs* (let loop ([cvs cvs])
                 (cond
                   [(null? cvs) '()]
                   [else        (define cv (car cvs))
                                (cond
                                  [(known-variable? (cdr cv))
                                   (define kv (value (cdr cv)))
                                   (set! k (+ (* (car cv) kv) k))
                                   (loop (cdr cvs))]
                                  [else
                                   (cons cv (loop (cdr cvs)))])])))
  ; Add the accumulated constants as the first cv,
  ; unless the constant is zero.
  (cond
    [(null? cvs*)         (list (cons k 1))]
    [(eqv? (cdar cvs*) 1) (define cv (car cvs*))
                          (define k* (+ (car cv) k))
                          (if (= k* 0)
                              (cdr cvs*)
                              (cons (cons k* 1) (cdr cvs*)))]
    [else                 (if (= k 0)
                              cvs*
                              (cons (cons k 1) cvs*))]))

;(define (reduce-known! eq)
;  (define-values (cs vs k) (reduce-known eq))
;  (set-combination-coefs!    eq cs)
;  (set-combination-vars!     eq vs)
;  (set-combination-constant! eq k))

#;(define (eliminate-dependent! eq dv)
    (define req (eliminate-dependent eq dv))
    (set-combination-coefs!    eq (combination-coefs    req))
    (set-combination-vars!     eq (combination-vars     req))
    (set-combination-constant! eq (combination-constant req)))

#;(define (remove-all-dependent-variables! eq)
    (define dv (find-dependent-variable eq))
    (when dv
      (eliminate-dependent! eq dv)
      (remove-all-dependent-variables! eq)))
