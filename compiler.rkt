#lang racket

(require graph)
(require data/queue)
(require racket/fixnum)
(require racket/promise)
(require racket/set racket/stream)

(require "interp-Lif.rkt")
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Lvec.rkt")
(require "interp-Lvec-prime.rkt")
(require "interp-Lfun.rkt")
(require "interp-Lfun-prime.rkt")

(require "interp-Cif.rkt")
(require "interp-Cvar.rkt")
(require "interp-Cwhile.rkt")
(require "interp-Cvec.rkt")
(require "interp-Cfun.rkt")

(require "interp.rkt")

(require "type-check-Lif.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Lvec.rkt")
(require "type-check-Lfun.rkt")

(require "type-check-Cif.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Cwhile.rkt")
(require "type-check-Cvec.rkt")
(require "type-check-Cfun.rkt")

(require "utilities.rkt")
(require "multigraph.rkt")
(require "priority_queue.rkt")
(require "graph-printing.rkt")

(provide (all-defined-out))

;; Predicate Checks on the operator.

(define (is-reg? arg)
    ;; register check
  (match arg
    [(Reg _) #t]
    [else #f]))

(define arthms (list '+ '-))
(define cmps   (list '< '> '= '<= '>= 'eq?))
(define logop  (list 'and 'or))
(define vecops (list 'vector-ref 'vector-set! 'vector-length))

(define (op-check op of-type) 
  (ormap 
    (lambda (cmp) (eq? cmp op)) 
    of-type))

;; pe-Lfun : Lfun -> Lfun
;;------------------------------------------------------------
;; A partial evaluator. Find operations with static arguments 
;; and solves them, replacing arithmetic operations with the
;; output integer and so on.

(define (pe-neg r) 
  ;; (- (Int n1)) -> (Int -n1)
  (match r 
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-adux r1 r2)
  ;; Helper function to collect integers across nested additions.
  (match* (r1 r2)
    [((Int r) (Prim '+ (list (Int x) arg))) 
      (let ([r (fx+ x r)]) (list (Int r) (pe-exp arg)))]
    [(_ _) (list r1  (pe-exp r2))]))

(define (pe-add r1 r2)
    ;; (+ (Int n1) (Int n2)) -> (Int (n1 + n2))
  (match* (r1 r2) 
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [((Int n1) arg) (Prim '+ (pe-adux (Int n1) arg))] 
    [(arg (Int n2)) (Prim '+ (pe-adux (Int n2) arg))]
    [(_ _) (Prim '+ (list r1 r2))])) 

(define (pe-sub r1 r2) 
    ;; (- (Int n1) (Int n2)) -> (Int (n1 - n2))
  (match* (r1 r2) 
    [((Int n1) (Int n2)) (Int (fx- n1 n2))] 
    [(_ _) (Prim '- (list r1 r2))])) 

(define (pe-cmp op r1 r2)
    ;; (cmp (Bool b1) (Bool b2)) -> (Bool (cmp b1 b2))
  (match* (r1 r2)
    [((Int n1) (Int n2)) 
      (case op 
        [(<)  (Bool (< n1 n2))]
        [(>)  (Bool (> n1 n2))]
        [(>=) (Bool (= n1 n2))]
        [(<=) (Bool (<= n1 n2))]
        [(eq?)  (Bool (eq? n1 n2))])]
    [(_ _) (Prim op (list r1 r2))]))

(define (pe-and r1 r2)
    ;;(and (Bool b1) (Bool b2)) -> (Bool (and b1 b2))
  (match* (r1 r2) 
    [((Bool n1) (Bool n2)) (Bool (and n1 n2))]
    [(_ _) (Prim 'and (list r1 r2))])) 

(define (pe-or r1 r2)
    ;;(or (Bool b1) (Bool b2)) -> (Bool (or b1 b2))
  (match* (r1 r2) 
    [((Bool n1) (Bool n2)) (Bool (or n1 n2))]
    [(_ _) (Prim 'or (list r1 r2))])) 

(define (pe-logop op r1 r2)
    ;; calls either pe-and or pe-or.
  (case op 
    [(and)  (pe-and  r1 r2)]
    [(or )  (pe-or   r1 r2)]))

(define (pe-not r1)
    ; (not (Bool b1)) -> (Bool (not b1))
  (match r1
    [(Bool n1) (Bool (not n1))]
    [_ (Prim 'not (list r1))]))

(define (pe-If cnd thn els)
    ;; if cnd is straight up just a boolean 
    ;; then pick a branch here itself. 
  (match cnd
    [(Bool bool) (if bool thn els)]
    [_ (If cnd thn els)]))

(define (pe-exp e) 
    ;; Calls any of the above functions to collect static args
    ;; based on the operation being performed.
  (match e 
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]  ;negation
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))] ;addition 
    [(Prim '- (list e1 e2)) (pe-sub (pe-exp e1) (pe-exp e2))] ;subtraction
    [(Prim op (list e1 e2)) #:when (op-check op  cmps) ( pe-cmp  op (pe-exp e1) (pe-exp e2))] ;comparisons
    [(Prim op (list e1 e2)) #:when (op-check op logop) (pe-logop op (pe-exp e1) (pe-exp e2))] ;and/or
    [(Prim 'not (list e1)) (pe-not (pe-exp e1))]  ;not
    [(If exp1 exp2 exp3) (pe-If (pe-exp exp1) (pe-exp exp2) (pe-exp exp3))] ; if statements
      ; the above are expressions where we might find static arguments to evaluate. 
      ; everything below just needs recursing on the arguments.
    [(Let x rhs body) (Let x (pe-exp rhs) (pe-exp body))] 
    [(Begin exps expr) (Begin (map pe-exp exps) (pe-exp expr))]
    [(SetBang var expr) (SetBang var (pe-exp expr))]
    [(WhileLoop con expr) (WhileLoop (pe-exp con) (pe-exp expr))]
    [_ e]))

(define (pe-Lfun p) 
  (match p 
    [(ProgramDefsExp info Defs expr) 
     (ProgramDefsExp info
      (map 
        (lambda (ex)
          (match ex
            [(Def var types ret-type info tail) (Def var types ret-type info (pe-exp tail))]))
      Defs) 
      (pe-exp expr))]))

;;        shrink : Lfun -> Lfun
;;----------------------------------------
;; Replace and/or with if stmts. Enables
;; shortcircuiting, reduces types of stmts. 
 
(define (shrink-exp exps)
  (match exps

    [(Prim 'and (list exp1 exp2)) (If (shrink-exp exp1) (shrink-exp exp2) (Bool #f))]
    [(Prim 'or  (list exp1 exp2)) (If (shrink-exp exp1) (Bool #t) (shrink-exp exp2))]

    [(Prim op args) (Prim op (map (lambda (arg) (shrink-exp arg)) args))]
    [(If exp1 exp2 exp3) (If (shrink-exp exp1) (shrink-exp exp2) (shrink-exp exp3))]
    [(Let var rhs body) (Let var (shrink-exp rhs) (shrink-exp body))]
    [(Begin exps expr) (Begin (map shrink-exp exps) (shrink-exp expr))]
    [(SetBang var expr) (SetBang var (shrink-exp expr))]
    [(WhileLoop con expr) (WhileLoop (shrink-exp con) (shrink-exp expr))]
    [(Apply func params) (Apply (shrink-exp func) (map shrink-exp params))]
    [_ exps]))

(define (shrink p)
  (match p 
    [(ProgramDefsExp info Defs expr) 
     (ProgramDefs info
      (append 
        (map 
          (lambda (ex)
            (match ex
              [(Def var types ret-type info tail) (Def var types ret-type info (shrink-exp tail))]))
        Defs) 
        (list (Def 'main '() 'Integer '() (shrink-exp expr)))))]))


;;   uniquify : Lvec -> Lvec
;;-----------------------------
;; Replaces same variable names 
;; with unique ones.

(define (uniquify-exp env)
    ;; Replaces variable name with unique one from env, or sets a 
    ;; unique name and adds to let in case of a let stmt.
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Let x ex body)
       (let ([new-env (dict-set env x (gensym x))])
         (Let
          (dict-ref new-env x)
          ((uniquify-exp env) ex)
          ((uniquify-exp new-env) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [(If exp1 exp2 exp3) (If ((uniquify-exp env) exp1) ((uniquify-exp env) exp2) ((uniquify-exp env) exp3))]
      [(Begin exps expr) (Begin (map (uniquify-exp env) exps) ((uniquify-exp env) expr))]
      [(SetBang var expr) (SetBang (dict-ref env var) ((uniquify-exp env) expr))]
      [(WhileLoop con expr) (WhileLoop ((uniquify-exp env) con) ((uniquify-exp env) expr))]
      [(Apply func params) (Apply ((uniquify-exp env) func) (map (uniquify-exp env) params))]
      [_ e])))

(define (make-func-env params)
  (let ([new-env '()])
    (let ([new-params
            (map 
              (lambda (param)
                (match param
                  [(list xs ': ps) 
                  (let ([throw 
                        (set! new-env (cons (cons xs (gensym xs)) new-env))])
                      (list (dict-ref new-env xs) ': ps))])) 
              params)])
      (values new-env new-params))))

(define (uniquify-func env) 
  (lambda (params func)
    (let-values ([(nenv nparams) (make-func-env params)])
         (values ((uniquify-exp (append env nenv)) func) nparams))))

(define (uniquify p)
  (match p
    [(ProgramDefs info Defs)
     (let ([env 
            (map
            (lambda (func)
              (match func 
                [(Def label param-types ret-type info expr) 
                 (if (eq? label 'main) (cons label label) (cons label (gensym label)))])) 
            Defs)])
      (ProgramDefs
      info
      (map 
        (lambda (func)
          (match func 
            [(Def label param-types ret-type info expr)
             (let-values ([(new-expr new-params) ((uniquify-func env) param-types expr)])
             (Def (dict-ref env label) new-params ret-type info new-expr))]))
        Defs)))]))


;;          reveal_functions : Lfun -> Lfunref
;;------------------------------------------------------
;; Calls to a function in the AST treat the label as a Var.
;; This changes that so they are treated as FunRef.

(define funcs (make-hash))

(define (find-fun expr)
  (match expr 
    [(Var x) (if (dict-has-key? funcs x) (FunRef x (dict-ref funcs x)) expr)]
    [(Prim op args) (Prim op (map (lambda (arg) (find-fun arg)) args))]
    [(If exp1 exp2 exp3) (If (find-fun exp1) (find-fun exp2) (find-fun exp3))]
    [(Let var rhs body) (Let var (find-fun rhs) (find-fun body))]
    [(Begin exps expr) (Begin (map find-fun exps) (find-fun expr))]
    [(SetBang var expr) (SetBang var (find-fun expr))]
    [(WhileLoop con expr) (WhileLoop (find-fun con) (find-fun expr))]
    [(Apply func params) (Apply (find-fun func) (map find-fun params))]
    [(HasType expr type) (HasType (find-fun expr) type)]
    [_ expr]))

(define (reveal_functions p)
  (set! funcs (make-hash))
  (match p
    [(ProgramDefs info Defs)
     (let ([throw 
            (map
            (lambda (func)
              (match func 
                [(Def label param-types ret-type info expr)
                 (dict-set! funcs label (length param-types))])) 
            Defs)])
      (ProgramDefs
      info
      (map 
        (lambda (func)
          (match func 
            [(Def label param-types ret-type info expr)
             (Def label param-types ret-type info (find-fun expr))]))
        Defs)))]))


;;                  limit_functions : Lfunref -> Lfunref
;;--------------------------------------------------------------------
;; If a function has more than 6 parameters, it collects any arguments
;; past the first 5 into a vector.

(define (change_params param-types vec-name) 
  (match param-types 
    [(list param1 param2 param3 param4 param5 vectorize ...) 
     (list param1 param2 param3 param4 param5 (list vec-name ': 
                                                (cons 'Vector
                                                  (map 
                                                    (lambda (pair) 
                                                      (match pair 
                                                        [(list xs ': ps) ps])) 
                                                  vectorize))))]))

(define (limit_args prms)
  (if (< 6 (length prms))
        ;; then
      (match prms
        [(list param1 param2 param3 param4 param5 vectorize ...) 
         (list param1 param2 param3 param4 param5 (Prim 'vector vectorize))]) 
        ;; else
      prms))

(define (make-param-lst param-types)
  (let ([param-lst '()]) 
    (foldr
      (lambda (pair constr) (match pair
                              [(list xs ': ps)
                               (cons xs constr)]))
    param-lst param-types)))

(define (replace-param xs param-lst params)
  (if (> 5 (index-of param-lst xs)) 
      ;; then
      (Var xs)
      ;; else 
      (Prim 'vector-ref 
            (list (Var params) 
                  (Int (- (index-of param-lst xs) 5))))))

(define (get-param arg param-types params) 
  (define param-lst (make-param-lst param-types))
  
  ; (displayln param-lst)

  (if (< 6 (length param-lst)) 
        ;; then
      (match arg 
        [(Var xs) (replace-param xs param-lst params)])
        ;; else
      arg
  ))

(define (limit_func_body body param-types params)
  (match body 
    [(Var x) (get-param body param-types params)]
    [(FunRef x n) (FunRef x n)]
    [(Prim op args) (Prim op (map (lambda (arg) (limit_func_body arg param-types params)) args))]
    [(If exp1 exp2 exp3) (If (limit_func_body exp1 param-types params) (limit_func_body exp2 param-types params) (limit_func_body exp3 param-types params))]
    [(Let var rhs body) (Let var (limit_func_body rhs param-types params) (limit_func_body body param-types params))]
    [(Begin exps expr) (Begin (map (lambda (arg) (limit_func_body arg param-types params)) exps) (limit_func_body expr param-types params))]
    [(SetBang var expr) (SetBang var (limit_func_body expr param-types params))]
    [(WhileLoop con expr) (WhileLoop (limit_func_body con param-types params) (limit_func_body expr param-types params))]
    [(Apply func prms) (Apply (limit_func_body func param-types params) (map (lambda (arg) (limit_func_body arg param-types params)) (limit_args prms)))]
    [(HasType expr type) (HasType (limit_func_body expr param-types params) type)]
    [_ body]))

(define (limit_func_def func)
  (match func
    [(Def label param-types ret-type info expr) 
     (if (member label funcs) 
            ;; then
         (let ([params (gensym 'pv)])
          (Def label (change_params param-types params) ret-type info (limit_func_body expr param-types params)))
            ;; else
         (Def label param-types ret-type info (limit_func_body expr param-types '())))]))

(define (limit_functions p)
  (set! funcs
    (filter 
      (lambda (key) (< 6 (hash-ref funcs key))) 
    (hash-keys funcs)))

  (match p
    [(ProgramDefs info Defs)
      (ProgramDefs
      info
      (map limit_func_def Defs))
    ]))

;;                  expose-allocation : Lvec -> Lalloc
;;----------------------------------------------------------------
;;      Handles tuple creation by interfacing with the collector.

(define (is-init-vec? expr)
    ;; Checks to see if the expression initialises a vector

  (match expr
    [(Prim 'vector args) #t]
    [else #f]))

(define (nest-set ind dispose arg-labels vec)
  (match arg-labels
    ['() (Var vec)]
    [(list arg-label arg-lbls ...) 
     (Let dispose (Prim 'vector-set! (list (Var vec) (Int ind) (Var (car arg-label)))) 
                  (nest-set (+ ind 1) dispose arg-lbls vec))]))

(define (nest-collect-and-alloc len dispose vec type cont)
  (let ([byts (+ 8 (* 8 len))])
       (Let dispose 
        (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int byts)))
                           (GlobalValue 'fromspace_end))) 
            (Void) (Collect byts)) 
        (Let vec (Allocate len type) cont))))

(define (nest-assign arg-labels cont) 
  (match arg-labels 
    ['() cont]
    [(list arg-label arg-lbls ...) 
     (Let (car arg-label) (cdr arg-label) (nest-assign arg-lbls cont))]))

(define (do-allocation vec-args len type)
  ;; Handles vector allocation. The entire vector instantiation becomes a 
  ;; series of nested lets. The let assignments are of three types, and 
  ;; three helper functions for each are in use:

  (let* ([vec (gensym 'vec)]
         [dispose (gensym 'hold)]
         [arg-labels 
          (foldr (lambda (arg labels) 
                    (cons (cons (gensym 'arg) arg) labels)) 
          '() vec-args)]) 
          ;; 1. nest-assign, to handle assigning vector elems to tmp vars 
        (nest-assign arg-labels 
                ;; 2. this, to interface with the garbage collector if needed
              (nest-collect-and-alloc len dispose vec type 
                      ;; 3. this, to set! the elements in the vector
                    (nest-set 0 dispose arg-labels
                          vec)))))

(define (expose-exp expr)
  ;; Finds expressions where a vector is being initialised. 

  (match expr 
    [(Prim op args) (Prim op (map expose-exp args))]
    [(Let var rhs body) (Let var (expose-exp rhs) (expose-exp body))]
    [(If cnd thn els) (If (expose-exp cnd) (expose-exp thn) (expose-exp els))]
    [(Begin exps expr) (Begin (map expose-exp exps) (expose-exp expr))]
    [(SetBang var expr) (SetBang var (expose-exp expr))]
    [(WhileLoop cnd body) (WhileLoop (expose-exp cnd) (expose-exp body))]
    [(HasType expr type) #:when (not (is-init-vec? expr)) (HasType (expose-exp expr) type)]
    [(Apply func args) (Apply (expose-exp func) (map expose-exp args))]
    
    [(HasType (Prim 'vector vec-args) type)
     (let ([vec-args_ (map expose-exp vec-args)]) 
          (do-allocation vec-args_ (length vec-args_) type))]

    [_ expr]))

(define (expose-allocation p)
  (match p
    [(ProgramDefs info Defs)
     (ProgramDefs
      info
      (map 
        (lambda (func)
          (match func 
            [(Def label param-types ret-type info expr)
             (Def label param-types ret-type info (expose-exp expr))]))
        Defs))
    ]))


;;                  uncover-get! : Lalloc -> Lalloc
;;----------------------------------------------------------------
;; Marks mutable variables by changing from (Var x) to (GetBang x).
;; They will now be treated as complex exprs in the rco pass.

(define (uncover-get-var is-mutable e)
  ;; changes mutable vars to GetBang.

  (match e
    [(Void) e]
    [(Int  _) e]
    [(Bool _) e]
    [(Collect int)      e] 
    [(GlobalValue ptr)  e]
    [(Allocate var int) e]
    [(Var x) (if (set-member? is-mutable x)
                 (GetBang x) (Var x))]
    [(FunRef x n) (if (set-member? is-mutable x)
                      (GetBang x) (FunRef x n))]
    [(Prim op args) 
      (Prim op 
        (map  (lambda (arg) 
                (uncover-get-var is-mutable arg)) 
        args))]
    [(Let x rhs body) (Let x  (uncover-get-var is-mutable rhs)  
                              (uncover-get-var is-mutable body))]
    [(If e1 e2 e3) (If  (uncover-get-var is-mutable e1)
                        (uncover-get-var is-mutable e2)
                        (uncover-get-var is-mutable e3))]
    [(SetBang var rhs) (SetBang var (uncover-get-var is-mutable rhs))]
    [(Begin exps expr) (Begin (map (lambda (ex) (uncover-get-var is-mutable ex)) exps) 
                              (uncover-get-var is-mutable expr))]
    [(WhileLoop con expr) (WhileLoop  (uncover-get-var is-mutable con)
                                      (uncover-get-var is-mutable expr))]
    [(Apply func args) (Apply (uncover-get-var is-mutable func) (map (lambda (arg) (uncover-get-var is-mutable arg)) args))]))

(define (recur-get-set collection sets)
  (foldr 
    (lambda (collect Set) (set-union collect Set))
  sets (map get-set-go! collection)))

(define (get-set-go! e) 

  ;; Constructs a set of mutable variables in the program.
  ;; Recurse on args of every instruction, and in the case
  ;; of a SetBang mark the variable mutable before doing so.

  (match e 
    [(Void )  (set)]
    [(Var x ) (set)] 
    [(Int n ) (set)] 
    [(Bool x) (set)]
    [(FunRef x n) (set)]
    [(Collect int)      (set)] 
    [(GlobalValue ptr)  (set)]
    [(Allocate var int) (set)]
    [(If e1 e2 e3)        (recur-get-set (list e1 e2 e3) (set))]
    [(Prim op args)       (recur-get-set args (set))]
    [(Let x rhs body)     (recur-get-set (list rhs body) (set))]
    [(SetBang var rhs)    (recur-get-set (list rhs) (set var))]
    [(Begin exps expr)    (recur-get-set exps (get-set-go! expr))]
    [(WhileLoop con expr) (recur-get-set (list con expr) (set))]
    [(Apply func args)    (recur-get-set (cons func args) (set))])) 

(define (uncover-get! p) 
  (match p
    [(ProgramDefs info Defs)
     (ProgramDefs
      info
      (map 
        (lambda (func)
          (match func 
            [(Def label param-types ret-type info expr)
             (Def label param-types ret-type info 
             (uncover-get-var (get-set-go! expr) expr))]))
        Defs))
    ]))
    

;;        remove complex ops : Lalloc -> Lalloc^mon
;;-----------------------------------------------------------
;; Transform complex args into let stmts w atomic args in the 
;; body. eg: (+ (+ 2 3) 4) := (let ([x (+ 2 3)]) (+ x 4))


(define (rco-tmp expr)
    ;; maps complex exprs to a variable. returns the var & the mapping.
  
  (let ([tmp (gensym 'tmp)]) 
       (values (Var tmp) (list (cons tmp (rco-exp expr))))))

(define (rco-atom expr)
  ;; Called from rco-exp when dealing with an instruction that must have 
  ;; atomic arguments. Unless expr is atomic calls rco-tmp to handle it. 

  (match expr
    [(Var  _) (values expr '())]
    [(Int  _) (values expr '())]
    [(Bool _) (values expr '())]
    [( Void ) (values expr '())]
    [(GetBang var)      (rco-tmp expr)]
    [(If e1  e2  e3)    (rco-tmp expr)]
    [(Let x ex body)    (rco-tmp expr)]
    [(Prim  op body)    (rco-tmp expr)]
    [(Begin exps ex)    (rco-tmp expr)]
    [( SetBang var ex ) (rco-tmp expr)]
    [(WhileLoop con ex) (rco-tmp expr)]
    [(Collect int)      (rco-tmp expr)]
    [(Allocate var int) (rco-tmp expr)]
    [(GlobalValue ptr)  (rco-tmp expr)]
    [(FunRef x n)       (rco-tmp expr)]
    [(Apply fun args)   (rco-tmp expr)]))

(define (rco-exp expr)
  ;;Handles instructions where it is valid for arguments to be non-atomic.

  (match expr
    [(Var  x) expr]
    [(Int  x) expr]
    [(Bool x) expr]
    [(FunRef x n) expr]
    [(Collect int)      expr]
    [(GlobalValue ptr)  expr]
    [(Allocate var int) expr]
    [(If e1  e2  e3) (If (rco-exp e1) (rco-exp e2) (rco-exp e3))]
    [(Let x ex body) (Let x (rco-exp ex) (rco-exp body))]
    [(SetBang var expr) (SetBang var (rco-exp expr))]
    [(GetBang var) (Var var)]
    [(Begin exps expr) (Begin (map rco-exp exps) (rco-exp expr))]
    [(WhileLoop con expr) (WhileLoop (rco-exp con) (rco-exp expr))]
    [(Prim  op body) 
        (let-values ([(atm mp) (values '() '())]) 
                      (for ((e body))
                        (let-values ([(natm nmp) (rco-atom e)])
                          (set! atm (cons natm atm))
                          (set! mp (append nmp mp))))
                      (foldl (lambda (mapp body)
                        (Let (car mapp) (cdr mapp) body)) 
                        (Prim op (reverse atm)) mp))]
    [(Apply fun args) 
     (let-values ([(atm mp) (values '() '())]) 
            (for ((e args))
              (let-values ([(natm nmp) (rco-atom e)])
                (set! atm (cons natm atm))
                (set! mp (append nmp mp))))
            (let-values ([(natm nmp) (rco-atom fun)])
              (foldl (lambda (mapp body)
              (Let (car mapp) (cdr mapp) body)) 
              (Apply natm (reverse atm)) (append mp nmp))))]
    [_ expr]))

(define (remove-complex-opera* p)
  (match p
  [(ProgramDefs info Defs)
    (ProgramDefs
    info
    (map 
      (lambda (func)
        (match func 
          [(Def label param-types ret-type info expr)
            (Def label param-types ret-type info (rco-exp expr))]))
      Defs))
  ]))

;;                        explicate-control : Lalloc^mon -> Ctup
;;-------------------------------------------------------------------------------------
;; Makes the flow of the program execution explicit by transforming to a C-like syntax.
;; Also constructs basic blocks out of if conditions and while loops to remove redundancy.

(define basic-blocks (make-hash))

(define does-tail-jmp? #f)

(define (create-block tail)
    ;; creates a block. Returns a goto stmt.
  ; (displayln tail)
  (match tail 
    [(Goto label) (Goto label)] 
    [else (let ([label 
                  (gensym 'block)]) 
               (dict-set! basic-blocks label tail) 
               (Goto label))])) 

(define (explicate-effect expr cont) 
  ;; deals w exprs in an effect situation; `expr` param exists only for its side
  ;; effect on the result produced by `cont`.

  (match expr
    
    ; expressions w no side effects can be discarded.
    
    [(Var _) cont]
    [(Int _) cont]
    [(Bool _) cont]
    [( Void ) cont]
    [(FunRef x n) cont]
    [(Prim op es) #:when (op-check op (append arthms cmps)) cont]

    ; on the other hand expressions with an effect 
    ; must be placed in a sequence.

    [(Prim 'read args) (Seq expr cont)]
    [(Prim 'vector-set! args) (Seq expr cont)]
    [(Let x rhs body) (explicate-assign rhs x (explicate-effect body cont))]
    [(If con e1 e2) (let ([goto (create-block cont)])
                         (let ([exp_1 (explicate-effect e1 goto)] [exp_2 (explicate-effect e2 goto)])
                              (explicate-pred con exp_1 exp_2)))]
    [(Collect int)      (Seq expr cont)]
    [(GlobalValue ptr)  (Seq expr cont)]
    [(Allocate var int) (Seq expr cont)]
    [(Apply fun args) (Seq (Call fun args) cont)]

    ; with a begin in an effect position, all non-terminal exps affect the last one,
    ; which in turn affects the cont.

    [(Begin exps e) 
      (let ([new-cont (explicate-effect e cont)]) 
        (foldr explicate-effect new-cont exps))]

    [(SetBang var ex) (explicate-assign ex var cont)]

    ;; while -> if cond then (body + goto cond) else cont

    [(WhileLoop con body) 
        ;; Make a label for the loop-body...
      (let ([tmp (gensym 'loop)])
            ;; ...Create a block out of the explicate-effect output on the body 
            ;; (with a goto in the cont position)...
          (let ([body_ (create-block (explicate-effect body (Goto tmp)))]) 
              ;; ...Now call explicate-pred on the con, with body_ and cont_. 
            (let ([loop-body (explicate-pred con body_ (create-block cont))])
                ;; Store the loop with its label in basic-blocks.
              (begin (dict-set! basic-blocks tmp loop-body) (Goto tmp)))))]))

(define (explicate-pred cnd thn els) 
  ;; Deals with expressions in the predicate position.

  (match cnd 
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (create-block thn) (create-block els))]
    [(Bool bool) (if bool thn els)]
    [(Let x rhs body) (explicate-assign rhs x (explicate-pred body thn els))]
    [(Prim 'not (list e)) (IfStmt (Prim 'eq? (cons e (list (Bool #f)))) (create-block thn) (create-block els))]
    [(Prim op es) #:when (op-check op cmps) 
                  (IfStmt (Prim op es)
                  (create-block thn) (create-block els))] 
    [(If cnd^ thn^ els^) 
     (let ([thn_ (create-block thn)] [els_ (create-block els)]) 
          (explicate-pred cnd^ (explicate-pred thn^ thn_ els_) (explicate-pred els^ thn_ els_)))] 
    [(Begin exps expr) 
      (let ([cont (explicate-pred expr thn els)]) 
        explicate-effect exps cont)]
    [(Apply fun args) 
      (let ([con (gensym 'con)]) 
           (explicate-assign cnd con (explicate-pred con thn els)))]
    [else (error "explicate-pred unhandled case" cnd)]))

(define (explicate-assign e x cont)
  ;; Handles assigning of expressions to a variable.

  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Bool bool) (Seq (Assign (Var x) (Bool bool)) cont)]
    [(FunRef y n) (Seq (Assign (Var x) (FunRef y n)) cont)]
    [(Void) (Seq (Assign (Var x) (Void)) cont)]
    [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
    [(If con exp1 exp2) (let ([goto (create-block cont)])
                             (let ([exp_1 (explicate-assign exp1 x goto)] [exp_2 (explicate-assign exp2 x goto)])
                                  (explicate-pred con exp_1 exp_2)))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(SetBang var ex) (explicate-assign ex var (explicate-assign (Var x) (Void) cont))]
    [(WhileLoop con body) (explicate-effect e (explicate-assign (Void) x (create-block cont)))]
    [(Begin exps expr) 
      (let ([cnt1 (explicate-assign expr x cont)])
           (foldr explicate-effect cnt1 exps))]
    [(Collect int)      (Seq e (explicate-assign (Void) x cont))]
    [(GlobalValue ptr)  (Seq (Assign (Var x) e) cont)]
    [(Allocate int vec) (Seq (Assign (Var x) e) cont)]
    [(Apply fun args) (Seq (Assign (Var x) (Call fun args)) cont)]
    [else (error "explicate-assign unhandled case" e)]))

(define (explicate-tail e)
  ;; Deals with expressions in a tail position.

  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Bool bool) (Return (Bool bool))]
    [(FunRef x n) (Return (FunRef x n))]
    [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
    [(If con exp1 exp2) (explicate-pred con (explicate-tail exp1) (explicate-tail exp2))]
    [(Prim op es) (let ([tmp (gensym 'tmp)]) (explicate-assign e tmp (explicate-tail (Var tmp))))]
    [(SetBang var ex) (explicate-assign ex var (Return (Void)))]
    [(Begin exps expr) 
      (let ([cont (explicate-tail expr)])
        (foldr explicate-effect cont exps))]
    [(Collect int)      (Seq e (Return (Void)))]
    [(GlobalValue ptr)  (Seq e (Return (Void)))]
    [(Allocate var int) (Seq e (Return (Void)))]
    [(Apply fun args) (begin (set! does-tail-jmp? #t) (TailCall fun args))]
    [else (error "explicate-tail unhandled case" e)]))

(define (fetch-blocks label label-block)
   (let ([blocks (list `(,label . ,(explicate-tail label-block)))]) 
        (append blocks (hash->list basic-blocks))))

(define (explicate-control-func label expr)
  (set! basic-blocks (make-hash))
  (fetch-blocks label expr))

(define (make-start label)
  (string->symbol (string-append (symbol->string label) (symbol->string '_start))))

(define (make-conclusion label)
  (string->symbol (string-append (symbol->string label) (symbol->string '_conclusion))))

(define (explicate-control p)
  (match p
  [(ProgramDefs info Defs)
    (ProgramDefs
    info
    (map 
      (lambda (func)
        (set! does-tail-jmp? #f)
        (match func 
          [(Def label param-types ret-type info expr)
            (let ([new-expr (explicate-control-func (make-start label) expr)])
            (Def label param-types ret-type (cons (cons'tailjmp? does-tail-jmp?) info) new-expr))]))
      Defs))
  ]))

;;                        select-instructions : Ctup -> x86Global
;;-----------------------------------------------------------------------------
;; Translates to x86 instructions while still retaining variables as locations.

(define func-regs 
  (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx)
        (Reg 'rcx) (Reg  'r8) (Reg  'r9)))

(define Lop-to-Xop
  (list (cons '+   'addq)
        (cons '-   'subq)
        (cons 'not 'xorq)))

(define cmp-to-cc
  (list (cons 'eq? 'e)
        (cons '<   'l)
        (cons '>   'g)
        (cons '<= 'le)
        (cons '>= 'ge)))

(define (sel-instr-neg result op arg)
    (if (eq? arg result)
      (list (Instr 'negq (list arg)))
      (list (Instr 'movq (list arg result)) (Instr 'negq (list result)))))

(define (sel-instr-q result op args) 
  ;;Converts arithmetic operations and the not operator. 
  (let ([operator (dict-ref Lop-to-Xop op)])
    (cond 
      [(eq? (length args) 1) (sel-instr-neg (select-instructions-atm result) op
                                            (select-instructions-atm (list-ref args 0)))]
      [(eq? (list-ref args 0) result) 
            (list (Instr operator (list (list-ref args 1) result)))]
      [else 
          (list (Instr 'movq (list 
                              (select-instructions-atm (list-ref args 0)) 
                              (select-instructions-atm result))) 
                (Instr operator (list 
                                (select-instructions-atm (list-ref args 1)) 
                                (select-instructions-atm result))))])))


(define (sel-instr-cmp result op args cod)
  ;; Converts comparator operations.
  (let ([code (dict-ref cmp-to-cc op)])
        (let ([lst 
          (cond 
            [(eq? cod 'j)
              (list (JmpIf code (list-ref result 0))
                    (Jmp (list-ref result 1)))] 
            [else
              (list (Instr cod (list code (ByteReg 'al)))
                    (Instr 'movzbq (list (ByteReg 'al) (select-instructions-atm result))))])])
        (append (list (Instr 'cmpq (reverse (map select-instructions-atm args))))
                lst))))

(define (sel-instr-ref var args)
  (match args 
    [(list tup (Int n)) (list (Instr 'movq (list (select-instructions-atm tup) (Reg 'r11)))
                        (Instr 'movq (list (Deref 'r11 (* 8 (+ n 1))) (select-instructions-atm var))))]))

(define (sel-instr-set! var args)
  (match args 
    [(list tup (Int n) rhs) (let ([x86 (list (Instr 'movq (list (select-instructions-atm tup) (Reg 'r11)))
                                       (Instr 'movq (list (select-instructions-atm rhs) (Deref 'r11 (* 8 (+ n 1))))))])
                           (unless (eq? #f var) (append x86 (Instr 'movq (list (Imm 0) var)))) x86)]))

(define (sel-instr-len var args)
  (match args
    [(list vec) 
      (list (Instr 'movq (list (select-instructions-atm vec) (Reg 'r11)))
            (Instr 'movq (list (Deref 'r11 0) (Reg 'rax)))
            (Instr 'sarq (list (Imm 1) (Reg 'rax)))
            (Instr 'andq (list (Imm 63) (Reg 'rax)))
            (Instr 'movq (list (Reg 'rax) (select-instructions-atm var))))]))

(define (sel-instr-vec var op args)
  (if (eq? op 'vector-ref) 
      (sel-instr-ref var args) 
      (if (eq? op 'vector-length) 
          (sel-instr-len var args)
          (sel-instr-set! var args))))

(define (type-mask type mask)
  (match type
      ;; ret mask
    [(list 'Vector) mask]
      ;; mark vector and recur on sublst
    [(list 'Vector (list 'Vector _ ...) typ ...)
     (type-mask (cons 'Vector typ)
                (bitwise-ior 1 (arithmetic-shift mask 1)))]
      ;; recur on sublst
    [(list 'Vector _ typ ...)
     (type-mask (cons 'Vector typ) (arithmetic-shift mask 1))]))

(define (sel-instr-allo var len type)
  (define tagg (bitwise-ior 1
               (arithmetic-shift len 1)
               (arithmetic-shift (type-mask type 0) 7)))
  
  (list  (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
         (Instr 'addq (list (Imm (* 8 (+ len 1))) (Global 'free_ptr)))
         (Instr 'movq (list (Imm tagg) (Deref 'r11 0)))
         (Instr 'movq (list (Reg 'r11) var))))

(define (sel-instr-col byts)
  (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi))) 
        (Instr 'movq (list (Imm byts) (Reg 'rsi)))
        (Callq 'collect 0)))

(define (sel-instr-glbl var ptr)
  (list (Instr 'movq (list (Global ptr) var))))

(define (select-instructions-atm e)
  (match e 
    [(Var x) (Var x)]
    [(Int x) (Imm x)]
    [(ByteReg x) (ByteReg x)]
    [(Bool bool) (if (eq? bool #t) (Imm 1) (Imm 0))]
    [(Void) (Imm 0)]
    [else (error "Select-Instructions-Atomic Unhandled Case:" e)]))

(define (select-instructions-stmt e) 
  ;; Main function for converting C⟲ statements.
  (match e
    [(Assign (Var x) (Prim 'read arg)) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) (Var x))))]
    [(Prim 'read arg) (list (Callq 'read_int 0))]
    [(Prim 'vector-set! args) (sel-instr-vec #f 'vector-set! args)]
    [(Collect int) (sel-instr-col int)]
    [(Assign (Var x) (Allocate len vec)) (sel-instr-allo (Var x) len vec)]
    [(Assign (Var x) (GlobalValue ptr)) (sel-instr-glbl (Var x) ptr)]
    [(Assign (Var x) (Prim op args)) #:when (op-check op arthms) (sel-instr-q (Var x) op args)]
    [(Assign (Var x) (Prim 'not (list arg))) (sel-instr-q (Var x) 'not (list arg (Int 1)))]
    [(Assign (Var x) (Prim op args)) #:when (op-check op cmps)   (sel-instr-cmp (Var x) op args 'set)]
    [(Assign (Var x) (Prim op args)) #:when (op-check op vecops) (sel-instr-vec (Var x) op args)]
    [(Assign (Var x) (FunRef y n)) (list (Instr 'leaq (list (Global y) (Var x))))]
    [(Assign (Var x) (Call fun args)) (append (select-instructions-stmt (Call fun args)) 
                                              (list (Instr 'movq (list (Reg 'rax) (Var x)))))]
    [(Assign (Var x) atm) (list (Instr 'movq (list (select-instructions-atm atm) (select-instructions-atm (Var x)))))]
    [(Call fun args)
     (let ([set_args (map 
                        (lambda (arg) 
                          (Instr 'movq (list (select-instructions-atm arg)
                                              (list-ref func-regs (index-of args arg)))))
                      args)])
     (append set_args (list (IndirectCallq fun (length args)))))]
    [else (error "Select-Instructions-Statement Unhandled Case:" e)]))

(define (select-instructions-tail lbl e)
  ;; Handles statements in the tail position.
  (match e
    [(Return x) (list (Instr 'movq (list (select-instructions-atm x) (Reg 'rax))) (Jmp (make-conclusion lbl)))]
    [(Goto label) (list (Jmp label))]
    [(IfStmt (Prim op args) (Goto thn) (Goto els)) (sel-instr-cmp (list thn els) op args 'j )]
    [(Seq stmt tail) (append (select-instructions-stmt stmt) (select-instructions-tail lbl tail))]
    [(TailCall fun args) 
     (let ([set_args (map 
                        (lambda (arg) 
                          (Instr 'movq (list (select-instructions-atm arg)
                                             (list-ref func-regs (index-of args arg)))))
                      args)])
          (append set_args (list (TailJmp fun (length args)))))]
    [else (error "Select-Instructions-Tail Unhandled Case:" e)]))

(define (select-instructions-block param-type label) 
  (lambda (block)
    (define set-args
      (if (eq? (car block) (make-start label)) 
        ;; then
      (map 
        (lambda (arg) 
          (Instr 'movq (list (list-ref func-regs (index-of param-type arg)) 
                             (Var (car arg)))))
      param-type) 
        ;; else
      '()
      ))
    (cons (car block) (Block '() (append set-args (select-instructions-tail label (cdr block)))))))

(define (select-instructions p)
  (match p
    [(ProgramDefs info defs)
     (X86ProgramDefs info
                  (map
                   (lambda (def)
                     (match def
                       [(Def label param-type ret-type info blocks)
                        (Def label '() 'Integer (cons (cons 'num-params (length param-type)) info) 
                             (map
                              (select-instructions-block param-type label)
                              blocks))]))
                   defs))]))

;;                    build-cfg : x86Global -> x86Global
;;--------------------------------------------------------------------
;; Builds a control flow graph for the program- each node represents a 
;; block in the code, an edge denotes a jump from one block to another.
;; CFG stored in prog_info.

(define (construct-cfg lbl info block-pairs) 

    ;; Constructs the control flow graph to determine the order in which to process
    ;; the blocks.

    ;Iterate through the block-pairs
  (let ([cfg (make-multigraph '())])
    (map 
      (lambda (block-pair)
        (match block-pair
          [(cons label (Block blk_info tail)) 
            (add-vertex! cfg label)
              ;Now proceed to iterate through every instruction in the block...
            (map 
              (lambda (instr) 
                  ;... and add an edge to the cfg when you find a jump.
                (match instr
                  [(JmpIf _ target) (add-directed-edge! cfg label target)]
                  [(Jmp target) (add-directed-edge! cfg label target)]
                  [_ (void)]))
            tail)]))
    block-pairs)
    (set! info (append info (list (cons 'cfg cfg)))) info))

(define (build-cfg p)
  (match p
    [(X86ProgramDefs info defs)
     (X86ProgramDefs info
                  (map
                   (lambda (def)
                     (match def
                       [(Def label param-type ret-type info blocks)
                        (Def label '() 'Integer (construct-cfg label info blocks) blocks)]))
                   defs))]))


;;       uncover-live : x86Global -> x86Global
;;---------------------------------------------------
;; Perform liveness analysis for register allocation.


(define label->live (make-hash))
(define label->block (make-hash))

(define (uncover-arg loc_or_not)
  ;; Checks if the argument is a valid location or not.

  (match loc_or_not
    [(Var s) (list loc_or_not)]
    [(Reg x) (list loc_or_not)]
    [_ '()]))

(define (uncover-write instr)
  ;; Returns a set of locations that are/can be written to in the instruction.

  (match instr
    [(Callq _ _) (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx)
                      (Reg 'rsi) (Reg 'rdi) (Reg 'r8 )
                      (Reg 'r9 ) (Reg 'r10) (Reg 'r11))]
    [(IndirectCallq _ _) (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx)
                              (Reg 'rsi) (Reg 'rdi) (Reg 'r8 )
                              (Reg 'r9 ) (Reg 'r10) (Reg 'r11))]
    [(TailJmp _ _) (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx)
                        (Reg 'rsi) (Reg 'rdi) (Reg 'r8 )
                        (Reg 'r9 ) (Reg 'r10) (Reg 'r11))]
    [(Instr op args) (list->set (uncover-arg (list-ref args (- (length args) 1))))]
    [(Instr 'cmpq _) (set)]
    [(JmpIf _ _) (set)]
    [(Jmp _) (set)]
    [_ (error "Uncover Write unhandled case: " instr)]))


(define (uncover-read instr)
  ;; Returns a set of locations being read from in an instruction.

  (match instr
    [(Instr 'movq (list source dest))   (list->set (uncover-arg source))]
    [(Instr 'movzbq (list source dest)) (list->set (uncover-arg source))]
    [(Instr op (list source dest))      (list->set (append (uncover-arg dest) (uncover-arg source)))]
    [(Instr op (list snd))              (list->set (uncover-arg snd))]
    [(Jmp label) (set)]
    [(JmpIf _ _) (set)]
    [(Callq target param-cnt) (list->set (take func-regs param-cnt))]
    [(IndirectCallq target param-cnt) (set-union (list->set (uncover-arg target)) 
                                                 (list->set (take func-regs param-cnt)))]
    [(TailJmp target param-cnt) (set-union (list->set (uncover-arg target)) 
                                           (list->set (take func-regs param-cnt)))]
    [_ (error "Uncover Read unhandled case: " instr)]))

(define (uncover-instr live-after-blk)
  ;; Given an instruction, return its live-before set.
  ;; In other words, the live-after set of the instruction
  ;; before it.

  (lambda (instr la-list)
    (match instr
      [(Jmp target)     (cons live-after-blk la-list)]            
      [(JmpIf _ target) (cons live-after-blk la-list)]
      [_ (cons 
          (set->list 
            (set-union 
              (set-subtract 
                (set->list (if (> (length la-list) 0) (list-ref la-list 0) '())) 
                (set->list (uncover-write instr))) 
              (set->list (uncover-read instr)))) 
          la-list)])))

(define (analyze-block lbl label live-after-blk)
  ;; Given a block, perform liveness analysis on it, and store its live-before set 
  ;; in label->live. returns the live-after set.

  (if (eq? label lbl) 
        ;; then
      (dict-ref label->live label)
        ;; else
      (let ([block (dict-ref label->block label)]) 
        (match block
           [(Block info blk) 
            (let ([live-after (foldr (uncover-instr (set->list live-after-blk)) '() blk)])
              (set! info (dict-set info 'live-after live-after))
              (let ([new-block (Block info blk)])
                (dict-set! label->block label new-block)
                (dict-set! label->live label (list->set (car live-after)))
                (list->set (car live-after))))]))))

(define (analyze_dataflow lbl G transfer bottom join) 
  ;; Iteratively performs dataflow analysis until
  ;; live-before sets for all blocks individually converge. 

  (define mapping (make-hash)) 

  (for ([v (in-vertices G)]) 
    (dict-set! mapping v bottom)) 

  (define worklist (make-queue)) 

  (for ([v (in-vertices G)]) 
    (enqueue! worklist v)) 

  (define trans-G (transpose G))

  (while  (not (queue-empty? worklist)) 
          (define node (dequeue! worklist)) 
          (define input 
                  (for/fold ([state bottom]) 
                            ([pred (in-neighbors trans-G node)]) 
                            (join state (dict-ref mapping pred))))
          ; (displayln (format "~a ~a" node input))
          (define output (transfer lbl node input)) 
          (cond 
            [(not (equal? output (dict-ref mapping node))) 
              (dict-set! mapping node output) 
              (for ([v (in-neighbors G node)]) 
                  (enqueue! worklist v))]))          
  mapping) 

(define (liveness-analysis lbl cfg blocks)
  ;; Given the control flow graph, and the program blocks, perform liveness
  ;; analysis and store the result for each block in its respective blk_info. 

  (displayln lbl)

  (define t-cfg (transpose cfg))

  (displayln (tsort t-cfg))

  (set! label->live  (make-hash))
  (set! label->block (make-hash))
  (dict-set! label->live (make-conclusion lbl) (set)) 
    ;; push the blocks in a global dict to make it easy to update the live after
    ;; set in each block and to return the damn thing 
  (map 
    (lambda (block) 
      (match block  
        [(cons label Blk) (dict-set! label->block label Blk)]))
  blocks)

  (analyze_dataflow (make-conclusion lbl) t-cfg analyze-block (set) set-union)
  (hash->list label->block))

(define (uncover-live p)
  (match p
    [(X86ProgramDefs info defs)
     (X86ProgramDefs info
                  (map
                   (lambda (def)
                     (match def
                       [(Def label param-type ret-type info blocks)
                        (Def label '() 'Integer info 
                        (liveness-analysis label (dict-ref info 'cfg) blocks))]))
                   defs))]))


;;                  build-interference : x86-var -> x86-var
;;----------------------------------------------------------------------------
;; Takes the liveness analysis and constructs an interference graph - basically 
;; treat all locations as a node in the graph, and draw an edge between two 
;; nodes if they are live at the same time.

(define (eq-loc? s d)
  (match* (s d)
    [((Var x) (Var x)) #t]
    [((Reg x) (Reg x)) #t]
    [(_ _) #f]))

(define (is-vec? s type-map) 
  (match s
    [(Var vec) (list? (dict-ref type-map vec #f))]
    [else #f]))

(define callee-saved-map 
  (list (Reg 'rsp) (Reg 'rbp) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14) (Reg 'r15)))

(define (interference-edges graph type-map)
  ;;adds edges to the graph.

  (lambda (source l_a-list)
    (when (is-vec? source type-map) (map (lambda (dest) (add-edge! graph source dest)) callee-saved-map))   
    (map
      (lambda (dest) 
        (when (not (has-vertex? graph dest)) (add-vertex! graph dest))
        (when (not (eq-loc? source dest)) (add-edge! graph source dest)))
      l_a-list)))

(define (interference-nodes graph type-map)
  ;;adds vertices to mark locations in the graph.

  (lambda (instr la)
    ; (displayln (format "~a: ~a" instr la))
    (let ([new-vert (set->list (uncover-write instr))])
          (when (not (eq? (length new-vert) 0)) 
            (add-vertex! graph (car new-vert))
            ((interference-edges graph type-map) (car new-vert) la)
          )))) 

(define (block-interference lbl blocks interference-graph type-map)
  ;; Given an empty interference graph, iterates over
  ;; all the blocks to add nodes and edges to it.

  (lambda (label)
    (when (not (eq? label (make-conclusion lbl)))
    (let ([block (dict-ref blocks label)])
      (match block 
        [(Block info instrs)
          (map
            (interference-nodes interference-graph type-map)
          (reverse (cdr (reverse instrs))) (cdr (dict-ref info 'live-after)))])))))

(define (make-interference-graph lbl cfg type-map blocks) 
  ;; calls instr-la-pair, and then construct-interference with the lists of 
  ;; instructions and list of live-after locations to build the interference graph.

  (let ([interference (undirected-graph '())])
        (map (block-interference lbl blocks interference type-map) (tsort (transpose cfg))) 
        ; (print-graph cfg)
        ; (print-graph interference)
        (list (cons 'conflicts interference))))

(define (build-interference p)
  (match p
    [(X86ProgramDefs info defs)
     (X86ProgramDefs info
                  (map
                   (lambda (def)
                     (match def
                       [(Def label param-type ret-type info blocks)
                        (displayln label)
                        (Def label '() 'Integer 
                        (append info (make-interference-graph label (dict-ref info 'cfg) (dict-ref info 'locals-types) blocks)) 
                        blocks)]))
                   defs))]))

;;                allocate-registers : x86-var -> x86-int
;;---------------------------------------------------------------------
;; Takes the interference graph and performs graph coloring to allocate 
;; registers to locations.

(define register-mapping
  (list (cons (Reg 'r15) -5)
        (cons (Reg 'r11) -4)
        (cons (Reg 'rbp) -3)
        (cons (Reg 'rsp) -2)
        (cons (Reg 'rax) -1)
        (cons (Reg 'rcx)  0)
        (cons (Reg 'rdx)  1)
        (cons (Reg 'rsi)  2)
        (cons (Reg 'rdi)  3)
        (cons (Reg 'r8)   4)
        (cons (Reg 'r9)   5)
        (cons (Reg 'r10)  6)
        (cons (Reg 'rbx)  7)
        (cons (Reg 'r12)  8)
        (cons (Reg 'r13)  9)
        (cons (Reg 'r14) 10)))

(define register-mapping-backwards
  (list (cons  0 (Reg 'rcx))
        (cons  1 (Reg 'rdx))
        (cons  2 (Reg 'rsi))
        (cons  3 (Reg 'rdi))
        (cons  4  (Reg 'r8))    
        (cons  5  (Reg 'r9))
        (cons  6 (Reg 'r10))
        (cons  7 (Reg 'rbx))
        (cons  8 (Reg 'r12))
        (cons  9 (Reg 'r13))
        (cons 10 (Reg 'r14))))

(define callee-saved (list -5 -3 -2 7 8 9 10))
(define caller-saved (list -4 -1 0 1 2 3 4 5 6))
(define stack-saved (range 11 111 1))
(define spilled -5)

(define (cmp-priority v1 v2)
  (>= (list-ref v1 1) (list-ref v2 1)))

(define (cget-priority g v)
    ;; Used to set initial priorities for the vertices. Returns cnt of 
    ;; neighbors with colors assigned, which initially is just number 
    ;; of neighbors which are registers.

  (let ([cnt 0]) 
    (map 
      (lambda (v) 
        (match v
          [(Reg x) (set! cnt (+ cnt 1))]
          [_ (+ cnt 0)]))
      (sequence->list (in-neighbors g v))) (list cnt)))

(define (cget-color v g colors locs) 
    ;; Assigns a color to a vertex.

    ;; banned ∈ {0, 10}U{-1, -2, -4, -5}
    ;; So, in the current setup variables spill onto the procedure call stack at values above 10.
    ;; For root stack spills we can consider negative numbers; since the lowest number that a 
    ;; neighbor can possess is -5, we can start assigning root stack spillage numbers from -6.

  (let ([banned 
    (for/list ([e (sequence->list (in-neighbors g (car v)))]) 
      (match e 
        [(Reg x) (dict-ref register-mapping e)]
        [(Var x) #:when (not (eq? (dict-ref colors e #f) #f)) (car (dict-ref colors e))]
        [_ -5]
      ))])

  (let ([available (set->list (set-subtract (list->set (range 11)) (list->set banned)))])
        (match (car v) 
          [(Var vec) 
            (if (and (list? (dict-ref locs vec #f)) (eq? 'Vector (car (dict-ref locs vec #f)))) 
                (let ([mini (apply min banned)])
                     (if (< mini spilled) 
                        (set! spilled (- mini 1)) 
                        (set! spilled (- spilled 1)))
                     (list spilled))
                (if (null? available) 
                    (list (+ 1 (apply max banned)))
                    (list (apply min available))))]))))

(define (color-graph graph locs)
    ;; Performs graph coloring on the interference graph for register allocation. 

  (let ([pq (make-pqueue cmp-priority)] 
        [colors (list (cons (Reg 'rsp) '(-2)) (cons (Reg 'rax) '(-1)) 
                      (cons (Reg 'r15) '(-5)) (cons (Reg 'r11) '(-4)))])
          (map (lambda (vertex)
                (pqueue-push! pq (cons (Var (car vertex)) (cget-priority graph (Var (car vertex))))))
                locs)
          (for ([i (in-range (pqueue-count pq))])
            (let ([popped (pqueue-pop! pq)]) 
              (set! colors (dict-set colors (car popped) (cget-color popped graph colors locs))))) colors))

(define (get-reg colorz v)
  (let ([color (car (dict-ref colorz v))]) (dict-ref register-mapping-backwards color)))

(define (assign-loc instr colorz)
  
  (define reg-assign 10)
  (define root-stack -5)

  (match instr
    [(Var x) #:when (> (car (dict-ref colorz instr)) reg-assign)  (Deref 'rbp (- (* 8 (- (car (dict-ref colorz instr)) reg-assign))))]
    [(Var x) #:when (< (car (dict-ref colorz instr)) root-stack)  (Deref 'r15 (- (* 8 (- (car (dict-ref colorz instr)) root-stack))))]
    [(Var x) #:when (<= (car (dict-ref colorz instr)) reg-assign) (get-reg colorz (Var x))]
    [(Instr op (list arg1 arg2)) (Instr op (list (assign-loc arg1 colorz) (assign-loc arg2 colorz)))]
    [(Instr op (list arg)) (Instr op (list (assign-loc arg colorz)))]
    [(TailJmp target param-cnt) (TailJmp (assign-loc target colorz) param-cnt)]
    [(IndirectCallq target param-cnt) (IndirectCallq (assign-loc target colorz) param-cnt)]
    [_ instr]))

(define (allocate-registers-func prog_info blks)
  (set! spilled -5)
  (begin
    (let ([colorz (color-graph (dict-ref prog_info 'conflicts) (dict-ref prog_info 'locals-types))])
      (let* ([prog_info 
              (append prog_info 
                    (list (cons 'stack-spill (max 0 (- (apply max (map cadr colorz)) 10)))))]
              [prog_info (append prog_info 
                                (list (cons 'num-root-spills (- (- (apply min (map cadr colorz)) -5)))))]) 
          (let ([new-blocks '()])
            (map
              (lambda (blk)
                (match blk
                  [(cons label (Block info block))
                    (let ([new-block
                            (foldr 
                              (lambda (pseudo-instr x86-instr)
                                (cons (assign-loc pseudo-instr colorz) x86-instr)) 
                              '() block)])
                          (set! new-blocks (cons (cons label (Block info new-block)) new-blocks)))]))
              blks)
            (values prog_info new-blocks))))))

(define (allocate-registers p)
  (match p
    [(X86ProgramDefs info defs)
     (X86ProgramDefs info
                  (map
                   (lambda (def)
                     (match def
                       [(Def label param-type ret-type info blocks)
                        (let-values ([(new-info new-blocks) (allocate-registers-func info blocks)])
                         (Def label param-type ret-type new-info new-blocks))]))
                   defs))]))

;;                    patch-instructions : x86int -> x86int
;;-------------------------------------------------------------------------
;; Handle instructions which do not adhere to x86 conventions in terms of 
;; their arguments; cases such as both arguments being memory addresses, 
;; one argument a mem address and the other an immediate value greater than 
;; 2^16. Look at patch-line for more details about the cases dealt with.

(define (is-deref? arg)
  (match arg 
    [(Deref _ _) #t]
    [else #f]))

(define (patch-instructions p)
  (match p
    [(X86ProgramDefs info defs)
     (X86ProgramDefs info
                  (map
                   (lambda (def)
                     (match def
                       [(Def lbl param-type ret-type info blocks)
                        (let ([new-blocks
                              (foldr               
                                (lambda (block new-block)
                                  (match block  
                                    [(cons label (Block info blk))
                                      (cons 
                                        (cons label 
                                          (Block info 
                                            (foldr 
                                              (lambda (pseudo-instr x86-instr) 
                                                (append (patch-line lbl pseudo-instr) x86-instr))
                                              '() blk))) new-block)]))
                                      '() blocks)]) 
                              (Def lbl param-type ret-type info new-blocks))]))
                   defs))]))

(define (patch-line lbl e)
  (match e
      ;A mov operation with both arguments identical is redundant.
    [(Instr 'movq (list same same)) '()]

      ;Any instruction where both args are locations on the stack.
    [(Instr op (list arg1 arg2)) #:when (and (is-deref? arg1) (is-deref? arg2)) 
     (list (Instr 'movq (list arg1 (Reg 'rax))) (Instr op (list (Reg 'rax) arg2)))]
    
      ;Second arg of movzbq must be a register.
    [(Instr 'movzbq (list arg1 arg2)) #:when (not (is-reg? arg2)) 
                      (list (Instr 'movzbq (list arg1 (Reg 'rax)))
                            (Instr 'movq (list (Reg 'rax) arg2)))]
    
      ; Cannot have an instruction where one argument is an immediate value >= 2^16, 
      ; and the other is a memory reference.
    [(Instr op (list (Imm int1) (Deref reg int2))) #:when (> int1 (expt 2 16)) 
                            (list (Instr 'movq (list (Imm int1) (Reg 'rax))) 
                                  (Instr op (list (Reg 'rax) (Deref reg int2))))]
    
      ; second argument of a cmpq cannot be imm; however 
      ; this is already handled by partial evaluator B)
    [(Instr 'cmpq (list arg (Imm arg2))) (list (Instr 'movq (list (Imm arg2) (Reg 'rax)))
                                               (Instr 'cmpq (list arg (Reg 'rax))))]

    [(Instr 'leaq (list arg1 (Deref reg int))) (list (Instr 'movq (list (Reg 'rax) (Deref reg int)))
                                                     (Instr 'leaq (list arg1 (Reg 'rax))))]

    [(TailJmp target param-cnt)             
     (list (Instr 'movq (list target (Reg 'rax)))
           (Jmp (make-conclusion lbl)))]

    [_ (list e)]))


;; prelude-and-conclusion : x86int -> x86int

(define (prelude-and-conclusion p)
  (match p
    [(X86ProgramDefs info defs)
     (X86Program info
      (foldr
       (lambda (def constr) 
         (match def
           [(Def label param-types ret-type info blocks)
            (append constr(generate-prelude label info blocks))])) 
      '() defs))]))

(define (prelude-root-stack lbl)
  (if (eq? lbl 'main)
    (list
    (Instr 'movq (list (Imm 16384) (Reg 'rdi)))
    (Instr 'movq (list (Imm 16384) (Reg 'rsi)))
    (Callq 'initialize 0)
    (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15))))
    
    '()))

(define (generate-prelude lbl info blox)
  (let ([root-stack-space (dict-ref info 'num-root-spills)] 
        [stack-space (dict-ref info 'stack-spill)]
        [tailjmp? (dict-ref info 'tailjmp?)])
    (append  
        (list 
          (cons 
          lbl 
          (Block '() 
            (append
              (list 
              (Instr 'pushq (list (Reg 'rbp))) 
              (Instr 'pushq (list (Reg 'rbx)))
              (Instr 'pushq (list (Reg 'r12)))
              (Instr 'pushq (list (Reg 'r13)))
              (Instr 'pushq (list (Reg 'r14)))
              (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))) 
              (Instr 'subq (list (Imm (align (* 8 stack-space) 16))  (Reg 'rsp))))
              (prelude-root-stack lbl)
              (list
              (Instr 'movq (list (Imm 0) (Deref 'r15 0)))
              (Instr 'addq (list (Imm (align (* 8 root-stack-space) 16)) (Reg 'r15))) 
              (Jmp (make-start lbl))))))) 
        blox  
        (list 
          (cons 
          (make-conclusion lbl) 
          (Block '() 
            (list 
              (Instr 'addq (list (Imm (align (* 8 stack-space) 16)) (Reg 'rsp)))
              (Instr 'popq (list (Reg 'r14)))
              (Instr 'popq (list (Reg 'r13)))
              (Instr 'popq (list (Reg 'r12)))
              (Instr 'popq (list (Reg 'rbx))) 
              (Instr 'subq (list (Imm (align (* 8 root-stack-space) 16)) (Reg 'r15)))
              (Instr 'popq (list (Reg 'rbp)))
              (if tailjmp?
                (IndirectJmp (Reg 'rax))
                (Retq)))
          ))) 
)))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"

(define compiler-passes
  `(  ;; Uncomment the following passes as you finish them.
    ("Partial Eval"          ,pe-Lfun                   ,interp-Lfun              ,type-check-Lfun)
    ("Shrink"                ,shrink                    ,interp-Lfun-prime        ,type-check-Lfun)
    ("Uniquify"              ,uniquify                  ,interp-Lfun-prime        ,type-check-Lfun)
    ("Reveal Funcs"          ,reveal_functions          ,interp-Lfun-prime        ,type-check-Lfun)
    ("Limit Funcs"           ,limit_functions           ,interp-Lfun-prime        ,type-check-Lfun-has-type)
    ("Expose Allocation"     ,expose-allocation         ,interp-Lfun-prime        ,type-check-Lfun)
    ("Uncover Get"           ,uncover-get!              ,interp-Lfun-prime        ,type-check-Lfun)
    ("Remove Complex Opera*" ,remove-complex-opera*     ,interp-Lfun-prime        ,type-check-Lfun)
    ("Explicate Control"     ,explicate-control         ,interp-Cfun              ,type-check-Cfun)
    ("Instruction Selection" ,select-instructions       ,interp-pseudo-x86-3)
    ("Build CFG"             ,build-cfg                 ,interp-pseudo-x86-3)
    ("uncover liveness"      ,uncover-live              ,interp-pseudo-x86-3)
    ("build interference"    ,build-interference        ,interp-pseudo-x86-3)
    ("allocate registers"    ,allocate-registers        ,interp-pseudo-x86-3)
    ("patch instructions"    ,patch-instructions        ,interp-x86-3)
    ("prelude-and-conclusion",prelude-and-conclusion    ,#f)
  ))