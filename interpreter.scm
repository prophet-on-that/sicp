(define-module (sicp interpreter)
  #:export (user-render))

(use-modules (sicp utils)
             (sicp env)
             (sicp dispatch-table)
             (sicp thunk)
             (srfi srfi-1))

;; Save underlying APPLY, as this is redefined
(define apply-in-underlying-scheme (@@ (guile-user) apply))

;; Exercise 4.1: LIST-OF-VALUES could simply be rewritten using MAP,
;; but isn't done here to emphasise that the implementing language
;; doesn't need to have higher-order procedures, even though the
;; interpreted language will have.
(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      ;;; Reversing the order of the LET expressions here changes the
      ;;; order in which the arguments to the procedure are evaluated.
      (let ((first (eval (first-operand exps) env)))
        (let ((rest (list-of-values (rest-operands exps) env)))
          (cons first rest)))))

(define (eval-if exp env)
  (if (true? (actual-value (if-predicate exp) env))
      (eval (if-consequent exp) env)
      (eval (if-alternative exp) env)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (eval (first-exp exps) env))
        (else (eval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)
                       (eval (assignment-value exp) env)
                       env)
  'ok)

(define (eval-definition exp env)
  (define-variable!
    (definition-variable exp)
    (eval (definition-value exp) env)
    env)
  'ok)

(define (eval-undefinition exp env)
  (undefine-variable!
   (undefinition-variable exp)
   env)
  'ok)

;;; Cons

(define (make-cons-cell a b)
  (list 'cons-cell a b))

(define (cons-cell? c)
  (tagged-list? c 'cons-cell))

(define (cons-cell-car c)
  (cadr c))

(define (cons-cell-cdr c)
  (caddr c))

(define (cons-exp-car exp)
  (cadr exp))

(define (cons-exp-cdr exp)
  (caddr exp))

(define (eval-cons exp env)
  (make-cons-cell (delay-it (cons-exp-car exp) env)
                  (delay-it (cons-exp-cdr exp) env)))

(define (eval-car exp env)
  (let ((c (actual-value (cadr exp) env)))
    (if (tagged-list? c 'cons-cell)
        (cons-cell-car c)
        (error "Not a cons cell -- EVAL-CAR" (cadr exp)))))

(define (eval-cdr exp env)
  (let ((c (actual-value (cadr exp) env)))
    (if (cons-cell? c)
        (cons-cell-cdr c)
        (error "Not a cons cell -- EVAL-CDR" (cadr exp)))))

;;; Syntax of expressions

(define (self-evaluating? exp)
  (cond ((number? exp) #t)
        ((string? exp) #t)
        (else #f)))

(define (variable? exp) (symbol? exp))

(define (text-of-quotation exp) (cadr exp))

(define (assignment-variable exp) (cadr exp))

(define (assignment-value exp) (caddr exp))

(define (make-assignment var val)
  (list 'set! var val))

(define (make-function-definition name arguments body)
  (cons 'define (cons (cons name arguments) body)))

(define (is-definition? exp)
  (tagged-list? exp 'define))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)           ; formal parameters
                   (cddr exp))))        ; body

(define (undefinition-variable exp)
  (cadr exp))

(define (make-lambda-parameter variable evaluation-type)
  (cons variable evaluation-type))

(define (lambda-parameter-variable param)
  (car param))

(define (lambda-parameter-evaluation-type param)
  (cdr param))

(define evaluation-types (list 'strict 'lazy 'lazy-memo))

(define (parse-lambda-parameter param)
  (cond ((variable? param)
         (make-lambda-parameter param 'lazy-memo))
        ((and (pair? param)
              (= 2 (length param)))
         (if (member (cadr param) evaluation-types)
             (make-lambda-parameter (car param) (cadr param))
             (error "Unrecognised evaluation type - PARSE-LAMBDA-PARAMETER" (cadr param))))
        (else
         (error "Unrecognised lambda parameter form - PARSE-LAMBDA-PARAMETER" param))))

(define (lambda-parameters exp)
  (map parse-lambda-parameter (cadr exp)))

(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

(define (if-predicate exp) (cadr exp))

(define (if-consequent exp) (caddr exp))

(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))

(define (begin-actions exp) (cdr exp))

(define (last-exp? seq) (null? (cdr seq)))

(define (first-exp seq) (car seq))

(define (rest-exps seq) (cdr seq))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq)
  (cons 'begin seq))

(define (application? exp) (pair? exp))

(define (make-application operator operands)
  (cons operator operands))

(define (operator exp) (car exp))

(define (operands exp) (cdr exp))

;; Exercise 4.2: with this, the ordering of evaluation in EVAL can be
;; changed such that applications are evaluated first.
;; (define (application? exp) (tagged-list exp 'call))
;; (define (operator exp) (cadr exp))
;; (define (operands exp) (cddr exp))

(define (no-operands? ops) (null? ops))

(define (first-operand ops) (car ops))

(define (rest-operands ops) (cdr ops))

;;; Cond

(define (cond-clauses exp) (cdr exp))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define (cond-predicate clause) (car clause))

(define (cond-actions clause) (cdr clause))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (functional-cond-clause? clause)
  (eq? '=> (list-ref clause 1)))

(define (functional-cond-action clause)
  (list-ref clause 2))

(define (expand-clauses clauses)
  (if (null? clauses)
      'false                            ; no else clause
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't last -- COND->IF" clauses))
            (if (functional-cond-clause? first)
                (let ((var (gensym)))
                  (make-let
                   (list (list var (cond-predicate first)))
                   (list
                    (make-if var
                             (make-application
                              (functional-cond-action first)
                              (list var))
                             (expand-clauses rest)))))
                (make-if (cond-predicate first)
                         (sequence->exp (cond-actions first))
                         (expand-clauses rest)))))))

;;; And

(define (singleton? list)
  (and (not (null? list))
       (null? (cdr list))))

(define (and-clauses exp)
  (cdr exp))

(define (and->if exp)
  (define (helper clauses)
    (if (singleton? clauses)
        (car clauses)
        (let ((var (gensym)))
          (make-let
           (list (list var (car clauses)))
           (list (make-if var (helper (cdr clauses)) 'false))))))
  (if (null? (and-clauses exp))
      'true                             ; Value for an empty AND form
      (helper (and-clauses exp))))

;;; Or

(define (or-clauses exp)
  (cdr exp))

(define (or->if exp)
  (define (helper clauses)
    (if (singleton? clauses)
        (car clauses)
        (let ((var (gensym)))
          (make-let
           (list (list var (car clauses)))
           (list (make-if var
                          var
                          (helper (cdr clauses))))))))
  (if (null? (or-clauses exp))
      'true                             ; Value for an empty OR form
      (helper (or-clauses exp))))

;;; Let

(define (make-let definitions body)
  (cons 'let (cons definitions body)))

(define (standard-let? exp)
  (pair? (cadr exp)))

(define (standard-let-definitions exp)
  (cadr exp))

(define (standard-let-body exp)
  (cddr exp))

(define (named-let? exp)
  (variable? (cadr exp)))

(define (named-let-name exp)
  (cadr exp))

(define (named-let-definitions exp)
  (caddr exp))

(define (named-let-body exp)
  (cdddr exp))

(define (let->combination exp)
  (cond ((standard-let? exp)
         (let ((parameters (map car (standard-let-definitions exp)))
               (arguments (map cadr (standard-let-definitions exp))))
           (make-application
            (make-lambda parameters (standard-let-body exp))
            arguments)))
        ((named-let? exp)
         ;; Define the named function in a new frame and invoke it
         ;; with the initial arguments. The implementation could be
         ;; optimised by removing the LET to construct the new
         ;; environment and adding a new frame directly.
         (make-let '()
                   (list
                    (make-function-definition (named-let-name exp)
                                              (map car (named-let-definitions exp))
                                              (named-let-body exp))
                    (make-application (named-let-name exp)
                                      (map cadr (named-let-definitions exp))))))
        (else
         (error "Malformed let form -- LET->COMBINATION" exp))))

;;; Let*

(define (let*-definitions exp)
  (cadr exp))

(define (let*-body exp)
  (cddr exp))

(define (let*->nested-lets exp)
  (define (helper definitions)
    (if (singleton? definitions)
        (make-let definitions (let*-body exp))
        (make-let (list (car definitions))
                  (list (helper (cdr definitions))))))
  (if (null? (let*-definitions exp))
      (error "Invalid LET* form" exp)
      (helper (let*-definitions exp))))

;;; While

;;; Usage: (while <cond> <body>)

(define (while-cond exp)
  (cadr exp))

(define (while-body exp)
  (cddr exp))

(define (while->combination exp)
  (let ((fn-name (gensym)))
    (make-let '()
              (list
               (make-function-definition fn-name
                                         '()
                                         (list
                                          (make-if (while-cond exp)
                                                   (make-begin
                                                    (append
                                                     (while-body exp)
                                                     (list
                                                      (make-application fn-name '()))))
                                                   #f)))
               (make-application fn-name '())))))

;; Quasiquote version of WHILE->COMBINATION. This version is much more
;; readable, but duplicates syntax definitions of the interpreted
;; language.
;; (define (while->combination exp)
;;   (let ((fn-name (gensym)))
;;     `(let ()
;;        (define (,fn-name)
;;          (if ,(while-cond exp)
;;              (begin
;;                ,@(while-body exp)
;;                (,fn-name))))
;;        (,fn-name))))

;;; Letrec

(define (letrec-bindings exp)
  (cadr exp))

(define (letrec-body exp)
  (cddr exp))

(define (letrec->combination exp)
  (let ((definitions (map (lambda (binding)
                            (list (car binding) ''*unassigned*))
                          (letrec-bindings exp)))
        (set-exps (map (lambda (binding)
                         (make-assignment (car binding) (cadr binding)))
                       (letrec-bindings exp))))
    (make-let definitions
              (append set-exps (letrec-body exp)))))

;;; Unless

(define (unless-predicate exp)
  (cadr exp))

(define (unless-alternative exp)
  (caddr exp))

(define (unless-consequent exp)
  (cadddr exp))

(define (unless->if exp)
  (make-if (unless-predicate exp)
           (unless-consequent exp)
           (unless-alternative exp)))

;;; Predicate testing

(define (true? x)
  (not (eq? x 'false)))

(define (false? x)
  (eq? x 'false))

;;; Representing procedures

(define (scan-out-defines body)
  (let ((definition-variables (map definition-variable
                                   (filter is-definition? body))))
    (if (not (null? definition-variables))
        (list
         (make-let (map (lambda (var)
                          (list var ''*unassigned*))
                        definition-variables)
                   (map (lambda (exp)
                          (if (is-definition? exp)
                              (make-assignment (definition-variable exp)
                                               (definition-value exp))
                              exp))
                        body)))
        body)))

(define (make-procedure parameters body env)
  ;; (list 'procedure parameters (scan-out-defines body) env)
  (list 'procedure parameters body env))

(define (compound-procedure? p)
  (tagged-list? p 'procedure))

(define (procedure-parameters p)
  (cadr p))

(define (procedure-body p)
  (caddr p))

(define (procedure-environment p)
  (cadddr p))

;;; Eval and apply

(define eval-dispatch-table (create-dispatch-table))

(define (put-eval-dispatch symbol fn)
  (dispatch-table-put! eval-dispatch-table symbol fn))

(define (get-eval-dispatch symbol)
  (dispatch-table-get eval-dispatch-table symbol))

(define-public (eval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp)
         (lookup-variable-value exp env))
        ((pair? exp)
         (let ((dispatch-fn (get-eval-dispatch (car exp))))
           (cond (dispatch-fn
                  (dispatch-fn exp env))
                 ((application? exp)
                  (apply (actual-value (operator exp) env)
                         (operands exp)
                         env))
                 (else
                  (error "Unknown expression type -- EVAL" exp)))))
        (else
         (error "Unknown expression type -- EVAL" exp))))

(define (native-list->list exp)
  (if (pair? exp)
      (make-cons-cell (native-list->list (car exp))
                      (native-list->list (cdr exp)))
      exp))

(put-eval-dispatch
 'quote
 (lambda (exp env)
   (native-list->list (text-of-quotation exp))))

(put-eval-dispatch 'set! eval-assignment)

(put-eval-dispatch 'define eval-definition)

(put-eval-dispatch 'undefine! eval-undefinition)

(put-eval-dispatch 'if eval-if)

(put-eval-dispatch
 'lambda
 (lambda (exp env)
   (make-procedure (lambda-parameters exp)
                   (lambda-body exp)
                   env)))

(put-eval-dispatch
 'begin
 (lambda (exp env)
   (eval-sequence (begin-actions exp) env)))

(put-eval-dispatch
 'cond
 (lambda (exp env)
   (eval (cond->if exp) env)))

(define (apply procedure arguments env)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure
          procedure
          (map (lambda (arg)
                 (actual-value arg env))
               arguments)))
        ((compound-procedure? procedure)
         (eval-sequence
          (procedure-body procedure)
          (extend-environment
           (map lambda-parameter-variable (procedure-parameters procedure))
           (map (lambda (param arg)
                  (cond ((eq? 'strict (lambda-parameter-evaluation-type param))
                         (actual-value arg env))
                        ((eq? 'lazy-memo (lambda-parameter-evaluation-type param))
                         (delay-it arg env))
                        ((eq? 'lazy (lambda-parameter-evaluation-type param))
                         (delay-it arg env #:memo #f))
                        (else
                         (error "Unsupported evaluation type -- APPLY" (lambda-parameter-evaluation-type param)))))
                (procedure-parameters procedure)
                arguments)
           (procedure-environment procedure))))
        (else
         (error
          "Unknown procedure type -- APPLY" procedure))))

(put-eval-dispatch
 'and
 (lambda (exp env)
   (eval (and->if exp) env)))

(put-eval-dispatch
 'or
 (lambda (exp env)
   (eval (or->if exp) env)))

(put-eval-dispatch
 'let
 (lambda (exp env)
   (eval (let->combination exp) env)))

(put-eval-dispatch
 'let*
 (lambda (exp env)
   (eval (let*->nested-lets exp) env)))

(put-eval-dispatch
 'while
 (lambda (exp env)
   (eval (while->combination exp) env)))

(put-eval-dispatch
 'letrec
 (lambda (exp env)
   (eval (letrec->combination exp) env)))

(put-eval-dispatch 'cons eval-cons)
(put-eval-dispatch 'car eval-car)
(put-eval-dispatch 'cdr eval-cdr)

;;; Eval with syntax analysis

(define (eval-analyse exp env)
  ((analyse exp) env))

(define analyse-dispatch-table (create-dispatch-table))

(define (analyse exp)
  (cond ((self-evaluating? exp)
         (analyse-self-evaluating exp))
        ((variable? exp)
         (analyse-variable exp))
        ((pair? exp)
         (let ((dispatch-fn (dispatch-table-get analyse-dispatch-table (car exp))))
           (cond (dispatch-fn
                  (dispatch-fn exp))
                 ((application? exp)
                  (analyse-application exp))
                 (else
                  (error "Unknown expression type -- ANALYSE" exp)))))
        (else
         (error "Unknown expression type -- ANALYSE" exp))))

(define (analyse-self-evaluating exp)
  (lambda (env) exp))

(define (analyse-variable exp)
  (lambda (env)
    (lookup-variable-value exp env)))

(dispatch-table-put! analyse-dispatch-table
                     'quote
                     (lambda (exp)
                       (let ((qval (text-of-quotation exp)))
                         (lambda (env) qval))))

(dispatch-table-put! analyse-dispatch-table
                     'set!
                     (lambda (exp)
                       (let ((var (assignment-variable exp))
                             (vproc (analyse (assignment-value exp))))
                         (lambda (env)
                           (set-variable-value! var (vproc env) env)
                           'ok))))

(dispatch-table-put! analyse-dispatch-table
                     'define
                     (lambda (exp)
                       (let ((var (definition-variable exp))
                             (vproc (analyse (definition-value exp))))
                         (lambda (env)
                           (define-variable! var (vproc env) env)))))

(dispatch-table-put! analyse-dispatch-table
                     'if
                     (lambda (exp)
                       (let ((pproc (analyse (if-predicate exp)))
                             (cproc (analyse (if-consequent exp)))
                             (aproc (analyse (if-alternative exp))))
                         (lambda (env)
                           (if (true? (pproc env))
                               (cproc env)
                               (aproc env))))))

(define (analyse-sequence exps)
  (define (sequentially proc1 proc2)
    (lambda (env)
      (proc1 env)
      (proc2 env)))
  ;; TODO: simplify with FOLDL
  (define (loop first-proc rest-procs)
    (if (null? rest-procs)
        first-proc
        (loop (sequentially first-proc (car rest-procs))
              (cdr rest-procs))))
  (let ((procs (map analyse exps)))
    (if (null? procs)
        (error "Empty sequence -- ANALYSE")
        (loop (car procs) (cdr procs)))))

(dispatch-table-put! analyse-dispatch-table
                     'lambda
                     (lambda (exp)
                       (let ((vars (lambda-parameters exp))
                             (bproc (analyse-sequence (lambda-body exp))))
                         (lambda (env)
                           (make-procedure vars bproc env)))))

(define (analyse-application exp)
  (let ((fproc (analyse (operator exp)))
        (aprocs (map analyse (operands exp))))
    (lambda (env)
      (execute-application (fproc env)
                           (map (lambda (aproc) (aproc env))
                                aprocs)))))

(define (execute-application proc args)
  (cond ((primitive-procedure? proc)
         (apply-primitive-procedure proc args))
        ((compound-procedure? proc)
         ((procedure-body proc)
          (extend-environment (map lambda-parameter-variable (procedure-parameters proc))
                              args
                              (procedure-environment proc))))
        (else
         (error "Unknown procedure type -- EXECUTE-APPLICATION" proc))))

(dispatch-table-put! analyse-dispatch-table
                     'let
                     (lambda (exp)
                       (analyse (let->combination exp))))

(dispatch-table-put! analyse-dispatch-table
                     'begin
                     (lambda (exp)
                       (analyse-sequence (begin-actions exp))))

(dispatch-table-put! analyse-dispatch-table
                     'unless
                     (lambda (exp)
                       (analyse (unless->if exp))))

;;; Environment

(define-public (setup-environment)
  (let ((initial-env
         (extend-environment (primitive-procedure-names)
                             (primitive-procedure-objects)
                             the-empty-environment)))
    (define-variable! 'true 'true initial-env)
    (define-variable! 'false 'false initial-env)
    initial-env))

;;; Primitive procedures

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc)
  (cadr proc))

(define primitive-procedures
  (list (list 'eq? (lambda (m n)
                    (if (eq? m n)
                        'true
                        'false)))
        (list '= (lambda (m n)
                   (if (= m n)
                       'true
                       'false)))
        (list '+ +)
        (list '- -)
        (list '* *)
        (list '/ /)))

(define (primitive-procedure-names)
  (map car primitive-procedures))

(define (primitive-procedure-objects)
  (map (lambda (proc)
         (list 'primitive (cadr proc)))
       primitive-procedures))

(define (apply-primitive-procedure proc args)
  (apply-in-underlying-scheme (primitive-implementation proc) args))

;;; Utils

(define-public user-render-default-max-depth 10)

(define* (user-render obj #:key (force? #f) (max-depth user-render-default-max-depth))
  (define (helper obj depth)
    (cond ((> depth max-depth)
           '...)
          ((thunk? obj)
           (if force?
               (helper (force-it obj) depth)
               '<thunk>))
          ((evaluated-thunk? obj)
           (helper (thunk-value obj) depth))
          ((cons-cell? obj)
           (cons (helper (cons-cell-car obj) 0)
                 (helper (cons-cell-cdr obj) (+ depth 1))))
          ((compound-procedure? obj)
           (list 'compound-procedure
                 (procedure-parameters obj)
                 (procedure-body obj)
                 '<procedure-env>))
          (else obj)))
  (helper obj 0))

;; Lazy

(define-public (actual-value exp env)
  (force-it (eval exp env)))

(define (force-it obj)
  (cond ((thunk? obj)
         (let ((result (actual-value
                        (thunk-exp obj)
                        (thunk-env obj))))
           (if (thunk-memo obj)
               (begin
                 (set-car! obj 'evaluated-thunk)
                 (set-car! (cdr obj) result) ; replace exp with its value
                 (set-cdr! (cdr obj) '())))     ; forget unneeded env
           result))
        ((evaluated-thunk? obj)
         (thunk-value obj))
        (else obj)))

;;; Execise 4.28

;; The following code illustrates why EVAL needs to force the operator
;; of an application before passing it to APPLY. This is the case
;; where the operator is a thunk.

;; (define (identity x)
;;   x)
;; (define f cons)
;; (f 1 2)
