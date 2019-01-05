(define-module (sicp interpreter))

(use-modules (srfi srfi-1)
             (sicp env))

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
  (if (true? (eval (if-predicate exp) env))
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

;;; Syntax of expressions

(define (self-evaluating? exp)
  (cond ((number? exp) #t)
        ((string? exp) #t)
        (else #f)))

(define (variable? exp) (symbol? exp))

(define (text-of-quotation exp) (cadr exp))

(define (assignment-variable exp) (cadr exp))

(define (assignment-value exp) (caddr exp))

(define (make-function-definition name arguments body)
  (cons 'define (cons (cons name arguments) body)))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cddr exp)           ; formal parameters
                   (cddr exp))))        ; body

(define (undefinition-variable exp)
  (cadr exp))

(define (lambda-parameters exp) (cadr exp))

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

;;; Predicate testing

(define (true? x)
  (not (eq? x 'false)))

(define (false? x)
  (eq? x 'false))

;;; Representing procedures

(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (tagged-list? p symbol)
  (and (pair? p)
       (eq? (car p) symbol)))

(define (compound-procedure? p)
  (tagged-list? p 'procedure))

(define (procedure-parameters p)
  (cadr p))

(define (procedure-body p)
  (caddr p))

(define (procedure-environment p)
  (cadddr p))

;;; Eval and apply

(define eval-dispatch-table '())

(define (put-eval-dispatch symbol fn)
  (set! eval-dispatch-table
        (alist-cons symbol fn eval-dispatch-table)))

(define  (get-eval-dispatch symbol)
  (let ((pair (assoc symbol eval-dispatch-table)))
    (if pair
        (cdr pair)
        #f)))

(define-public (eval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp)
         (lookup-variable-value exp env))
        ((pair? exp)
         (let ((dispatch-fn (get-eval-dispatch (car exp))))
           (cond (dispatch-fn
                  (dispatch-fn exp env))
                 ((application? exp)
                  (apply (eval (operator exp) env)
                         (list-of-values (operands exp) env)))
                 (else
                  (error "Unknown expression type -- EVAL" exp)))))
        (else
         (error "Unknown expression type -- EVAL" exp))))

(put-eval-dispatch
 'quote
 (lambda (exp env)
   (text-of-quotation exp)))

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

(define (apply procedure arguments)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
        ((compound-procedure? procedure)
         (eval-sequence
          (procedure-body procedure)
          (extend-environment
           (procedure-parameters procedure)
           arguments
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
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cons cons)
        (list 'null? null?)
        (list 'list list)))

(define (primitive-procedure-names)
  (map car primitive-procedures))

(define (primitive-procedure-objects)
  (map (lambda (proc)
         (list 'primitive (cadr proc)))
       primitive-procedures))

(define (apply-primitive-procedure proc args)
  (apply-in-underlying-scheme (primitive-implementation proc) args))

;;; Utils

(define-public (user-print object)
  (if (compound-procedure? object)
      (display (list 'compound-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))
