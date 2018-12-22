(define-module (sicp ch4))

(use-modules (srfi srfi-1))

;; Exercise 4.1: LIST-OF-VALUES could simply be rewritten using MAP,
;; but isn't done here to emphasise that the implementing language
;; doesn't need to have higher-order procedures, even though the
;; interpreted language will have.
(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      ;;; Reversing the order of the LET expressions here changes the
      ;;; order in which the arguments to the procedure are evaluated.
      (let ((first (eval (first-operands exps) env)))
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
  (define-value!
    (definition-variable exp)
    (eval (definition-value exp) env)
    env)
  'ok)

; Syntax of expressions

(define (self-evaluating? exp)
  (cond ((number? exp) #t)
        ((string? exp) #t)
        (else #f)))

(define (variable? exp) (symbol? exp))

(define (text-of-quotation exp) (cadr exp))

(define (assignment-variable exp) (cadr exp))

(define (assignment-value exp) (caddr exp))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cddr exp)           ; formal parameters
                   (cddr exp))))        ; body

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

; Cond

(define (cond-clauses exp) (cdr exp))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define (cond-predicate clause) (car clause))

(define (cond-actions clause) (cdr clause))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
      'false                            ; no else clause
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't last -- COND->IF" clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))

; And

(define (singleton? list)
  (and (not (null? list))
       (null? (cdr list))))

(define (and-clauses exp)
  (cdr exp))

(define (eval-and exp env)
  (eval-and-clauses (and-clauses exp) env))

(define (eval-and-clauses clauses env)
  (if (null? clauses)
      'true                  ; Value for an empty AND expression
      (let ((val (eval (car clauses) env)))
        (if (true? val)
            (if (singleton? clauses)
                val
                (eval-and-clauses (cdr clauses) env ))
            'false))))

; Or

(define (or-clauses exp)
  (cdr exp))

(define (eval-or exp env)
  (eval-or-clauses (or-clauses exp) env))

(define (eval-or-clauses clauses env)
  (if (null? clauses)
      'true                             ; Value for an empty OR expression
      (let ((val (eval (car clauses) env)))
        (if (true? val)
            val
            (if (singleton? clauses)
                'false
                (eval-or-clauses (cdr clauses) env))))))

;;; Let

(define (make-let definitions body)
  (cons 'let (cons definitions body)))

(define (let-definitions exp)
  (cadr exp))

(define (let-body exp)
  (cddr exp))

(define (let->combination exp)
  (let ((parameters (map car (let-definitions exp)))
        (arguments (map cadr (let-definitions exp))))
    (make-application
     (make-lambda parameters (let-body exp))
     arguments)))

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

; Eval and apply

(define eval-dispatch-table '())

(define (put-eval-dispatch symbol fn)
  (set! eval-dispatch-table
        (alist-cons symbol fn eval-dispatch-table)))

(define  (get-eval-dispatch symbol)
  (let ((pair (assoc symbol eval-dispatch-table)))
    (if pair
        (cdr pair)
        #f)))

(define (eval exp env)
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

(put-eval-dispatch 'and eval-and)

(put-eval-dispatch 'or eval-or)

(put-eval-dispatch
 'let
 (lambda (exp env)
   (eval (let->combination exp) env)))

(put-eval-dispatch
 'let*
 (lambda (exp env)
   (eval (let*->nested-lets exp) env)))
