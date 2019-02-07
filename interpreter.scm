(define-module (sicp interpreter))

(use-modules (sicp env)
             (sicp dispatch-table))

;; Save underlying APPLY, as this is redefined
(define apply-in-underlying-scheme (@@ (guile-user) apply))

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

(define (amb-choices exp)
  (cdr exp))

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

(define-public (ambeval exp env succeed fail)
  ((analyse exp) env succeed fail))

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
  (lambda (env succeed fail)
    (succeed exp fail)))

(define (analyse-variable exp)
  (lambda (env succeed fail)
    (succeed (lookup-variable-value exp env)
             fail)))

(dispatch-table-put! analyse-dispatch-table
                     'quote
                     (lambda (exp)
                       (let ((qval (text-of-quotation exp)))
                         (lambda (env succeed fail)
                           (succeed qval fail)))))

(dispatch-table-put! analyse-dispatch-table
                     'set!
                     (lambda (exp)
                       (let ((var (assignment-variable exp))
                             (vproc (analyse (assignment-value exp))))
                         (lambda (env succeed fail)
                           (vproc env
                                  (lambda (val fail2)
                                    (let ((old-value
                                           (lookup-variable-value var env)))
                                      (set-variable-value! var val env)
                                      (succeed 'ok
                                               (lambda ()
                                                 (set-variable-value! var old-value env)
                                                 (fail2)))))
                                  fail)))))

(dispatch-table-put! analyse-dispatch-table
                     'define
                     (lambda (exp)
                       (let ((var (definition-variable exp))
                             (vproc (analyse (definition-value exp))))
                         (lambda (env succeed fail)
                           (vproc env
                                  (lambda (val fail2)
                                    (define-variable! var val env)
                                    (succeed 'ok fail2))
                                  fail)))))

(dispatch-table-put! analyse-dispatch-table
                     'if
                     (lambda (exp)
                       (let ((pproc (analyse (if-predicate exp)))
                             (cproc (analyse (if-consequent exp)))
                             (aproc (analyse (if-alternative exp))))
                         (lambda (env succeed fail)
                           (pproc env
                                  (lambda (pred-value fail2)
                                    (if (true? pred-value)
                                        (cproc env succeed fail2)
                                        (aproc env succeed fail2)))
                                  fail)))))

(define (analyse-sequence exps)
  (define (sequentially a b)
    (lambda (env succeed fail)
      (a env
         (lambda (a-value fail2)
           (b env succeed fail2))
         fail)))
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
                         (lambda (env succeed fail)
                           (succeed (make-procedure vars bproc env)
                                    fail)))))

(define (analyse-application exp)
  (let ((fproc (analyse (operator exp)))
        (aprocs (map analyse (operands exp))))
    (lambda (env succeed fail)
      (fproc env
             (lambda (proc fail2)
               (get-args aprocs
                         env
                         (lambda (args fail3)
                           (execute-application proc args succeed fail3))
                         fail2))
             fail))))

(define (get-args aprocs env succeed fail)
  (if (null? aprocs)
      (succeed '() fail)
      ((car aprocs) env
       (lambda (arg fail2)
         (get-args (cdr aprocs)
                   env
                   (lambda (args fail3)
                     (succeed (cons arg args)
                              fail3))
                   fail2))
       fail)))

(define (execute-application proc args succeed fail)
  (cond ((primitive-procedure? proc)
         (succeed (apply-primitive-procedure proc args)
                  fail))
        ((compound-procedure? proc)
         ((procedure-body proc)
          (extend-environment (procedure-parameters proc)
                              args
                              (procedure-environment proc))
          succeed
          fail))
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

(dispatch-table-put! analyse-dispatch-table
                     'amb
                     (lambda (exp)
                       (let ((cprocs (map analyse (amb-choices exp))))
                         (lambda (env succeed fail)
                           (define (try-next choices)
                             (if (null? choices)
                                 (fail)
                                 ((car choices) env
                                  succeed
                                  (lambda ()
                                    (try-next (cdr choices))))))
                           (try-next cprocs)))))

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
        (list 'null? (lambda (list)
                       (if (null? list)
                           'true
                           'false)))
        (list 'list list)
        (list '= (lambda (m n)
                   (if (= m n)
                       'true
                       'false)))
        (list '+ +)
        (list '- -)
        (list '* *)
        (list '>= (lambda (m n)
                    (if (>= m n)
                        'true
                        'false)))
        (list '> (lambda (m n)
                   (if (> m n)
                       'true
                       'false)))
        (list 'eq? (lambda (m n)
                     (if (eq? m n)
                         'true
                         'false)))
        (list 'abs abs)))

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
