(define-module (sicp env))

(use-modules ((srfi srfi-1)))

(define (enclosing-environment env)
  (cdr env))

(define (first-frame env)
  (car env))

(define-public the-empty-environment '())

(define (make-frame variables values)
  (list (map cons variables values)))

(define (frame-bindings frame)
  (car frame))

(define (set-frame-bindings! frame bindings)
  (set-car! frame bindings))

(define (frame-variables frame)
  (map car (frame-bindings frame)))

(define (frame-values frame)
  (map cdr (frame-bindings frame)))

(define (add-binding-to-frame! var val frame)
  (set-frame-bindings! frame (cons (cons var val) (frame-bindings frame))))

(define-public (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied" vars vals)
          (error "Too few arguments supplied" vars vals))))

(define (lookup-binding-in-frame var frame)
  (define (scan bindings)
    (cond ((null? bindings)
           #f)
          ((eq? var (caar bindings))
           (car bindings))
          (else
           (scan (cdr bindings)))))
  (scan (frame-bindings frame)))

(define (lookup-binding-in-env var env)
  (if (eq? env the-empty-environment)
      (error "Unbound variable" var)
      (let ((binding (lookup-binding-in-frame var (first-frame env))))
        (if (pair? binding)
            binding
            (lookup-binding-in-env var (enclosing-environment env))))))

(define-public (lookup-variable-value var env)
  (let ((val (cdr (lookup-binding-in-env var env))))
    (if (eq? val '*unassigned*)
        (error "Variable is unassigned" var)
        val)))

(define-public (set-variable-value! var val env)
  (set-cdr! (lookup-binding-in-env var env) val))

(define-public (define-variable! var val env)
  (let ((frame (first-frame env)))
    (let ((binding (lookup-binding-in-frame var frame)))
      (if (pair? binding)
          (set-cdr! binding val)
          (add-binding-to-frame! var val frame)))))

;; Deletes the first occurrence of VAR in environment ENV. Throws an
;; error if no occurrences are found.
(define-public (undefine-variable! var env)
  (define (undefine-from-frame! frame)
    (let ((old-binding-count (length (frame-bindings frame)))
          (new-bindings (alist-delete var (frame-bindings frame) eq?)))
      (set-frame-bindings! frame new-bindings)
      (< (length new-bindings) old-binding-count)))
  (if (eq? env the-empty-environment)
      (error "Cannot undefine unbound variable" var)
      (let ((undefined? (undefine-from-frame! (first-frame env))))
        (if (not undefined?)
            (undefine-variable! var (enclosing-environment env))))))
