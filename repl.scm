(define-module (sicp repl))

(use-modules (sicp interpreter))

(define input-prompt ";;; L-Eval input:")

(define output-prompt ";;; L-Eval value:")

(define (driver-loop)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (let ((output (actual-value input the-global-environment)))
      (announce-output output-prompt)
      (user-print output)))
  (driver-loop))

(define (prompt-for-input string)
  (newline)
  (newline)
  (display string)
  (newline))

(define (announce-output string)
  (newline)
  (display string)
  (newline))

(define the-global-environment (setup-environment))

;; Global definitions
(map (lambda (form)
       (eval form the-global-environment))
     '((define (cons x y)
         (lambda (z) (z x y)))
       (define (car c)
         (c (lambda (x y) x)))
       (define (cdr c)
         (c (lambda (x y) y)))
       (define (null? l)
         (eq? l '()))
       (define (length l)
         (if (null? l)
             0
             (+ 1 (length (cdr l)))))))

