(define-module (sicp repl))

(use-modules (sicp interpreter)
             (sicp eval-utils))

(define input-prompt ";;; L-Eval input:")

(define output-prompt ";;; L-Eval value:")

(define* (driver-loop #:key (force-print? #t) (max-print-depth user-render-default-max-depth))
  (define (helper)
    (prompt-for-input input-prompt)
    (let ((input (read)))
      (let ((output (actual-value input the-global-environment)))
        (announce-output output-prompt)
        (display (user-render output #:force? force-print? #:max-depth max-print-depth))))
    (helper))
  (helper))

(define (announce-output string)
  (newline)
  (display string)
  (newline))

(define the-global-environment (setup-environment))

(map (lambda (exp)
       (eval exp the-global-environment))
     '((define (null? l)
         (eq? l '()))
       (define (length l)
         (if (null? l)
             0
             (+ 1 (length (cdr l)))))))

