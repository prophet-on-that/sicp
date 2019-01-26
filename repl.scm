(define-module (sicp repl))

(use-modules (sicp interpreter))

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
