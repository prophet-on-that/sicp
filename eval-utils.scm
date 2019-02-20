(define-module (sicp eval-utils))

(define-public (prompt-for-input string)
  (newline)
  (newline)
  (display string)
  (newline))

(define-public (tagged-list? p symbol)
  (and (pair? p)
       (eq? (car p) symbol)))
