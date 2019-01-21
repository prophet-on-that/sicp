(define-module (sicp utils))

(define-public (tagged-list? p symbol)
  (and (pair? p)
       (eq? (car p) symbol)))
