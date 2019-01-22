(define-module (sicp thunk)
  #:export (delay-it))

(use-modules (sicp utils))

(define* (delay-it exp env #:key (memo #t))
  (list 'thunk exp env memo))

(define-public (thunk? obj)
  (tagged-list? obj 'thunk))

(define-public (thunk-exp thunk)
  (cadr thunk))

(define-public (thunk-env thunk)
  (caddr thunk))

(define-public (thunk-memo thunk)
  (cadddr thunk))

(define-public (evaluated-thunk? obj)
  (tagged-list? obj 'evaluated-thunk))

(define-public (thunk-value evaluated-thunk)
  (cadr evaluated-thunk))
