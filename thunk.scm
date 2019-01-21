(define-module (sicp thunk))

(use-modules (sicp utils))

(define-public (delay-it exp env)
  (list 'thunk exp env))

(define-public (thunk? obj)
  (tagged-list? obj 'thunk))

(define-public (thunk-exp thunk)
  (cadr thunk))

(define-public (thunk-env thunk)
  (caddr thunk))

(define-public (evaluated-thunk? obj)
  (tagged-list? obj 'evaluated-thunk))

(define-public (thunk-value evaluated-thunk)
  (cadr evaluated-thunk))
