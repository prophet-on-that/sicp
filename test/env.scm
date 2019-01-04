(use-modules (srfi srfi-64)
             (sicp ch4 env))

(test-begin "env-test")

(test-error
 "Look up value in empty env"
 (lookup-variable-value 'a the-empty-environment))

(let ((env (extend-environment (list 'a 'b)
                               (list 1 2)
                               the-empty-environment)))
  (test-eqv "Look up first value in env" 1 (lookup-variable-value 'a env))
  (test-eqv "Look up second value in env" 2 (lookup-variable-value 'b env))
  (test-error "Look up unbound value in one-tier env" (lookup-variable-value 'c env)))

(let ((env (extend-environment (list 'a 'c)
                               (list 3 4)
                               (extend-environment (list 'a 'b)
                                                   (list 1 2)
                                                   the-empty-environment))))
  (test-eqv "Look up shadowing value in two-tier env" 3 (lookup-variable-value 'a env))
  (test-eqv "Look up value in two-tier env" 4 (lookup-variable-value 'c env))
  (test-eqv "Look up outer scope value in two-tier env" 2 (lookup-variable-value 'b env)))

(let ((env (extend-environment '() '() the-empty-environment)))
  (define-variable! 'a 1 env)
  (test-eqv "Look up defined variable" 1 (lookup-variable-value 'a env))
  (set-variable-value! 'a 2 env)
  (test-eqv "Look up set variable" 2 (lookup-variable-value 'a env))
  (test-error "Set undefined variable" (set-variable-value! 'b 3 env)))

(test-end "env-test")
