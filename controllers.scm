(define-module (sicp controllers))

(use-modules (sicp reg-machine)
             (srfi srfi-64))

;;; GCD

(define gcd-machine
  (make-machine
   '(a b t)
   (list (list 'rem remainder)
         (list '= =))
   '(test-b
     (test (op =) (reg b) (const 0))
     (branch (label gcd-done))
     (assign t (op rem) (reg a) (reg b))
     (assign a (reg b))
     (assign b (reg t))
     (goto (label test-b))
     gcd-done)))

;;; Factorial

(define factorial-machine
  (make-machine
   '(n val continue)
   (list (list '- -)
         (list '= =)
         (list '* *))
   '((assign continue (label fact-done))
     fact-loop
     (test (op =) (reg n) (const 1))
     (branch (label base-case))
     (save continue)
     (save n)
     (assign n (op -) (reg n) (const 1))
     (assign continue (label after-fact))
     (goto (label fact-loop))
     after-fact
     (restore n)
     (restore continue)
     (assign val (op *) (reg n) (reg val))
     (goto (reg continue))
     base-case
     (assign val (const 1))
     (goto (reg continue))
     fact-done)))

;;; Test suite

(test-begin "reg-machine-test")

(set-register-contents! gcd-machine 'a 30)
(set-register-contents! gcd-machine 'b 45)
(start gcd-machine)
(test-eqv
    "GCD machine operates correctly"
  (get-register-contents gcd-machine 'a)
  15)

(set-register-contents! factorial-machine 'n 5)
(start factorial-machine)
(test-eqv
    "Factorial machine operates correctly"
  (get-register-contents factorial-machine 'val)
  120)

(test-error
 "Throw error on duplicate labels"
 (make-machine
  '(a)
  '()
  '(start
    (goto (label here))
    here
    (assign a (const 3))
    (goto (label there))
    here
    (assign a (const 4))
    (goto (label there))
    there)))

(test-error
 "Throw error when label passed to operation expression"
 (make-machine
  '(a)
  (list (list '+ +))
  '(start
    (assign a (op +) (label start) (const 1)))))

(test-end "reg-machine-test")
