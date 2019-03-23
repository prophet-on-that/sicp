;;; Exercise 5.2
(controller
 (assign product (const 1))
 (assign counter (const 1))
 test-counter
 (test (op >) (reg counter) (reg n))
 (branch (label factorial-done))
 (assign product (op *) (reg counter) (reg product))
 (assign counter (op +) (reg counter) (const 1))
 (goto test-counter)
 factorial-done)

;;; Exercise 5.3
(controller
 (assign g (const 1.0))
 test-g
 (assign g_squared (op *) (reg g) (reg g))
 (assign diff (op -) (reg g_squared) (reg x))
 (test (op >) (reg diff) (const 0))
 (branch (label post-abs))
 (assign diff (op *) (reg diff) (const -1))
 post-abs
 (test (op <) (reg diff) (const 0.001))
 (branch (label end-newton))
 (assign frac (op /) (reg x) (reg g))
 (assign sum (op +) (reg frac) (reg g))
 (assign g (op /) (reg sum) (const 2))
 (goto (label test-g))
 end-newton)

;;; Exercise 5.4

(controller
 (assign continue (label expt-done))
 expt-loop
 (test (op =) (reg n) (const 0))
 (branch (label base-case))
 (save continue)
 (assign n (op -) (reg n) (const 1))
 (assign continue (label after-expt))
 (goto (label expt-loop))
 after-expt
 (restore continue)
 (assign val (op *) (reg val) (reg b))
 (goto (reg continue))
 base-case
 (assign val (const 1))
 (goto (reg continue))
 expt-done)

(controller
 (assign counter (reg n))
 (assign product (const 1))
 test-counter
 (test (op =) (reg counter) (const 0))
 (branch (label expt-done))
 (assign counter (op -) (reg counter) (const 1))
 (assign product (op *) (reg product) (reg b))
 (goto (label test-counter))
 expt-done)

