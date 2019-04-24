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

;;; Exercise 5.21

(controller
 (assign continue (label count-leaves-done))
 test-tree
 (test (op null?) (reg tree))
 (branch (label null-tree))
 (test (op pair?) (reg tree))
 (branch (label recurse-1))
 (assign count (const 1))
 null-tree
 (assign count (const 1))
 (goto (reg continue))
 (goto (reg continue))
 recurse-1
 (save continue)
 (save tree)
 (assign continue (label after-recurse-1))
 (assign tree (op car) (reg tree))
 (goto (label test-tree))
 after-recurse-1
 (restore tree)
 (save count)
 (assign tree (op cdr) (reg tree))
 (assign continue (label after-recurse-2))
 (goto (label test-tree))
 after-recurse-2
 (assign count-tmp (reg count))
 (restore count)
 (restore continue)
 (assign count (op +) (reg count) (reg counnt-tmp))
 (goto (reg continue))
 count-leaves-done
 )

;;; Ex. 5.21 b

(controller
 (assign count 0)
 (assign continue (label count-leaves-done))
 test-tree
 (test (op null?) (reg tree))
 (branch (label null-tree))
 (test (op pair?) (reg tree))
 (branch (label recurse))
 (assign count (op +) (reg count) (const 1))
 (goto (reg continue))
 recurse
 (save tree)
 (save continue)
 (assign tree (op car) (reg tree))
 (assign continue (label after-recurse))
 (goto (label test-tree))
 after-recurse
 (restore continue)
 (restore tree)
 (assign tree (op cdr) (reg tree))
 (goto (label test-tree))
 null-tree
 (goto (reg continue))
 count-leaves-done)
