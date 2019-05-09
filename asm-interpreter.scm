(define-module (sicp asm-interpreter))

(use-modules (sicp virt-machine)
             (srfi srfi-64))

;;; Architecture: 32-bit
;;; Typed pointer tag: 4 bits for typed pointer information stored in
;;; highest bits.
(define tag-mask #xf0000000)
(define value-mask #x0fffffff)
(define pair-tag #x10000000)
(define number-tag #x20000000)

;;; Register aliases
;;; 0 - the-cars
;;; 1 - the-cdrs
;;; 2 - free: current unassigned index into the-cars and the-cdrs
;;; 3 - rax: general-purpose
;;; 4 - rbx: general-purpose
;;; 5 - rcx: general-purpose
;;; 6 - continue

;;; Memory layout:
;;; 0 - max-num-pairs - 1: the-cars
;;; max-num-pairs - 2 * max-num-pairs - 1: the-cdrs

;;; Exit codes
;;; 1 - attempting to take CAR of a non-pair

(define (init max-num-pairs)
  `((alias 0 the-cars)
    (alias 1 the-cdrs)
    (alias 2 next-free-pair)
    (alias 3 rax)
    (alias 4 rbx)
    (alias 5 rcx)
    (alias 6 continue)

    (assign (reg the-cars) (const 0))
    (assign (reg the-cdrs) (const ,max-num-pairs))
    (assign (reg next-free-pair) (const 0))))

(define (memory-management-defs max-num-pairs)
  `(cons
    ;; Inputs:
    ;; rax - car of new pair
    ;; rbx - cdr of new pair
    ;; Uses:
    ;; rax
    ;; rcx
    ;; Outputs:
    ;; rax - newly-assigned pair
    (assign (reg rcx) (op +) (reg the-cars) (reg next-free-pair)) ; Offset into the-cars
    (mem-store (reg rcx) (reg rax))
    (assign (reg rcx) (op +) (reg the-cdrs) (reg next-free-pair)) ; Offset into the-cdrs
    (mem-store (reg rcx) (reg rbx))
    (assign (reg rax) (op logior) (reg next-free-pair) (const ,pair-tag))
    (assign (reg next-free-pair) (op +) (reg next-free-pair) (const 1)) ; TODO: check bounds and trigger garbage collection
    (goto (reg continue))

    pair?
    ;; Inputs:
    ;; rax - Object to test
    ;; Uses:
    ;; rax
    ;; Outputs:
    ;; test
    (assign (reg rax) (op logand) (reg rax) (const ,tag-mask))
    (test (op =) (reg rax) (const ,pair-tag))
    (goto (reg continue))

    car
    ;; Inputs:
    ;; rax - pair
    ;; Uses:
    ;; rax
    ;; rbx
    ;; Outputs:
    ;; rax - car of pair
    (stack-push (reg continue))
    (stack-push (reg rax))
    (assign (reg continue) (label car-after-pair?))
    (goto (label pair?))
    car-after-pair?
    (jez (label car-invalid-arg))
    (stack-pop (reg rax))
    (stack-pop (reg continue))
    (assign (reg rbx) (op logand) (reg rax) (const ,value-mask)) ; Fetch offset into the-cars and the-cdrs
    (assign (reg rbx) (op +) (reg rbx) (reg the-cars))
    (mem-load (reg rax) (reg rbx))
    (goto (reg continue))
    car-invalid-arg
    (error (const 1))))

;;; Test suite

(test-begin "asm-interpreter-test")

;;; Test cons
(let* ((max-num-pairs 4)
       (code `(,@(init max-num-pairs)
               (goto (label start))
               ,@(memory-management-defs max-num-pairs)
               start
               (assign (reg rax) (op logior) (const ,number-tag) (const 1))
               (assign (reg rbx) (op logior) (const ,number-tag) (const 2))
               (assign (reg continue) (label after-cons))
               (goto (label cons))
               after-cons))
      (machine (make-machine-load-text 8 8 code))
      (reg3 (get-machine-register machine 3))
      (reg-free (get-machine-register machine 2))
      (memory (get-machine-memory machine)))
  (start-machine machine)
  (test-eqv (get-register-contents reg3) (logior pair-tag 0))
  (test-eqv (get-register-contents reg-free) 1))

;;; Test pair?: true
(let* ((max-num-pairs 4)
       (code `(,@(init max-num-pairs)
               (goto (label start))
               ,@(memory-management-defs max-num-pairs)
               start
               (assign (reg rax) (op logior) (const ,number-tag) (const 1))
               (assign (reg rbx) (op logior) (const ,number-tag) (const 2))
               (assign (reg continue) (label after-cons))
               (goto (label cons))
               after-cons
               (assign (reg continue) (label after-pair?))
               (goto (label pair?))
               after-pair?))
      (machine (make-machine-load-text 8 8 code))
      (flag (get-machine-flag machine)))
  (start-machine machine)
  (test-eqv (get-register-contents flag) 1))

;;; Test pair?: false
(let* ((max-num-pairs 4)
       (code `(,@(init max-num-pairs)
               (goto (label start))
               ,@(memory-management-defs max-num-pairs)
               start
               (assign (reg rax) (op logior) (const ,number-tag) (const 1))
               (assign (reg continue) (label after-pair?))
               (goto (label pair?))
               after-pair?))
      (machine (make-machine-load-text 8 8 code))
      (flag (get-machine-flag machine)))
  (start-machine machine)
  (test-eqv (get-register-contents flag) 0))

;;; Test car: valid pair
(let* ((max-num-pairs 4)
       (code `(,@(init max-num-pairs)
               (goto (label start))
               ,@(memory-management-defs max-num-pairs)
               start
               (assign (reg rax) (op logior) (const ,number-tag) (const 1))
               (assign (reg rbx) (op logior) (const ,number-tag) (const 2))
               (assign (reg continue) (label after-cons))
               (goto (label cons))
               after-cons
               (assign (reg continue) (label after-car))
               (goto (label car))
               after-car))
      (machine (make-machine-load-text 8 8 code))
      (rax (get-machine-register machine 3)))
  (start-machine machine)
  (test-eqv (get-register-contents rax) (logior number-tag 1)))

;;; Test car: invalid pair
(let* ((max-num-pairs 4)
       (code `(,@(init max-num-pairs)
               (goto (label start))
               ,@(memory-management-defs max-num-pairs)
               start
               (assign (reg rax) (op logior) (const ,number-tag) (const 1))
               (assign (reg continue) (label after-car))
               (goto (label car))
               after-car))
      (machine (make-machine-load-text 8 8 code))
      (rax (get-machine-register machine 3)))
  (test-error #t (start-machine machine)))

(test-end "asm-interpreter-test")
