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
(define rax 0)
(define rbx 1)
(define rcx 2)
(define rdx 3)
(define continue 4)

;;; Memory layout
(define the-cars-pointer 0)
(define the-cdrs-pointer 1)
(define free-pair-pointer 2)            ; Next unassigned index into the pairs arrays
(define the-cars-offset 8)

;;; Exit codes
;;; 1 - attempting to take CAR of a non-pair

(define (init max-num-pairs)
  `((alias ,rax rax)
    (alias ,rbx rbx)
    (alias ,rcx rcx)
    (alias ,rdx rdx)
    (alias ,continue continue)

    ;; Initialise the-cars-pointer
    (assign (reg rax) (const ,the-cars-offset))
    (mem-store (const ,the-cars-pointer) (reg rax))

    ;; Initialise the-cdrs pointer
    (assign (reg rax) (const ,(+ the-cars-offset max-num-pairs)))
    (mem-store (const ,the-cdrs-pointer) (reg rax))

    ;; Initialise free-pair-pointer
    (assign (reg rax) (const 0))
    (mem-store (const ,free-pair-pointer) (reg rax))))

(define (memory-management-defs max-num-pairs)
  `(cons
    ;; Inputs:
    ;; rax - car of new pair
    ;; rbx - cdr of new pair
    ;; Uses:
    ;; rax
    ;; rcx
    ;; rdx
    ;; Outputs:
    ;; rax - newly-assigned pair
    ;; TODO: trigger garbage collection when out of space
    (mem-load (reg rcx) (const ,free-pair-pointer))
    (mem-load (reg rdx) (const ,the-cars-pointer))
    (assign (reg rdx) (op +) (reg rdx) (reg rcx))
    (mem-store (reg rdx) (reg rax))
    (mem-load (reg rdx) (const ,the-cdrs-pointer))
    (assign (reg rdx) (op +) (reg rdx) (reg rcx))
    (mem-store (reg rdx) (reg rbx))
    (assign (reg rax) (op logior) (reg rcx) (const ,pair-tag))
    (assign (reg rcx) (op +) (reg rcx) (const 1))
    (mem-store (const ,free-pair-pointer) (reg rcx))
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
    ;; TODO: test for this in Scheme CAR implementation
    (stack-push (reg continue))
    (stack-push (reg rax))
    (assign (reg continue) (label car-after-pair?))
    (goto (label pair?))
    car-after-pair?
    (jez (label car-invalid-arg))
    (stack-pop (reg rax))
    (stack-pop (reg continue))
    (assign (reg rax) (op logand) (reg rax) (const ,value-mask)) ; Offset into the-cars and the-cdrs
    (mem-load (reg rbx) (const ,the-cars-pointer))
    (assign (reg rax) (op +) (reg rax) (reg rbx))
    (mem-load (reg rax) (reg rax))
    (goto (reg continue))
    car-invalid-arg
    (error (const 1))))

;;; Utilities

(define (wrap-code max-num-pairs code)
  `(,@(init max-num-pairs)
    (goto (label start))
    ,@(memory-management-defs max-num-pairs)
    start
    ,@code))

;;; Test suite

(define test-max-num-pairs 8)
(define test-num-registers 8)
(define test-memory-size (+ the-cars-offset
                            (* test-max-num-pairs 4)))

(test-begin "asm-interpreter-test")

;;; Test cons
(let* ((code
        (wrap-code
         test-max-num-pairs
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (assign (reg rbx) (op logior) (const ,number-tag) (const 2))
           (assign (reg continue) (label after-cons))
           (goto (label cons))
           after-cons)))
       (machine (make-machine-load-text test-num-registers test-memory-size code))
       (rax (get-machine-register machine rax))
       (memory (get-machine-memory machine)))
  (start-machine machine)
  (test-eqv (get-register-contents rax) (logior pair-tag 0))
  (test-eqv (get-memory memory free-pair-pointer) 1))

;;; Test pair?: true
(let* ((code
        (wrap-code
         test-max-num-pairs
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (assign (reg rbx) (op logior) (const ,number-tag) (const 2))
           (assign (reg continue) (label after-cons))
           (goto (label cons))
           after-cons
           (assign (reg continue) (label after-pair?))
           (goto (label pair?))
           after-pair?)))
       (machine (make-machine-load-text test-num-registers test-memory-size code))
       (flag (get-machine-flag machine)))
  (start-machine machine)
  (test-eqv (get-register-contents flag) 1))

;;; Test pair?: false
(let* ((code
        (wrap-code
         test-max-num-pairs
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (assign (reg continue) (label after-pair?))
           (goto (label pair?))
           after-pair?)))
       (machine (make-machine-load-text test-num-registers test-memory-size code))
       (flag (get-machine-flag machine)))
  (start-machine machine)
  (test-eqv (get-register-contents flag) 0))

;;; Test car: valid pair
(let* ((code
        (wrap-code
         test-max-num-pairs
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (assign (reg rbx) (op logior) (const ,number-tag) (const 2))
           (assign (reg continue) (label after-cons))
           (goto (label cons))
           after-cons
           (assign (reg continue) (label after-car))
           (goto (label car))
           after-car)))
       (machine (make-machine-load-text test-num-registers test-memory-size code))
       (rax (get-machine-register machine rax)))
  (start-machine machine)
  (test-eqv (get-register-contents rax) (logior number-tag 1)))

;;; Test car: invalid pair
(let* ((code
        (wrap-code
         test-max-num-pairs
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (assign (reg continue) (label after-car))
           (goto (label car))
           after-car)))
       (machine (make-machine-load-text test-num-registers test-memory-size code)))
  (test-error #t (start-machine machine)))

(test-end "asm-interpreter-test")
