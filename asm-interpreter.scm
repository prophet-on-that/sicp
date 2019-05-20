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
(define ret 0)                          ; Used for return value
(define rax 1)
(define rbx 2)
(define rcx 3)
(define rdx 4)
(define continue 4)

;;; Memory layout
(define the-cars-pointer 0)
(define the-cdrs-pointer 1)
(define free-pair-pointer 2)            ; Next unassigned index into the pairs arrays
(define the-cars-offset 8)

;;; Exit codes
;;; 1 - attempting to take CAR of a non-pair
;;; 2 - attempting to take CDR of a non-pair
;;; 3 - attempting to set the CAR of a non-pair

(define (init max-num-pairs)
  `((alias ,ret ret)
    (alias ,rax rax)
    (alias ,rbx rbx)
    (alias ,rcx rcx)
    (alias ,rdx rdx)

    ;; Initialise the-cars-pointer
    (mem-store (const ,the-cars-pointer) (const ,the-cars-offset))

    ;; Initialise the-cdrs pointer
    (assign (reg rax) (const ,(+ the-cars-offset max-num-pairs)))
    (mem-store (const ,the-cdrs-pointer) (reg rax))

    ;; Initialise free-pair-pointer
    (assign (reg rax) (const 0))
    (mem-store (const ,free-pair-pointer) (reg rax))))

(define (memory-management-defs max-num-pairs)
  `(
    ;; Args:
    ;; 0 - car of new pair
    ;; 1 - cdr of new pair
    ;; Returns: newly-assigned pair
    ;; TODO: trigger garbage collection when out of space
    cons
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (mem-load (reg rax) (const ,free-pair-pointer))
    (mem-load (reg rbx) (const ,the-cars-pointer))
    (assign (reg rbx) (op +) (reg rax) (reg rbx))
    (mem-load (reg rcx) (op +) (reg bp) (const 2)) ; arg 0
    (mem-store (reg rbx) (reg rcx))
    (mem-load (reg rbx) (const ,the-cdrs-pointer))
    (assign (reg rbx) (op +) (reg rax) (reg rbx))
    (mem-load (reg rcx) (op +) (reg bp) (const 3)) ; arg 1
    (mem-store (reg rbx) (reg rcx))
    (assign (reg rbx) (op +) (reg rax) (const 1)) ; new free pair pointer
    (mem-store (const ,free-pair-pointer) (reg rbx))
    (assign (reg ret) (op logior) (reg rax) (const ,pair-tag))
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - Object to test
    pair?
    (mem-load (reg ret) (op +) (reg bp) (const 2)) ; arg 0
    (assign (reg ret) (op logand) (reg ret) (const ,tag-mask))
    (test (op =) (reg ret) (const ,pair-tag))
    (ret)

    ;; Args:
    ;; 0 - Pair from which to retrieve car
    ;; Returns: car of pair
    ;; TODO: test for pair in Scheme CAR implementation, for
    ;; efficiency
    car
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (stack-push (reg rax))
    (call pair?)
    (jez (label car-invalid-arg))
    (stack-pop (reg rax))
    (assign (reg rax) (op logand) (reg rax) (const ,value-mask)) ; Offset into pair arrays
    (mem-load (reg rbx) (const ,the-cars-pointer))
    (assign (reg rax) (op +) (reg rax) (reg rbx))
    (mem-load (reg ret) (reg rax))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)
    car-invalid-arg
    (error (const 1))

    ;; Args:
    ;; 0 - Pair to modify
    ;; 1 - Value to set in CAR
    set-car!
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (stack-push (reg rax))
    (call pair?)
    (jez (label set-car!-invalid-arg))
    (stack-pop)
    (assign (reg rax) (op logand) (reg rax) (const ,value-mask)) ; Offset into pairs array
    (mem-load (reg rbx) (const ,the-cars-pointer))
    (assign (reg rax) (op +) (reg rax) (reg rbx)) ; Memory address of CAR of pair
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1
    (mem-store (reg rax) (reg rbx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)
    set-car!-invalid-arg
    (error (const 3))

    ;; Args:
    ;; 0 - Pair from which to retrieve cdr
    ;; Returns: cdr of pair
    ;; TODO: test for pair in Scheme CDR implementation, for
    ;; efficiency
    cdr
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (stack-push (reg rax))
    (call pair?)
    (jez (label cdr-invalid-arg))
    (stack-pop (reg rax))
    (assign (reg rax) (op logand) (reg rax) (const ,value-mask)) ; Offset into pair arrays
    (mem-load (reg rbx) (const ,the-cdrs-pointer))
    (assign (reg rax) (op +) (reg rax) (reg rbx))
    (mem-load (reg ret) (reg rax))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)
    cdr-invalid-arg
    (error (const 2))

    gc
    ;; Push all data registers to the stack, so that the stack holds
    ;; all pair references
    ,@(map
       (lambda (i)
         `(stack-push (reg ,i)))
       (range 0 max-num-pairs))

    ;; Restore pushed registers
    ,@(map
       (lambda (i)
         `(stack-pop (reg ,i)))
       (reverse (range 0 max-num-pairs)))
    (ret)))

;;; Utilities

(define (wrap-code max-num-pairs code)
  `(,@(init max-num-pairs)
    (goto (label start))
    ,@(memory-management-defs max-num-pairs)
    start
    ,@code))

(define (range min max)
  "Integer range between MIN (inclusive) and MAX (exclusive)."
  (if (>= min max)
      '()
      (cons min
            (range (1+ min) max))))

;;; Test suite

(define test-max-num-pairs 8)
(define test-num-registers 8)
(define test-stack-size 128)
(define test-memory-size (+ the-cars-offset
                            (* test-max-num-pairs 4)
                            test-stack-size))

(define (make-test-machine code)
  (make-machine-load-text
   test-num-registers
   test-memory-size
   (wrap-code test-max-num-pairs code)))

(test-begin "asm-interpreter-test")

;;; Test cons
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (call cons)
           (assign (reg sp) (op +) (reg sp) (const 2)))))
       (ret (get-machine-register machine ret))
       (memory (get-machine-memory machine)))
  (start-machine machine)
  (test-eqv (get-register-contents ret) (logior pair-tag 0))
  (test-eqv (get-memory memory free-pair-pointer) 1))

;;; Test pair?: true
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (assign (reg rax) (op logior) (const ,number-tag) (const 2))
           (stack-push (reg rax))
           (call cons)
           (assign (reg sp) (op +) (reg sp) (const 2))
           (stack-push (reg ret))
           (call pair?)
           (stack-pop))))
       (flag (get-machine-flag machine)))
  (start-machine machine)
  (test-eqv (get-register-contents flag) 1))

;;; Test pair?: false
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (call pair?)
           (stack-pop))))
       (flag (get-machine-flag machine)))
  (start-machine machine)
  (test-eqv (get-register-contents flag) 0))

;;; Test car: valid pair
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 2))
           (stack-push (reg rax))
           (assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (call cons)
           (assign (reg sp) (op +) (reg sp) (const 2))
           (stack-push (reg ret))
           (call car)
           (stack-pop))))
       (ret (get-machine-register machine ret)))
  (start-machine machine)
  (test-eqv (get-register-contents ret) (logior number-tag 1)))

;;; Test car: invalid pair
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (call car)
           (stack-pop)))))
  (test-error #t (start-machine machine)))

;;; Test cdr: valid pair
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 2))
           (stack-push (reg rax))
           (assign (reg rbx) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (call cons)
           (assign (reg sp) (op +) (reg sp) (const 2))
           (stack-push (reg ret))
           (call cdr)
           (stack-pop))))
       (ret (get-machine-register machine ret)))
  (start-machine machine)
  (test-eqv (get-register-contents ret) (logior number-tag 2)))

;;; Test cdr: invalid pair
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (call cdr)
           (stack-pop)))))
  (test-error #t (start-machine machine)))

;;; Test set-car!: valid pair
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 2))
           (stack-push (reg rax))
           (assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (call cons)
           (assign (reg sp) (op +) (reg sp) (const 2))
           (assign (reg rax) (reg ret))
           (assign (reg rbx) (op logior) (const ,number-tag) (const 3))
           (stack-push (reg rbx))
           (stack-push (reg rax))
           (call set-car!)
           (assign (reg sp) (op +) (reg sp) (const 2))
           (stack-push (reg rax))
           (call car)
           (stack-pop))))
       (ret (get-machine-register machine ret)))
  (start-machine machine)
  (test-eqv (get-register-contents ret) (logior number-tag 3)))

;;; Test set-car!: invalid pair
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (stack-push (reg rax))
           (call set-car!)
           (assign (reg sp) (op +) (reg sp) (const 2))))))
  (test-error #t (start-machine machine)))

(test-end "asm-interpreter-test")
