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
(define rax 0)                          ; Used for return value
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
;;; 2 - attempting to take CDR of a non-pair

(define (init max-num-pairs)
  `((alias ,rax rax)
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
    (assign (reg rax) (op logior) (reg rax) (const ,pair-tag))
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (ret)

    ;; Args:
    ;; 0 - Object to test
    pair?
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; arg 0
    (assign (reg rax) (op logand) (reg rax) (const ,tag-mask))
    (test (op =) (reg rax) (const ,pair-tag))
    (ret)

    ;; Args:
    ;; 0 - Pair from which to retrieve car
    ;; Returns: car of pair
    ;; TODO: test for pair in Scheme CAR implementation, for
    ;; efficiency
    car
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (stack-push (reg rax))
    (call pair?)
    (jez (label car-invalid-arg))
    (stack-pop (reg rax))
    (assign (reg rax) (op logand) (reg rax) (const ,value-mask)) ; Offset into pair arrays
    (stack-push (reg rbx))
    (mem-load (reg rbx) (const ,the-cars-pointer))
    (assign (reg rax) (op +) (reg rax) (reg rbx))
    (mem-load (reg rax) (reg rax))
    (stack-pop (reg rbx))
    (ret)
    car-invalid-arg
    (error (const 1))

    ;; Args:
    ;; 0 - Pair from which to retrieve cdr
    ;; Returns: cdr of pair
    ;; TODO: test for pair in Scheme CDR implementation, for
    ;; efficiency
    cdr
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (stack-push (reg rax))
    (call pair?)
    (jez (label cdr-invalid-arg))
    (stack-pop (reg rax))
    (assign (reg rax) (op logand) (reg rax) (const ,value-mask)) ; Offset into pair arrays
    (stack-push (reg rbx))
    (mem-load (reg rbx) (const ,the-cdrs-pointer))
    (assign (reg rax) (op +) (reg rax) (reg rbx))
    (mem-load (reg rax) (reg rax))
    (stack-pop (reg rbx))
    (ret)
    cdr-invalid-arg
    (error (const 2))
    ))

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
           (call cons))))
       (rax (get-machine-register machine rax))
       (memory (get-machine-memory machine)))
  (start-machine machine)
  (test-eqv (get-register-contents rax) (logior pair-tag 0))
  (test-eqv (get-memory memory free-pair-pointer) 1))

;;; Test pair?: true
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (assign (reg rax) (op logior) (const ,number-tag) (const 2))
           (stack-push (reg rax))
           (call cons)
           (stack-push (reg rax))
           (call pair?))))
       (flag (get-machine-flag machine)))
  (start-machine machine)
  (test-eqv (get-register-contents flag) 1))

;;; Test pair?: false
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (call pair?))))
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
           (stack-push (reg rax))
           (call car))))
       (rax (get-machine-register machine rax)))
  (start-machine machine)
  (test-eqv (get-register-contents rax) (logior number-tag 1)))

;;; Test car: invalid pair
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (call car)))))
  (test-error #t (start-machine machine)))

;;; Test cdr: valid pair
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 2))
           (stack-push (reg rax))
           (assign (reg rbx) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (call cons)
           (stack-push (reg rax))
           (call cdr))))
       (rax (get-machine-register machine rax)))
  (start-machine machine)
  (test-eqv (get-register-contents rax) (logior number-tag 2)))

;;; Test cdr: invalid pair
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (call cdr)))))
  (test-error #t (start-machine machine)))

(test-end "asm-interpreter-test")
