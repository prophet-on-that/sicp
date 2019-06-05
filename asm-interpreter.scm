(define-module (sicp asm-interpreter))

(use-modules (sicp virt-machine)
             (srfi srfi-64)
             (srfi srfi-1))

;;; Architecture: 32-bit
;;; Typed pointer tag: 4 bits for typed pointer information stored in
;;; highest bits.
(define tag-mask #xf0000000)
(define value-mask #x0fffffff)
(define pair-tag #x10000000)
(define number-tag #x20000000)
(define broken-heart #x30000000)
(define empty-list #x40000000)

;;; Register aliases
(define ret 0)                          ; Used for return value
(define rax 1)
(define rbx 2)
(define rcx 3)
(define rdx 4)

;;; Memory layout
(define the-cars-pointer 0)
(define the-cdrs-pointer 1)
(define free-pair-pointer 2)            ; Next unassigned index into the pairs arrays
(define new-cars-pointer 3)
(define new-cdrs-pointer 4)
(define read-buffer-pointer 5)
(define the-cars-offset 8)

;;; Exit codes
;;; 1 - attempting to take CAR of a non-pair
;;; 2 - attempting to take CDR of a non-pair
;;; 3 - attempting to set the CAR of a non-pair
;;; 4 - attempting to set the CAR of a non-pair
;;; 5 - no space for a new pair
(define error-read-list-bad-start-char 8)
(define error-read-unterminated-input 9)
(define error-read-unknown-char 10)

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
    (mem-store (const ,free-pair-pointer) (reg rax))

    ;; Initialise new-cars-pointer
    (assign (reg rax) (const ,(+ the-cars-offset (* 2 max-num-pairs))))
    (mem-store (const ,new-cars-pointer) (reg rax))

    ;; Initialise new-cdrs-pointer
    (assign (reg rax) (const ,(+ the-cars-offset (* 3 max-num-pairs))))
    (mem-store (const ,new-cdrs-pointer) (reg rax))

    ;; Initialise read-buffer-pointer
    (assign (reg rax) (const ,(+ the-cars-offset (* 4 max-num-pairs))))
    (mem-store (const ,read-buffer-pointer) (reg rax))))

(define (memory-management-defs num-registers max-num-pairs memory-size)
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
    ;; Trigger garbage collection when no pairs are available
    (mem-load (reg rax) (const ,free-pair-pointer))
    (test (op >=) (reg rax) (const ,max-num-pairs))
    (jez (label cons-after-gc))
    (call gc)
    ;; Throw error if no space exists after garbage collection
    (mem-load (reg rax) (const ,free-pair-pointer))
    (test (op >=) (reg rax) (const ,max-num-pairs))
    (jez (label cons-after-gc))
    (error (const 5))

    cons-after-gc
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

    ;; Args:
    ;; 0 - Pair to modify
    ;; 1 - Value to set in CDR
    set-cdr!
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (stack-push (reg rax))
    (call pair?)
    (jez (label set-cdr!-invalid-arg))
    (stack-pop)
    (assign (reg rax) (op logand) (reg rax) (const ,value-mask)) ; Offset into pairs array
    (mem-load (reg rbx) (const ,the-cdrs-pointer))
    (assign (reg rax) (op +) (reg rax) (reg rbx)) ; Memory address of CDR of pair
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1
    (mem-store (reg rax) (reg rbx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)
    set-cdr!-invalid-arg
    (error (const 3))

    ;; Args:
    ;; 0 - pair from which to extract the cadr
    ;; Output: cadr of pair
    cadr
    (mem-load (reg ret) (op +) (reg bp) (const 2)) ; Arg 0 - pair
    ,@(call 'cdr 'ret)
    ,@(call 'car 'ret)
    (ret)

    ;; Args:
    ;; 0 - pair from which to extract the cddr
    ;; Output: cddr of pair
    cddr
    (mem-load (reg ret) (op +) (reg bp) (const 2)) ; Arg 0 - pair
    ,@(call 'cdr 'ret)
    ,@(call 'cdr 'ret)
    (ret)

    ;; Args:
    ;; 0 - pair from which to extract the caar
    ;; Output: caar of pair
    caar
    (mem-load (reg ret) (op +) (reg bp) (const 2)) ; Arg 0 - pair
    ,@(call 'car 'ret)
    ,@(call 'car 'ret)
    (ret)

    gc
    ;; Push all data registers to the stack, so that the stack holds
    ;; all pair references
    ,@(map
       (lambda (i)
         `(stack-push (reg ,i)))
       (range 0 num-registers))
    (mem-store (const ,free-pair-pointer) (const 0))
    ;; Relocate all pairs on stack
    (assign (reg rax) (reg sp))         ; Stack index pointer

    gc-stack-relocate
    (test (op <) (reg rax) (const ,memory-size))
    (jez (label gc-after-stack-relocate))
    (stack-push (reg rax))
    (call gc-relocate-pair)
    (stack-pop)
    (assign (reg rax) (op +) (reg rax) (const 1))
    (goto (label gc-stack-relocate))

    gc-after-stack-relocate
    (assign (reg rax) (const 0))        ; Scan pointer

    gc-scan
    (mem-load (reg rbx) (const ,free-pair-pointer))
    (test (op <) (reg rax) (reg rbx))
    (jez (label gc-after-scan))
    ;; Relocate CAR of current pair
    (mem-load (reg rcx) (const ,new-cars-pointer))
    (assign (reg rcx) (op +) (reg rcx) (reg rax))
    ,@(call 'gc-relocate-pair 'rcx)
    ;; Relocate CDR of current pair
    (mem-load (reg rcx) (const ,new-cdrs-pointer))
    (assign (reg rcx) (op +) (reg rcx) (reg rax))
    ,@(call 'gc-relocate-pair 'rcx)
    ;; Increment scan pointer
    (assign (reg rax) (op +) (reg rax) (const 1))
    (goto (label gc-scan))

    gc-after-scan
    ;; Swap the-cars with new-cars
    (mem-load (reg rax) (const ,the-cars-pointer))
    (mem-load (reg rbx) (const ,new-cars-pointer))
    (mem-store (const ,the-cars-pointer) (reg rbx))
    (mem-store (const ,new-cars-pointer) (reg rax))
    ;; Swap the-cdrs with new-cdrs
    (mem-load (reg rax) (const ,the-cdrs-pointer))
    (mem-load (reg rbx) (const ,new-cdrs-pointer))
    (mem-store (const ,the-cdrs-pointer) (reg rbx))
    (mem-store (const ,new-cdrs-pointer) (reg rax))
    ;; Restore pushed registers
    ,@(map
       (lambda (i)
         `(stack-pop (reg ,i)))
       (reverse (range 0 num-registers)))
    (ret)

    ;; Args:
    ;; 0 - memory location of object to relocate
    ;; TODO: not all registers are used by all branches - optimise this.
    ;; TODO: some pushes and pops of function arguments are unnecessary
    gc-relocate-pair
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (stack-push (reg rdx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (mem-load (reg rbx) (reg rax))   ; Candidate object for relocation
    (stack-push (reg rbx))
    (call pair?)
    (stack-pop)
    (jez (label gc-relocate-pair-end))
    (stack-push (reg rbx))
    (call car)
    (stack-pop)
    (test (op =) (reg ret) (const ,broken-heart))
    (jne (label gc-relocate-pair-already-moved))
    ;; Relocate CAR of old pair to new memory
    (mem-load (reg rcx) (const ,new-cars-pointer))
    (mem-load (reg rdx) (const ,free-pair-pointer))
    (assign (reg rcx) (op +) (reg rcx) (reg rdx)) ; Offset into new-cars
    (mem-store (reg rcx) (reg ret))
    ;; Relocate CDR of old pair to new memory
    (stack-push (reg rbx))
    (call cdr)
    (stack-pop)
    (mem-load (reg rcx) (const ,new-cdrs-pointer))
    (assign (reg rcx) (op +) (reg rcx) (reg rdx)) ; Offset into new-cdrs
    (mem-store (reg rcx) (reg ret))
    ;; Set CAR of old pair to broken heart
    (stack-push (const ,broken-heart))
    (stack-push (reg rbx))
    (call set-car!)
    (assign (reg sp) (op +) (reg sp) (const 2))
    ;; Set CDR of old pair to FREE-PAIR-POINTER
    (stack-push (reg rdx))
    (stack-push (reg rbx))
    (call set-cdr!)
    (assign (reg sp) (op +) (reg sp) (const 2))
    ;; Set memory location to point to new pair
    (assign (reg rcx) (op logior) (const ,pair-tag) (reg rdx))
    (mem-store (reg rax) (reg rcx))
    ;; Increment FREE-PAIR-POINTER
    (assign (reg rdx) (op +) (reg rdx) (const 1))
    (mem-store (const ,free-pair-pointer) (reg rdx))
    (goto (label gc-relocate-pair-end))

    gc-relocate-pair-already-moved
    ;; Point location to CDR of already-moved pair
    (stack-push (reg rbx))
    (call cdr)
    (stack-pop)
    (assign (reg rbx) (op logior) (reg ret) (const ,pair-tag))
    (mem-store (reg rax) (reg rbx))

    gc-relocate-pair-end
    (stack-pop (reg rdx))
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - Object
    ;; 1 - Object
    eq?
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1
    (test (op =) (reg rax) (reg rbx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - Object
    ;; 1 - Object
    equal?
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (stack-push (reg rdx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1

    equal?-entry
    ,@(call 'pair? 'rax)
    (jne (label equal?-first-pair))
    (goto (label equal?-test-eq?))

    equal?-first-pair
    ,@(call 'pair? 'rbx)
    (jne (label equal?-second-pair))
    (goto (label equal?-test-eq?))

    ;; Recursively test both cars and cdrs
    equal?-second-pair
    ,@(call 'car 'rax)
    (assign (reg rcx) (reg ret))
    ,@(call 'car 'rbx)
    (assign (reg rdx) (reg ret))
    ,@(call 'equal? 'rcx 'rdx)
    (jez (label equal?-end))
    ,@(call 'cdr 'rax)
    (assign (reg rax) (reg ret))
    ,@(call 'cdr 'rbx)
    (assign (reg rbx) (reg ret))
    (goto (label equal?-entry))         ; TCO

    equal?-test-eq?
    ,@(call 'eq? 'rax 'rbx)

    equal?-end
    (stack-pop (reg rdx))
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - ASCII character to test
    numeric-char?
    (stack-push (reg rax))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (test (op >=) (reg rax) (const ,(char->integer #\0)))
    (jez (label numeric-char?-end))
    (test (op <=) (reg rax) (const ,(char->integer #\9)))

    numeric-char?-end
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - ASCII character to test
    whitespace-char?
    (stack-push (reg rax))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (test (op =) (reg rax) (const ,(char->integer #\ )))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - ASCII character to test
    list-start-char?
    (stack-push (reg rax))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (test (op =) (reg rax) (const ,(char->integer #\()))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - ASCII character to test
    list-end-char?
    (stack-push (reg rax))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (test (op =) (reg rax) (const ,(char->integer #\))))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - memory address from which to start parsing
    ;; 1 - first memory address after the buffer
    ;; Output: pair containing the parsed integer and the address
    ;; after the last character parsed
    parse-int
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (stack-push (reg rdx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0 - buffer location
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1
    (assign (reg rcx) (const 0))        ; Parsed number
    parse-int-test
    (test (op <) (reg rax) (reg rbx))
    (jez (label parse-int-end))
    (mem-load (reg rdx) (reg rax))      ; Current char
    ,@(call 'numeric-char? 'rdx)
    (jez (label parse-int-end))
    (assign (reg rdx) (op -) (reg rdx) (const ,(char->integer #\0)))
    (assign (reg rcx) (op *) (reg rcx) (const 10))
    (assign (reg rcx) (op +) (reg rcx) (reg rdx))
    (assign (reg rax) (op +) (reg rax) (const 1))
    (goto (label parse-int-test))

    parse-int-end
    (assign (reg rcx) (op logior) (reg rcx) (const ,number-tag))
    ,@(call 'cons 'rcx 'rax)
    (stack-pop (reg rdx))
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)
    ;; Args:
    ;; 0 - memory address from which to start parsing
    ;; 1 - first memory address after the buffer
    ;; Output: pair containing the parsed list and the address
    ;; after the last character parsed
    parse-list-remainder
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (stack-push (reg rdx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0 - buffer location
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1

    parse-list-remainder-test
    (test (op <) (reg rax) (reg rbx))
    (jez (label read-unterminated-input))
    (mem-load (reg rcx) (reg rax))      ; Current char
    ,@(call 'whitespace-char? 'rcx)
    (jne (label parse-list-remainder-whitespace))
    ,@(call 'list-end-char? 'rcx)
    (jne (label parse-list-remainder-empty-list))
    ,@(call 'numeric-char? 'rcx)
    (jne (label parse-list-remainder-int))
    ,@(call 'list-start-char? 'rcx)
    (jne (label parse-list-remainder-list))
    (goto (label read-unknown-char))

    parse-list-remainder-whitespace
    (assign (reg rax) (op +) (reg rax) (const 1))
    (goto (label parse-list-remainder-test))

    parse-list-remainder-empty-list
    (assign (reg rcx) (const ,empty-list))
    (assign (reg rax) (op +) (reg rax) (const 1))
    ,@(call 'cons 'rcx 'rax)
    (goto (label parse-list-remainder-end))

    parse-list-remainder-int
    ,@(call 'parse-int 'rax 'rbx)
    (goto (label parse-list-remainder-continue))

    parse-list-remainder-list
    ,@(call 'parse-list 'rax 'rbx)
    (goto (label parse-list-remainder-continue))

    parse-list-remainder-continue
    (assign (reg rcx) (reg ret))
    ,@(call 'cdr 'rcx)
    (assign (reg rdx) (reg ret))
    ,@(call 'parse-list-remainder 'rdx 'rbx)
    (assign (reg rax) (reg ret))
    ,@(call 'cdr 'rax)
    (assign (reg rbx) (reg ret))        ; Index after the end of the list
    ,@(call 'car 'rax)
    (assign (reg rax) (reg ret))        ; Remainder of the list
    ,@(call 'car 'rcx)
    (assign (reg rcx) (reg ret))        ; The current parsed value
    ,@(call 'cons 'rcx 'rax)
    (assign (reg rax) (reg ret))        ; The parsed list
    ,@(call 'cons 'rax 'rbx)
    (goto (label parse-list-remainder-end))

    parse-list-remainder-end
    (stack-pop (reg rdx))
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    read-unterminated-input
    (error (const ,error-read-unterminated-input))

    read-unknown-char
    (error (const ,error-read-unknown-char))

    ;; Args:
    ;; 0 - memory address from which to start parsing
    ;; 1 - first memory address after the buffer
    ;; Output: pair containing the parsed list and the address
    ;; after the last character parsed
    parse-list
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0 - buffer location
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1
    (mem-load (reg rcx) (reg rax))                 ; Current char
    ,@(call 'list-start-char? 'rcx)
    (jez (label parse-list-error))
    (test (op =) (reg rcx) (const ,(char->integer #\()))
    (jez (label parse-list-error))
    (assign (reg rax) (op +) (reg rax) (const 1))
    ,@(call 'parse-list-remainder 'rax 'rbx)
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    parse-list-error
    (error (const ,error-read-list-bad-start-char))

    ;; Args:
    ;; 0 - memory address from which to start parsing
    ;; 1 - first memory address after the buffer
    ;; Output: pair containing the parsed expression and the address
    ;; after the last character parsed
    parse-exp
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0 - buffer location
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1

    parse-exp-test
    (test (op <) (reg rax) (reg rbx))
    (jez (label read-unterminated-input))
    (mem-load (reg rcx) (reg rax))      ; Current char
    ,@(call 'whitespace-char? 'rcx)
    (jne (label parse-exp-whitespace))
    ,@(call 'numeric-char? 'rcx)
    (jne (label parse-exp-int))
    ,@(call 'list-start-char? 'rcx)
    (jne (label parse-exp-list))
    (goto (label read-unknown-char))

    parse-exp-whitespace
    (assign (reg rax) (op +) (reg rax) (const 1))
    (goto (label parse-exp-test))

    parse-exp-int
    ,@(call 'parse-int 'rax 'rbx)
    (goto (label parse-exp-end))

    parse-exp-list
    ,@(call 'parse-list 'rax 'rbx)
    (goto (label parse-exp-end))

    parse-exp-end
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)
    ))

;;; Utilities

(define (wrap-code num-registers max-num-pairs memory-size code)
  `(,@(init max-num-pairs)
    (goto (label start))
    ,@(memory-management-defs num-registers max-num-pairs memory-size)
    start
    ,@code))

(define (range min max)
  "Integer range between MIN (inclusive) and MAX (exclusive)."
  (if (>= min max)
      '()
      (cons min
            (range (1+ min) max))))

(define (render-trace-value obj)
  (cond ((number? obj)
         (let ((tag (logand tag-mask obj))
               (val (logand value-mask obj)))
           (if (and (> tag 0)
                    (< tag #xf0000000))
               (cond ((= tag pair-tag)
                      (format #f "p~d" val))
                     ((= tag number-tag)
                      (format #f "n~d" val))
                     ((= tag broken-heart) "bh")
                     ((= tag empty-list) "()")
                     (else
                      (format #f "~d/~d" (bit-extract tag 28 32) val)))
               (format #f "~d" obj))))
        ((pair? obj)
         "<pair>")
        ((symbol? obj)
         (format #f "~a" obj))
        (else
         "<unknown>")))

(define (register-trace-renderer reg-name old new)
  (format #f
          "reg ~a: set to ~a (previous ~a)"
          reg-name
          (render-trace-value new)
          (render-trace-value old)))

(define (write-memory memory offset list)
  (for-each
   (lambda (n i)
     (set-memory! memory i n))
   list
   (iota (length list) offset)))

;;; Test suite

(define test-max-num-pairs 8)
(define test-num-registers 8)
(define test-stack-size 128)
(define test-read-buffer-size 128)
(define test-memory-size (+ the-cars-offset
                            (* test-max-num-pairs 4)
                            test-stack-size
                            test-read-buffer-size))
(define test-read-buffer-offset (+ the-cars-offset
                                   (* 4 test-max-num-pairs)))

(define* (make-test-machine code #:key
                            (num-registers test-num-registers)
                            (stack-size test-stack-size)
                            (max-num-pairs test-max-num-pairs)
                            (read-buffer-size test-read-buffer-size))
  (let ((memory-size (+ the-cars-offset
                        (* 4 max-num-pairs)
                        read-buffer-size
                        stack-size)))
    (make-machine-load-text
     num-registers
     memory-size
     (wrap-code num-registers max-num-pairs memory-size code)
     #:register-trace-renderer register-trace-renderer
     #:stack-limit stack-size)))

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
           (assign (reg rax) (op logior) (const ,number-tag) (const 1))
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

;;; Test set-cdr!: valid pair
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
           (call set-cdr!)
           (assign (reg sp) (op +) (reg sp) (const 2))
           (stack-push (reg rax))
           (call cdr)
           (stack-pop))))
       (ret (get-machine-register machine ret)))
  (start-machine machine)
  (test-eqv (get-register-contents ret) (logior number-tag 3)))

;;; Test set-cdr!: invalid pair
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (stack-push (reg rax))
           (call set-cdr!)
           (assign (reg sp) (op +) (reg sp) (const 2))))))
  (test-error #t (start-machine machine)))

;;; Test cadr
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (const 2))
           (assign (reg rbx) (const ,empty-list))
           ,@(call 'cons 'rax 'rbx)
           (assign (reg rax) (const 1))
           ,@(call 'cons 'rax 'ret)
           ,@(call 'cadr 'ret)))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine ret)) 2))

;;; Test cddr
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (const 2))
           (assign (reg rbx) (const ,empty-list))
           ,@(call 'cons 'rax 'rbx)
           (assign (reg rax) (const 1))
           ,@(call 'cons 'rax 'ret)
           ,@(call 'cddr 'ret)))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine ret)) empty-list))

;;; Test caar: '((1))
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (const 1))
           (assign (reg rbx) (const ,empty-list))
           ,@(call 'cons 'rax 'rbx)
           (assign (reg rax) (const ,empty-list))
           ,@(call 'cons 'ret 'rax)
           ,@(call 'caar 'ret)))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine ret)) 1))

;;; Test gc: single preserved pair
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 2))
           (stack-push (reg rax))
           (assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (call cons)
           (stack-pop)
           (assign (reg rax) (reg ret))
           (call gc)
           (stack-push (reg rax))
           (call car)
           (assign (reg rbx) (reg ret))
           (call cdr)
           (stack-pop)
           (assign (reg rcx) (reg ret)))))
       (rax (get-machine-register machine rax))
       (rbx (get-machine-register machine rbx))
       (rcx (get-machine-register machine rcx)))
  (start-machine machine)
  (test-eqv (get-register-contents rax) (logior pair-tag 0))
  (test-eqv (get-register-contents rbx) (logior number-tag 1))
  (test-eqv (get-register-contents rcx) (logior number-tag 2)))

;;; Test gc: single unpreserved pair
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 2))
           (stack-push (reg rax))
           (assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (stack-push (reg rax))
           (call cons)
           (stack-pop)
           (assign (reg ret) (const 0))
           (call gc))))
       (memory (get-machine-memory machine)))
  (start-machine machine)
  (test-eqv (get-memory memory free-pair-pointer) 0))

;;; Test gc: two references to same pair
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (assign (reg rbx) (op logior) (const ,number-tag) (const 2))
           ,@(call 'cons 'rax 'rbx)
           (assign (reg rax) (reg ret))
           (call gc))))
       (memory (get-machine-memory machine))
       (ret (get-machine-register machine ret))
       (rax (get-machine-register machine rax)))
  (start-machine machine)
  (test-eqv (get-memory memory free-pair-pointer) 1)
  (test-eqv (get-register-contents ret) (logior pair-tag 0))
  (test-eqv (get-register-contents rax) (logior pair-tag 0)))

;;; Test gc: preserved pair '((1 . 2) . (3 . 4))
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (op logior) (const ,number-tag) (const 1))
           (assign (reg rbx) (op logior) (const ,number-tag) (const 2))
           ,@(call 'cons 'rax 'rbx)
           (assign (reg rcx) (reg ret))
           (assign (reg rax) (op logior) (const ,number-tag) (const 3))
           (assign (reg rbx) (op logior) (const ,number-tag) (const 4))
           ,@(call 'cons 'rax 'rbx)
           ,@(call 'cons 'rcx 'ret)
           (call gc)
           ,@(call 'car 'ret)
           ,@(call 'cdr 'ret))))
       (memory (get-machine-memory machine))
       (ret (get-machine-register machine ret)))
  (start-machine machine)
  (test-eqv (get-memory memory free-pair-pointer) 3)
  (test-eqv (get-register-contents ret) (logior number-tag 2)))

;;; Test gc: triggered when out of pairs
(let* ((machine
        (make-test-machine
         `(
           ;; Create max number of (unreferenced) pairs
           (assign (reg rax) (const 0))
           loop
           (test (op <) (reg rax) (const ,test-max-num-pairs))
           (jez (label after-loop))
           ,@(call 'cons 'rax rax)
           (assign (reg ret) (const 0))
           (assign (reg rax) (op +) (reg rax) (const 1))
           (goto (label loop))

           after-loop
           ;; Create further pair
           (assign (reg rax) (const ,test-max-num-pairs))
           ,@(call 'cons 'rax 'rax)
           (assign (reg rax) (reg ret))
           ,@(call 'car 'rax)
           (assign (reg rbx) (reg ret))
           ,@(call 'cdr 'rax)
           (assign (reg rcx) (reg ret)))))
       (memory (get-machine-memory machine))
       (rbx (get-machine-register machine rbx))
       (rcx (get-machine-register machine rcx)))
  (start-machine machine)
  (test-eqv (get-memory memory free-pair-pointer) 1)
  (test-eqv (get-register-contents rbx) test-max-num-pairs)
  (test-eqv (get-register-contents rcx) test-max-num-pairs))

;;; Test gc: fails when out of pairs, even after GC
(let* ((machine
        (make-test-machine
         `(
           ;; Create max number of pairs
           (assign (reg rax) (const 0))
           loop
           (test (op <) (reg rax) (const ,test-max-num-pairs))
           (jez (label after-loop))
           ,@(call 'cons 'rax rax)
           (stack-push (reg ret))
           (assign (reg rax) (op +) (reg rax) (const 1))
           (goto (label loop))

           after-loop
           ;; Create further pair
           (assign (reg rax) (const ,test-max-num-pairs))
           ,@(call 'cons 'rax 'rax)))))
  (test-error #t (start-machine machine)))

;;; Test gc: flips correctly multiple times
(let* ((machine
        (make-test-machine
         `((assign (reg rax) (const 0))
           (assign (reg rbx) (const ,(1+ (* test-max-num-pairs 2)))) ; Limit
           loop
           (test (op <) (reg rax) (reg rbx))
           (jez (label after-loop))
           ,@(call 'cons 'rax rax)
           (assign (reg ret) (const 0))
           (assign (reg rax) (op +) (reg rax) (const 1))
           (goto (label loop))
           after-loop)))
       (memory (get-machine-memory machine)))
  (start-machine machine)
  (test-eqv (get-memory memory free-pair-pointer) 1))

;;; Test numeric-char?: valid values
(for-each
 (lambda (char)
   (let ((machine
          (make-test-machine
           `((assign (reg rax) (const ,(char->integer char)))
             ,@(call 'numeric-char? 'rax)))))
     (start-machine machine)
     (test-eqv (get-register-contents (get-machine-flag machine)) 1)))
 (string->list "0123456789"))

;;; Test numeric-char?: invalid values
(for-each
 (lambda (char)
   (let ((machine
          (make-test-machine
           `((assign (reg rax) (const ,(char->integer char)))
             ,@(call 'numeric-char? 'rax)))))
     (start-machine machine)
     (test-eqv (get-register-contents (get-machine-flag machine)) 0)))
 (string->list " azAZ!"))

;;; Test whitespace-char?: valid values
(for-each
 (lambda (char)
   (let ((machine
          (make-test-machine
           `((assign (reg rax) (const ,(char->integer char)))
             ,@(call 'whitespace-char? 'rax)))))
     (start-machine machine)
     (test-eqv (get-register-contents (get-machine-flag machine)) 1)))
 (string->list " "))

;;; Test whitespace-char?: invalid values
(for-each
 (lambda (char)
   (let ((machine
          (make-test-machine
           `((assign (reg rax) (const ,(char->integer char)))
             ,@(call 'whitespace-char? 'rax)))))
     (start-machine machine)
     (test-eqv (get-register-contents (get-machine-flag machine)) 0)))
 (string->list "09azAZ!"))

;;; Test parse-int: valid values
(for-each
   (lambda (test-case)
     (let* ((str
             (if (string? test-case)
                 test-case
                 (car test-case)))
            (parsed-number
             (if (string? test-case)
                 (string->number test-case)
                 (cadr test-case)))
            (count-chars-read
             (if (string? test-case)
                 (string-length test-case)
                 (caddr test-case)))
            (machine
             (make-test-machine
              `((assign (reg rax) (const ,test-read-buffer-offset))
                (assign (reg rbx) (const ,(+ test-read-buffer-offset test-read-buffer-size)))
                ,@(call 'parse-int 'rax 'rbx)
                (assign (reg rax) (reg ret))
                ,@(call 'car 'rax)
                (assign (reg rbx) (reg ret))
                ,@(call 'cdr 'rax))))
            (memory (get-machine-memory machine)))
       (reset-machine machine)
       (write-memory memory
                     test-read-buffer-offset
                     (map char->integer (string->list str)))
       (continue-machine machine)
       (test-eqv (get-register-contents (get-machine-register machine rbx))
         (logior parsed-number number-tag))
       (test-eqv (get-register-contents (get-machine-register machine ret))
         (+ test-read-buffer-offset count-chars-read))))
   '(
     "0"
     "9"
     "999"
     "1001"
     "001111"
     ("0 " 0 1)
     ("0)" 0 1)
     ("9d" 9 1)
     ("900d " 900 3)))

;;; Test parse-list: '()
(let ((machine (make-test-machine
                `((assign (reg rax) (const ,test-read-buffer-offset))
                  (assign (reg rbx) (const ,(+ test-read-buffer-offset test-read-buffer-size)))
                  ,@(call 'parse-list 'rax 'rbx)
                  (assign (reg rax) (reg ret))
                  ,@(call 'cdr 'rax)
                  (assign (reg rbx) (reg ret)) ; Index in buffer after parsing list
                  ,@(call 'car 'rax)
                  (assign (reg rax) (reg ret))))) ; The parsed list
      (exp (string->list (format #f "~a" '()))))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine rbx))
    (+ test-read-buffer-offset (length exp)))
  (test-eqv (get-register-contents (get-machine-register machine rax)) empty-list))

;;; Test parse-list: '(1 2)
(let ((machine (make-test-machine
                `((assign (reg rax) (const ,test-read-buffer-offset))
                  (assign (reg rbx) (const ,(+ test-read-buffer-offset test-read-buffer-size)))
                  ,@(call 'parse-list 'rax 'rbx)
                  (assign (reg rax) (reg ret))
                  ,@(call 'cdr 'rax)
                  (assign (reg rbx) (reg ret)) ; Index in buffer after parsing list
                  ,@(call 'car 'rax)
                  (assign (reg rax) (reg ret)) ; The parsed list
                  ,@(call 'car 'rax)
                  (assign (reg rcx) (reg ret))  ; CAR of list
                  ,@(call 'cadr 'rax)
                  (assign (reg rdx) (reg ret)) ; CADR of list
                  ,@(call 'cddr 'rax)))) ; CDDR of list
      (exp (string->list (format #f "~a" '(1 2)))))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine rbx))
    (+ test-read-buffer-offset (length exp)))
  (test-eqv (get-register-contents (get-machine-register machine rcx))
    (logior number-tag 1))
  (test-eqv (get-register-contents (get-machine-register machine rdx))
    (logior number-tag 2))
  (test-eqv (get-register-contents (get-machine-register machine ret)) empty-list))

;;; Test parse-list: '((1) 2)
(let ((machine (make-test-machine
                `((assign (reg rax) (const ,test-read-buffer-offset))
                  (assign (reg rbx) (const ,(+ test-read-buffer-offset test-read-buffer-size)))
                  ,@(call 'parse-list 'rax 'rbx)
                  (assign (reg rax) (reg ret))
                  ,@(call 'cdr 'rax)
                  (assign (reg rbx) (reg ret)) ; Index in buffer after parsing list
                  ,@(call 'car 'rax)
                  (assign (reg rax) (reg ret)) ; The parsed list
                  ,@(call 'caar 'rax)
                  (assign (reg rcx) (reg ret))  ; CAAR of list
                  ,@(call 'cadr 'rax)
                  (assign (reg rdx) (reg ret)) ; CADR of list
                  ,@(call 'cddr 'rax)))) ; CDDR of list
      (exp (string->list (format #f "~a" '((1) 2)))))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine rbx))
    (+ test-read-buffer-offset (length exp)))
  (test-eqv (get-register-contents (get-machine-register machine rcx))
    (logior number-tag 1))
  (test-eqv (get-register-contents (get-machine-register machine rdx))
    (logior number-tag 2))
  (test-eqv (get-register-contents (get-machine-register machine ret)) empty-list))

;;; Test parse-list: unusual whitespace
(let ((machine (make-test-machine
                `((assign (reg rax) (const ,test-read-buffer-offset))
                  (assign (reg rbx) (const ,(+ test-read-buffer-offset test-read-buffer-size)))
                  ,@(call 'parse-list 'rax 'rbx)
                  (assign (reg rax) (reg ret))
                  ,@(call 'cdr 'rax)
                  (assign (reg rbx) (reg ret)) ; Index in buffer after parsing list
                  ,@(call 'car 'rax)
                  (assign (reg rax) (reg ret)) ; The parsed list
                  ,@(call 'car 'rax)
                  (assign (reg rcx) (reg ret))  ; CAR of list
                  ,@(call 'cadr 'rax)
                  (assign (reg rdx) (reg ret)) ; CADR of list
                  ,@(call 'cddr 'rax)))) ; CDDR of list
      (exp (string->list "( 1  2   )")))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine rbx))
    (+ test-read-buffer-offset (length exp)))
  (test-eqv (get-register-contents (get-machine-register machine rcx))
    (logior number-tag 1))
  (test-eqv (get-register-contents (get-machine-register machine rdx))
    (logior number-tag 2))
  (test-eqv (get-register-contents (get-machine-register machine ret)) empty-list))

;;; Test parse-list: error on unterminated input
(let ((machine (make-test-machine
                `((assign (reg rax) (const ,test-read-buffer-offset))
                  (assign (reg rbx) (const ,(+ test-read-buffer-offset test-read-buffer-size)))
                  ,@(call 'parse-list 'rax 'rbx))))
      (exp (string->list "(1 2")))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (test-error #t (continue-machine machine)))

;;; Test parse-exp: integer
(let ((machine (make-test-machine
                `((assign (reg rax) (const ,test-read-buffer-offset))
                  (assign (reg rbx) (const ,(+ test-read-buffer-offset test-read-buffer-size)))
                  ,@(call 'parse-exp 'rax 'rbx)
                  (assign (reg rbx) (reg ret))
                  ,@(call 'cdr 'rbx)
                  (assign (reg rax) (reg ret)) ; Index in buffer after parse
                  ,@(call 'car 'rbx)
                  (assign (reg rbx) (reg ret))))) ; The parsed value
      (exp (string->list "9")))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine rax))
    (+ test-read-buffer-offset (length exp)))
  (test-eqv (get-register-contents (get-machine-register machine rbx))
    (logior number-tag 9)))

;;; Test parse-exp: integer with leading and trailing whitespace
(let ((machine (make-test-machine
                `((assign (reg rax) (const ,test-read-buffer-offset))
                  (assign (reg rbx) (const ,(+ test-read-buffer-offset test-read-buffer-size)))
                  ,@(call 'parse-exp 'rax 'rbx)
                  (assign (reg rbx) (reg ret))
                  ,@(call 'cdr 'rbx)
                  (assign (reg rax) (reg ret)) ; Index in buffer after parse
                  ,@(call 'car 'rbx)
                  (assign (reg rbx) (reg ret))))) ; The parsed value
      (exp (string->list "  9  ")))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine rax))
    (+ test-read-buffer-offset 3))
  (test-eqv (get-register-contents (get-machine-register machine rbx))
    (logior number-tag 9)))

;;; Test parse-exp: list
(let ((machine (make-test-machine
                `((assign (reg rax) (const ,test-read-buffer-offset))
                  (assign (reg rbx) (const ,(+ test-read-buffer-offset test-read-buffer-size)))
                  ,@(call 'parse-exp 'rax 'rbx)
                  (assign (reg rbx) (reg ret))
                  ,@(call 'cdr 'rbx)
                  (assign (reg rax) (reg ret)) ; Index in buffer after parse
                  ,@(call 'car 'rbx)
                  (assign (reg rbx) (reg ret)) ; The parsed value
                  ,@(call 'car 'rbx)
                  (assign (reg rcx) (reg ret)) ; CAR of parsed value
                  ,@(call 'cdr 'rbx)
                  (assign (reg rdx) (reg ret))))) ; CDR of parsed value
      (exp (string->list "(1)")))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine rax))
    (+ test-read-buffer-offset (length exp)))
  (test-eqv (get-register-contents (get-machine-register machine rcx))
    (logior number-tag 1))
  (test-eqv (get-register-contents (get-machine-register machine rdx)) empty-list))

;;; Test parse-exp: malformed input
(for-each
 (lambda (str)
   (let ((machine (make-test-machine
                   `((assign (reg rax) (const ,test-read-buffer-offset))
                     (assign (reg rbx) (const ,(+ test-read-buffer-offset test-read-buffer-size)))
                     ,@(call 'parse-exp 'rax 'rbx))))
         (exp (string->list str)))
     (reset-machine machine)
     (write-memory (get-machine-memory machine)
                   test-read-buffer-offset
                   (map char->integer exp))
     (test-error (continue-machine machine))))
 '(")1 2 3)" "(1 2"))

;;; Test eq successful: '((1) (2))
(let ((machine
       (make-test-machine
        `((goto (label _start))

          build-list
          (stack-push (reg rax))
          (stack-push (reg rbx))
          (stack-push (reg rcx))
          (assign (reg rax) (op logior) (const ,number-tag) (const 2))
          (assign (reg rbx) (const ,empty-list))
          ,@(call 'cons 'rax 'rbx)
          (assign (reg rax) (reg ret))
          ,@(call 'cons 'rax 'rbx)
          (assign (reg rcx) (reg ret))
          (assign (reg rax) (op logior) (const ,number-tag) (const 1))
          (assign (reg rbx) (const ,empty-list))
          ,@(call 'cons 'rax 'rbx)
          ,@(call 'cons 'ret 'rcx)
          (stack-pop (reg rcx))
          (stack-pop (reg rbx))
          (stack-pop (reg rax))
          (ret)

          _start
          ,@(call 'build-list)
          (assign (reg rax) (reg ret))
          ,@(call 'build-list)
          (assign (reg rbx) (reg ret))
          ,@(call 'equal? 'rax 'rbx)))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 'flag)) 1))

(let ((machine
       (make-test-machine
        `((goto (label _start))

          ;; Args:
          ;; 0 - integer M
          ;; 1 - integer N
          ;; Output: the list [M..N)
          range
          (stack-push (reg rax))
          (stack-push (reg rbx))
          (stack-push (reg rcx))
          (mem-load (reg rax) (op +) (reg bp) (const 2)) ; M
          (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; N
          (test (op >=) (reg rax) (reg rbx))
          (jne (label range-base-case))
          (assign (reg rcx) (op +) (reg rax) (const 1))
          ,@(call 'range 'rcx 'rbx)
          ,@(call 'cons 'rax 'ret)
          (goto (label range-end))

          range-base-case
          (assign (reg ret) (const ,empty-list))

          range-end
          (stack-pop (reg rcx))
          (stack-pop (reg rbx))
          (stack-pop (reg rax))
          (ret)

          _start
          (assign (reg rax) (const 0))
          (assign (reg rbx) (const 2))
          ,@(call 'range 'rax 'rbx)
          (assign (reg rcx) (reg ret))
          (assign (reg rbx) (const 3))
          ,@(call 'range 'rax 'rbx)
          ,@(call 'equal? 'rcx 'ret)))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 'flag)) 0))

(test-end "asm-interpreter-test")
