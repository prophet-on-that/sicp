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
(define symbol-tag #x50000000)

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
(define symbol-list 6)
(define char-table-offset 8)
(define char-table-size 128)
(define the-cars-offset (+ char-table-offset char-table-size))

;;; Exit codes
;;; 1 - attempting to take CAR of a non-pair
;;; 2 - attempting to take CDR of a non-pair
;;; 3 - attempting to set the CAR of a non-pair
;;; 4 - attempting to set the CAR of a non-pair
(define error-no-remaining-pairs 5)
(define error-read-list-bad-start-char 8)
(define error-read-unterminated-input 9)
(define error-read-symbol-bad-start-char 10)

(define (get-read-buffer-offset max-num-pairs)
  (+ the-cars-offset (* 4 max-num-pairs)))

(define number-chars "0123456789")
(define symbol-start-chars "!#$%&*+,-./:<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_abcdefghijklmnopqrstuvwxyz{|}~")
(define char-groups
  `((whitespace . " ")
    (number . ,number-chars)
    (list-start . "(")
    (list-end . ")")
    (symbol-start . ,symbol-start-chars)
    (symbol-body . ,(string-append symbol-start-chars number-chars))))

(define (char-group-bitmask char)
  (fold
   (lambda (char-group i bitmask)
     (if (string-index (cdr char-group) char)
         (logior (integer-expt 2 i) bitmask)
         bitmask))
   0
   char-groups
   (iota (length char-groups))))

(define (test-char-in-group reg-name target-reg group-name)
  "Test char in register REG-NAME for membership of group
GROUP-NAME. Modify TARGET-REG during operation."
  (let ((group-mask
         (integer-expt
          2
          (list-index
           (lambda (elem)
             (eq? group-name (car elem)))
           char-groups))))
    (if group-mask
        `((mem-load (reg ,target-reg) (op +) (const ,char-table-offset) (reg ,reg-name))
          (assign (reg ,target-reg) (op logand) (const ,group-mask) (reg ,target-reg))
          (test (op >) (reg ,target-reg) (const 0)))
        (error "Unrecognised group name -- TEST-CHAR-IN-GROUP" group-name))))

(define parse-failed-value 0)

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
    (assign (reg rax) (const ,(get-read-buffer-offset max-num-pairs)))
    (mem-store (const ,read-buffer-pointer) (reg rax))

    ;; Initalise symbol list
    (assign (reg rax) (const ,empty-list))
    (mem-store (const ,symbol-list) (reg rax))

    ;; Initialise char table. For parsing expressions, we store an
    ;; integer for each character representing the various character
    ;; groups (whitespace, number etc) that the character belongs
    ;; to. We then index the table with the character's numeric
    ;; representation and test the appropriate bit to determine if it
    ;; belongs to a group.
    ,@(map
       (lambda (n)
         (let ((bitmask (char-group-bitmask (integer->char n)))
               (offset (+ n char-table-offset)))
           `(mem-store (const ,offset) (const ,bitmask))))
       (iota char-table-size))))

(define (memory-management-defs num-registers max-num-pairs memory-size)
  `(
    ;; Args:
    ;; 0 - car of new pair
    ;; 1 - cdr of new pair
    ;; Returns: newly-assigned pair
    cons
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (stack-push (reg rdx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; arg 0
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; arg 1

    cons-entry
    ;; Trigger garbage collection when no pairs are available
    (mem-load (reg rcx) (const ,free-pair-pointer))
    (test (op >=) (reg rcx) (const ,max-num-pairs))
    (jez (label cons-after-gc))
    (call gc)
    ;; Throw error if no space exists after garbage collection
    (mem-load (reg rcx) (const ,free-pair-pointer))
    (test (op >=) (reg rcx) (const ,max-num-pairs))
    (jez (label cons-after-gc))
    (error (const ,error-no-remaining-pairs))

    cons-after-gc
    (mem-load (reg rdx) (const ,the-cars-pointer))
    (assign (reg rdx) (op +) (reg rcx) (reg rdx))
    (mem-store (reg rdx) (reg rax))
    (mem-load (reg rdx) (const ,the-cdrs-pointer))
    (assign (reg rdx) (op +) (reg rcx) (reg rdx))
    (mem-store (reg rdx) (reg rbx))
    (assign (reg ret) (op logior) (reg rcx) (const ,pair-tag))
    (assign (reg rcx) (op +) (reg rcx) (const 1)) ; new free pair pointer
    (mem-store (const ,free-pair-pointer) (reg rcx))
    (stack-pop (reg rdx))
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

    ;; Args:
    ;; 0 - pair from which to extract the caadr
    ;; Output: caadr of pair
    caadr
    (mem-load (reg ret) (op +) (reg bp) (const 2)) ; Arg 0 - pair
    ,@(call 'cdr 'ret)
    ,@(call 'car 'ret)
    ,@(call 'car 'ret)
    (ret)

    ;; Args:
    ;; 0 - pair from which to extract the caddr
    ;; Output: caddr of pair
    caddr
    (mem-load (reg ret) (op +) (reg bp) (const 2)) ; Arg 0 - pair
    ,@(call 'cdr 'ret)
    ,@(call 'cdr 'ret)
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
    (test (op =) (reg rax) (reg rbx))

    equal?-end
    (stack-pop (reg rdx))
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - list holding the parsed characters of the symbol
    ;; Output: the value uniquely identifying the symbol
    ;;
    ;; A symbol is identified by its index in SYMBOL-LIST.
    ;; TODO: ensure symbol list is carried over in garbage collection
    intern-symbol
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (stack-push (reg rdx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0
    (mem-load (reg rbx) (const ,symbol-list))
    (test (op =) (reg rbx) (const ,empty-list))
    (jne (label intern-symbol-empty-list))
    (assign (reg rcx) (const 0))        ; Index in SYMBOL-LIST

    intern-symbol-test
    ,@(call 'car 'rbx)
    ,@(call 'equal? 'rax 'ret)
    (jne (label intern-symbol-found))
    (assign (reg rcx) (op +) (reg rcx) (const 1))
    ,@(call 'cdr 'rbx)
    (test (op =) (reg ret) (const ,empty-list))
    (jne (label intern-symbol-not-found))
    (assign (reg rbx) (reg ret))
    (goto (label intern-symbol-test))

    intern-symbol-empty-list
    ;; Set SYMBOL-LIST to a singleton list
    (assign (reg rdx) (const ,empty-list))
    ,@(call 'cons 'rax 'rdx)
    (mem-store (const ,symbol-list) (reg ret))
    (assign (reg ret) (op logior) (const 0) (const ,symbol-tag))
    (goto (label intern-symbol-end))

    intern-symbol-found
    (assign (reg ret) (op logior) (reg rcx) (const ,symbol-tag))
    (goto (label intern-symbol-end))

    intern-symbol-not-found
    ;; Add the symbol to the end of SYMBOL-LIST
    (assign (reg rdx) (const ,empty-list))
    ,@(call 'cons 'rax 'rdx)
    ,@(call 'set-cdr! 'rbx 'ret)
    (assign (reg ret) (op logior) (reg rcx) (const ,symbol-tag))

    intern-symbol-end
    (stack-pop (reg rdx))
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - memory address from which to start parsing
    ;; 1 - first memory address after the end of the input string
    ;; Output: pair containing the parsed integer and the address
    ;; after the last character parsed, or PARSE-FAILED-VALUE
    ;; indicating parsing has failed.
    parse-int
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (stack-push (reg rdx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0 - buffer location
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1
    (test (op <) (reg rax) (reg rbx))
    (jez (label parse-int-error))
    (mem-load (reg rcx) (reg rax))      ; Current char
    ,@(test-char-in-group 'rcx 'rdx 'number)
    (jez (label parse-int-error))
    (assign (reg rdx) (op -) (reg rcx) (const ,(char->integer #\0))) ; Parsed number so far
    (assign (reg rax) (op +) (reg rax) (const 1))

    parse-int-test
    (stack-push (reg rdx))
    (test (op <) (reg rax) (reg rbx))
    (jez (label parse-int-complete))
    (mem-load (reg rcx) (reg rax))      ; Current char
    ,@(test-char-in-group 'rcx 'rdx 'whitespace)
    (jne (label parse-int-complete))
    ,@(test-char-in-group 'rcx 'rdx 'list-end)
    (jne (label parse-int-complete))
    ,@(test-char-in-group 'rcx 'rdx 'number)
    (jez (label parse-int-error))
    (stack-pop (reg rdx))
    (assign (reg rcx) (op -) (reg rcx) (const ,(char->integer #\0)))
    (assign (reg rdx) (op *) (reg rdx) (const 10))
    (assign (reg rdx) (op +) (reg rdx) (reg rcx))
    (assign (reg rax) (op +) (reg rax) (const 1))
    (goto (label parse-int-test))

    parse-int-error
    (assign (reg ret) (const ,parse-failed-value))
    (goto (label parse-int-end))

    parse-int-complete
    (stack-pop (reg rdx))
    (assign (reg rdx) (op logior) (reg rdx) (const ,number-tag))
    ,@(call 'cons 'rdx 'rax)

    parse-int-end
    (stack-pop (reg rdx))
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - memory address from which to start parsing
    ;; 1 - first memory address after the end of the input string
    ;; Output: pair containing the parsed symbol and the address
    ;; after the last character parsed, or PARSE-FAILED-VALUE
    ;; indicating parsing has failed.
    parse-symbol
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (stack-push (reg rdx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0 - buffer location
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1
    (test (op <) (reg rax) (reg rbx))
    (jez (label parse-symbol-error))
    (mem-load (reg rcx) (reg rax))                 ; Current char
    ,@(test-char-in-group 'rcx 'rdx 'symbol-start)
    (jez (label parse-symbol-error))
    (assign (reg rax) (op +) (reg rax) (const 1))
    ,@(call 'parse-symbol-remainder 'rax 'rbx)
    (test (op =) (reg ret) (const ,parse-failed-value))
    (jne (label parse-symbol-error))
    (assign (reg rax) (reg ret))
    ,@(call 'car 'rax)
    (assign (reg rbx) (reg ret)) ; The remainder of the symbol as a list
    ,@(call 'cdr 'rax)
    (assign (reg rax) (reg ret))   ; Index after the end of the symbol
    ,@(call 'cons 'rcx 'rbx)
    (assign (reg rbx) (reg ret)) ; The parsed symbol as a character list
    ,@(call 'intern-symbol 'rbx)
    ,@(call 'cons 'ret 'rax)            ; TODO: TCO
    (goto (label parse-symbol-end))

    parse-symbol-error
    (assign (reg ret) (const ,parse-failed-value))

    parse-symbol-end
    (stack-pop (reg rdx))
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - memory address from which to start parsing
    ;; 1 - first memory address after the end of the input string
    ;; Output: pair containing the parsed symbol and the address
    ;; after the last character parsed, or PARSE-FAILED-VALUE
    ;; indicating parsing has failed.
    parse-symbol-remainder
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (stack-push (reg rdx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0 - buffer location
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1
    (test (op <) (reg rax) (reg rbx))
    (jez (label parse-symbol-remainder-base-case))
    (mem-load (reg rcx) (reg rax))      ; Current char
    ,@(test-char-in-group 'rcx 'rdx 'whitespace)
    (jne (label parse-symbol-remainder-base-case))
    ,@(test-char-in-group 'rcx 'rdx 'list-end)
    (jne (label parse-symbol-remainder-base-case))
    ,@(test-char-in-group 'rcx 'rdx 'symbol-body)
    (jez (label parse-symbol-remainder-error))
    (assign (reg rax) (op +) (reg rax) (const 1))
    ,@(call 'parse-symbol-remainder 'rax 'rbx)
    (test (op =) (reg ret) (const ,parse-failed-value))
    (jne (label parse-symbol-remainder-error))
    (assign (reg rax) (reg ret))
    ,@(call 'car 'rax)
    (assign (reg rbx) (reg ret)) ; The character list for the rest of the symbol
    ,@(call 'cdr 'rax)
    (assign (reg rax) (reg ret)) ; Index after the last parsed character
    ,@(call 'cons 'rcx 'rbx)     ; The character list from this point
    ,@(call 'cons 'ret 'rax)            ; TODO: TCO
    (goto (label parse-symbol-remainder-end))

    parse-symbol-remainder-error
    (assign (reg ret) (const ,parse-failed-value))
    (goto (label parse-symbol-remainder-end))

    parse-symbol-remainder-base-case
    (assign (reg rcx) (const ,empty-list))
    ,@(call 'cons 'rcx 'rax)            ; TODO: TCO

    parse-symbol-remainder-end
    (stack-pop (reg rdx))
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - memory address from which to start parsing
    ;; 1 - first memory address after the end of the input string
    ;; Output: first memory address after the parsed whitespace (or
    ;; the first argument if no whitespace is parsed.
    parse-whitespace*
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0 - buffer location
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1

    parse-whitespace*-test
    (test (op <) (reg rax) (reg rbx))
    (jez (label parse-whitespace*-end))
    (mem-load (reg rcx) (reg rax))
    ,@(test-char-in-group 'rcx 'rcx 'whitespace)
    (jez (label parse-whitespace*-end))
    (assign (reg rax) (op +) (reg rax) (const 1))
    (goto (label parse-whitespace*-test))

    parse-whitespace*-end
    (assign (reg ret) (reg rax))
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - memory address from which to start parsing
    ;; 1 - first memory address after the end of the input string
    ;; Output: pair containing the parsed list and the address
    ;; after the last character parsed, or PARSE-FAILED-VALUE
    ;; indicating parsing has failed.
    parse-list-remainder
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (stack-push (reg rdx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0 - buffer location
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1

    parse-list-remainder-entry
    ,@(call 'parse-whitespace* 'rax 'rbx)
    (assign (reg rax) (reg ret))
    ;; Attempt to parse an expression
    ,@(call 'parse-exp 'rax 'rbx)
    (test (op =) (reg ret) (const ,parse-failed-value))
    (jez (label parse-list-remainder-continue))
    ;; Test for end of list
    (test (op <) (reg rax) (reg rbx))
    (jez (label parse-list-remainder-error))
    (mem-load (reg rcx) (reg rax))
    ,@(test-char-in-group 'rcx 'rcx 'list-end)
    (jne (label parse-list-remainder-empty-list))
    (goto (label parse-list-remainder-error))

    parse-list-remainder-empty-list
    (assign (reg rax) (op +) (reg rax) (const 1))
    (assign (reg rcx) (const ,empty-list))
    ,@(call 'cons 'rcx 'rax)
    (goto (label parse-list-remainder-end))

    parse-list-remainder-continue
    (assign (reg rcx) (reg ret))
    ,@(call 'cdr 'rcx)
    (assign (reg rax) (reg ret))
    ,@(call 'car 'rcx)
    (assign (reg rcx) (reg ret))        ; Newly-parsed value
    ,@(call 'parse-list-remainder 'rax 'rbx)
    (test (op =) (reg ret) (const ,parse-failed-value))
    (jne (label parse-list-remainder-error))
    (assign (reg rdx) (reg ret))
    ,@(call 'cdr 'rdx)
    (assign (reg rax) (reg ret))
    ,@(call 'car 'rdx)
    (assign (reg rdx) (reg ret))        ; The rest of the list
    ,@(call 'cons 'rcx 'rdx)            ; The parsed list
    ,@(call 'cons 'ret 'rax)
    (goto (label parse-list-remainder-end))

    parse-list-remainder-error
    (assign (reg ret) (const ,parse-failed-value))

    parse-list-remainder-end
    (stack-pop (reg rdx))
    (stack-pop (reg rcx))
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - memory address from which to start parsing
    ;; 1 - first memory address after the end of the input string
    ;; Output: pair containing the parsed list and the address
    ;; after the last character parsed, or PARSE-FAILED-VALUE
    ;; indicating parsing has failed.
    parse-exp
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0 - buffer location
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1
    ,@(call 'parse-symbol 'rax 'rbx)
    (test (op =) (reg ret) (const ,parse-failed-value))
    (jez (label parse-exp-end))
    ,@(call 'parse-int 'rax 'rbx)
    (test (op =) (reg ret) (const ,parse-failed-value))
    (jez (label parse-exp-end))
    ,@(call 'parse-list 'rax 'rbx)
    (test (op =) (reg ret) (const ,parse-failed-value))
    (jez (label parse-exp-end))
    ;; Parse failed
    (assign (reg ret) (const ,parse-failed-value))

    parse-exp-end
    (stack-pop (reg rbx))
    (stack-pop (reg rax))
    (ret)

    ;; Args:
    ;; 0 - memory address from which to start parsing
    ;; 1 - first memory address after the end of the input string
    ;; Output: pair containing the parsed list and the address
    ;; after the last character parsed, or PARSE-FAILED-VALUE
    ;; indicating parsing has failed.
    parse-list
    (stack-push (reg rax))
    (stack-push (reg rbx))
    (stack-push (reg rcx))
    (mem-load (reg rax) (op +) (reg bp) (const 2)) ; Arg 0 - buffer location
    (mem-load (reg rbx) (op +) (reg bp) (const 3)) ; Arg 1
    (test (op <) (reg rax) (reg rbx))
    (jez (label parse-list-error))
    (mem-load (reg rcx) (reg rax))                 ; Current char
    ,@(test-char-in-group 'rcx 'rcx 'list-start)
    (jez (label parse-list-error))
    (assign (reg rax) (op +) (reg rax) (const 1))
    (stack-push (reg rdx))
    (goto (label parse-list-remainder-entry))     ; TCO

    parse-list-error
    (assign (reg ret) (const ,parse-failed-value))
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
                     ((= tag symbol-tag)
                      (format #f "s~d" val))
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

;;; Test equal? successful: '((1) (2))
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

;;; Test equal? unsuccessful: (1 2) vs (1 2 3)
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

;;; Test parse-int: success cases
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
                (assign (reg rbx) (const ,(+ test-read-buffer-offset (string-length str))))
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
   '("0"
     "9"
     "999"
     "1001"
     "001111"
     ("9 " 9 1)
     ("9)" 9 1)))

;;; Test parse-int: failure cases
(for-each
   (lambda (str)
     (let* ((machine
             (make-test-machine
              `((assign (reg rax) (const ,test-read-buffer-offset))
                (assign (reg rbx) (const ,(+ test-read-buffer-offset (string-length str))))
                ,@(call 'parse-int 'rax 'rbx)
                (test (op =) (reg ret) (const ,parse-failed-value))
                (jne (label end))
                (error (const -1))

                end)))
            (memory (get-machine-memory machine)))
       (reset-machine machine)
       (write-memory memory
                     test-read-buffer-offset
                     (map char->integer (string->list str)))
       (continue-machine machine)))
   '(""
     "d"
     "1d"
     "1."
     "1'"
     "1("))

;;; Test parse-int: bounds checking
(for-each
 (lambda (test-case)
   (let* ((str (car test-case))
          (bound (cadr test-case))
          (parsed-number (caddr test-case))
          (machine
           (make-test-machine
            `((assign (reg rax) (const ,test-read-buffer-offset))
                (assign (reg rbx) (const ,(+ test-read-buffer-offset bound)))
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
         (+ test-read-buffer-offset bound))))
 '(("99" 1 9)
   ("999" 2 99)
   ("99d" 2 99)))

;;; Test parse-list: '()
(let* ((exp (string->list (format #f "~a" '())))
       (machine (make-test-machine
                 `((assign (reg rax) (const ,test-read-buffer-offset))
                   (assign (reg rbx) (const ,(+ test-read-buffer-offset (length exp))))
                   ,@(call 'parse-list 'rax 'rbx)
                   (assign (reg rax) (reg ret))
                   ,@(call 'car 'rax)
                   (assign (reg rbx) (reg ret)) ; The parsed value
                   ,@(call 'cdr 'rax)
                   (assign (reg rcx) (reg ret)))))) ; Index after parsing
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine rbx)) empty-list)
  (test-eqv (get-register-contents (get-machine-register machine rcx))
    (+ test-read-buffer-offset (length exp))))

;;; Test parse-list: '(1 2)
(let* ((l '(1 2))
       (exp (string->list (format #f "~a" l)))
       (machine (make-test-machine
                 `((assign (reg rax) (const ,test-read-buffer-offset))
                   (assign (reg rbx) (const ,(+ test-read-buffer-offset (length exp))))
                   ,@(call 'parse-list 'rax 'rbx)
                   (assign (reg rax) (reg ret))
                   ,@(call 'car 'rax)
                   (assign (reg rbx) (reg ret)) ; Parsed value
                   ,@(call 'cdr 'rax)
                   (assign (reg rax) (reg ret)) ; Index after parsing
                   ,@(call 'car 'rbx)
                   (assign (reg rcx) (reg ret)) ; CAR of list
                   ,@(call 'cadr 'rbx)
                   (assign (reg rdx) (reg ret)) ; CADR of list
                   ,@(call 'cddr 'rbx)))))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine rax))
    (+ test-read-buffer-offset (length exp)))
  (test-eqv (get-register-contents (get-machine-register machine rcx))
    (logior number-tag (car l)))
  (test-eqv (get-register-contents (get-machine-register machine rdx))
    (logior number-tag (cadr l)))
  (test-eqv (get-register-contents (get-machine-register machine ret))
    empty-list))

;;; Test parse-list: '((1) (2))
(let* ((l '((1) (2)))
       (exp (string->list (format #f "~a" l)))
       (machine (make-test-machine
                 `((assign (reg rax) (const ,test-read-buffer-offset))
                   (assign (reg rbx) (const ,(+ test-read-buffer-offset (length exp))))
                   ,@(call 'parse-list 'rax 'rbx)
                   (assign (reg rax) (reg ret))
                   ,@(call 'car 'rax)
                   (assign (reg rbx) (reg ret)) ; Parsed value
                   ,@(call 'cdr 'rax)
                   (assign (reg rax) (reg ret)) ; Index after parsing
                   ,@(call 'caar 'rbx)
                   (assign (reg rcx) (reg ret)) ; CAAR of list
                   ,@(call 'caadr 'rbx)
                   (assign (reg rdx) (reg ret)) ; CAADR of list
                   ,@(call 'cddr 'rbx)))))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine rax))
    (+ test-read-buffer-offset (length exp)))
  (test-eqv (get-register-contents (get-machine-register machine rcx))
    (logior number-tag (caar l)))
  (test-eqv (get-register-contents (get-machine-register machine rdx))
    (logior number-tag (caadr l)))
  (test-eqv (get-register-contents (get-machine-register machine ret))
    empty-list))

;;; Test parse-list: '( ( 1) ( 2  )   )
(let* ((exp (string->list (format #f "~a" "( ( 1) ( 2  )   )")))
       (machine (make-test-machine
                 `((assign (reg rax) (const ,test-read-buffer-offset))
                   (assign (reg rbx) (const ,(+ test-read-buffer-offset (length exp))))
                   ,@(call 'parse-list 'rax 'rbx)
                   (assign (reg rax) (reg ret))
                   ,@(call 'car 'rax)
                   (assign (reg rbx) (reg ret)) ; Parsed value
                   ,@(call 'cdr 'rax)
                   (assign (reg rax) (reg ret)) ; Index after parsing
                   ,@(call 'caar 'rbx)
                   (assign (reg rcx) (reg ret)) ; CAAR of list
                   ,@(call 'caadr 'rbx)
                   (assign (reg rdx) (reg ret)) ; CAADR of list
                   ,@(call 'cddr 'rbx)))))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine rax))
    (+ test-read-buffer-offset (length exp)))
  (test-eqv (get-register-contents (get-machine-register machine rcx))
    (logior number-tag 1))
  (test-eqv (get-register-contents (get-machine-register machine rdx))
    (logior number-tag 2))
  (test-eqv (get-register-contents (get-machine-register machine ret))
    empty-list))

;;; Test parse-list failures
(for-each
 (lambda (test-case)
   (let* ((exp (string->list (format #f "~a" test-case)))
          (machine (make-test-machine
                    `((assign (reg rax) (const ,test-read-buffer-offset))
                      (assign (reg rbx) (const ,(+ test-read-buffer-offset (length exp))))
                      ,@(call 'parse-list 'rax 'rbx)
                      (assign (reg rax) (reg ret))))))
     (reset-machine machine)
     (write-memory (get-machine-memory machine)
                   test-read-buffer-offset
                   (map char->integer exp))
     (continue-machine machine)
     (test-eqv (get-register-contents (get-machine-register machine rax)) parse-failed-value)))
 '("(1"
   "((1)"
   ")"
   ""))

;;; Test parse-symbol success cases
(for-each
 (lambda (test-case)
   (let* ((test-case-str
           (if (pair? test-case)
               (car test-case)
               test-case))
          (test-case-parsed-count
           (if (pair? test-case)
               (cadr test-case)
               (string-length test-case)))
          (exp (string->list test-case-str))
          (machine (make-test-machine
                    `((assign (reg rax) (const ,test-read-buffer-offset))
                      (assign (reg rbx) (const ,(+ test-read-buffer-offset (length exp))))
                      ,@(call 'parse-symbol 'rax 'rbx)
                      (assign (reg rax) (reg ret))
                      ,@(call 'car 'rax)
                      (assign (reg rbx) (reg ret))
                      ,@(call 'cdr 'rax)
                      (assign (reg rax) (reg ret))))))
     (reset-machine machine)
     (write-memory (get-machine-memory machine)
                   test-read-buffer-offset
                   (map char->integer exp))
     (continue-machine machine)
     (test-eqv (get-register-contents (get-machine-register machine rax))
       (+ test-read-buffer-offset test-case-parsed-count))
     (test-eqv (logand tag-mask
                       (get-register-contents (get-machine-register machine rbx)))
       symbol-tag)))
 '("a"
   "a0"
   "a-0"
   ("a0)" 2)
   ("a0 " 2)))

;;; Test parse-symbol failure
(for-each
 (lambda (test-case-str)
   (let* ((exp (string->list test-case-str))
          (machine (make-test-machine
                    `((assign (reg rax) (const ,test-read-buffer-offset))
                      (assign (reg rbx) (const ,(+ test-read-buffer-offset (length exp))))
                      ,@(call 'parse-symbol 'rax 'rbx)
                      (assign (reg rax) (reg ret))))))
     (reset-machine machine)
     (write-memory (get-machine-memory machine)
                   test-read-buffer-offset
                   (map char->integer exp))
     (continue-machine machine)
     (test-eqv (get-register-contents (get-machine-register machine rax))
       parse-failed-value)))
 '("" "8" "8a"))

;;; Test parse-exp: '(a b c)
(let* ((max-num-pairs 128)
       (exp (string->list (format #f "~a" '(a b c))))
       (machine (make-test-machine
                 `((assign (reg rax) (const ,test-read-buffer-offset))
                   (assign (reg rbx) (const ,(+ test-read-buffer-offset (length exp))))
                   ,@(call 'parse-exp 'rax 'rbx)
                   (assign (reg rax) (reg ret))
                   ,@(call 'car 'rax)
                   (assign (reg rax) (reg ret)) ; Parsed value
                   ,@(call 'car 'rax)
                   (assign (reg rbx) (reg ret))
                   ,@(call 'cadr 'rax)
                   (assign (reg rcx) (reg ret))
                   ,@(call 'caddr 'rax)
                   (assign (reg rdx) (reg ret)))
                 #:max-num-pairs max-num-pairs)))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (let ((rbx-value (get-register-contents (get-machine-register machine rbx)))
        (rcx-value (get-register-contents (get-machine-register machine rcx)))
        (rdx-value (get-register-contents (get-machine-register machine rdx))))
    (test-eqv (logand tag-mask rbx-value) symbol-tag)
    (test-eqv (logand tag-mask rcx-value) symbol-tag)
    (test-eqv (logand tag-mask rdx-value) symbol-tag)
    (test-assert (not (= rbx-value rcx-value)))
    (test-assert (not (= rbx-value rdx-value)))
    (test-assert (not (= rcx-value rdx-value)))))

;;; Test parse-exp: '(a b a)
(let* ((max-num-pairs 128)
       (exp (string->list (format #f "~a" '(a b a))))
       (machine (make-test-machine
                 `((assign (reg rax) (const ,test-read-buffer-offset))
                   (assign (reg rbx) (const ,(+ test-read-buffer-offset (length exp))))
                   ,@(call 'parse-exp 'rax 'rbx)
                   (assign (reg rax) (reg ret))
                   ,@(call 'car 'rax)
                   (assign (reg rax) (reg ret)) ; Parsed value
                   ,@(call 'car 'rax)
                   (assign (reg rbx) (reg ret))
                   ,@(call 'cadr 'rax)
                   (assign (reg rcx) (reg ret))
                   ,@(call 'caddr 'rax)
                   (assign (reg rdx) (reg ret)))
                 #:max-num-pairs max-num-pairs)))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (let ((rbx-value (get-register-contents (get-machine-register machine rbx)))
        (rcx-value (get-register-contents (get-machine-register machine rcx)))
        (rdx-value (get-register-contents (get-machine-register machine rdx))))
    (test-eqv (logand tag-mask rbx-value) symbol-tag)
    (test-eqv (logand tag-mask rcx-value) symbol-tag)
    (test-eqv (logand tag-mask rdx-value) symbol-tag)
    (test-assert (not (= rbx-value rcx-value)))
    (test-assert (not (= rcx-value rdx-value)))
    (test-eqv rbx-value rdx-value)))

;;; Test parse-exp: '(a aa)
(let* ((max-num-pairs 128)
       (exp (string->list (format #f "~a" '(a b a))))
       (machine (make-test-machine
                 `((assign (reg rax) (const ,test-read-buffer-offset))
                   (assign (reg rbx) (const ,(+ test-read-buffer-offset (length exp))))
                   ,@(call 'parse-exp 'rax 'rbx)
                   (assign (reg rax) (reg ret))
                   ,@(call 'car 'rax)
                   (assign (reg rax) (reg ret)) ; Parsed value
                   ,@(call 'car 'rax)
                   (assign (reg rbx) (reg ret))
                   ,@(call 'cadr 'rax)
                   (assign (reg rcx) (reg ret)))
                 #:max-num-pairs max-num-pairs)))
  (reset-machine machine)
  (write-memory (get-machine-memory machine)
                test-read-buffer-offset
                (map char->integer exp))
  (continue-machine machine)
  (let ((rbx-value (get-register-contents (get-machine-register machine rbx)))
        (rcx-value (get-register-contents (get-machine-register machine rcx))))
    (test-eqv (logand tag-mask rbx-value) symbol-tag)
    (test-eqv (logand tag-mask rcx-value) symbol-tag)
    (test-assert (not (= rbx-value rcx-value)))))

(test-end "asm-interpreter-test")
