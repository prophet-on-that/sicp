(define-module (sicp virt-machine))

(use-modules (srfi srfi-43)
             (srfi srfi-64)
             (srfi srfi-1)
             (sicp eval-utils))

;;; Register

(define (make-register)
  (let ((contents '*unassigned*))
    (define (dispatch message)
      (cond ((eq? message 'get) contents)
            ((eq? message 'set!)
             (lambda (val)
               (set! contents val)))
            (else
             (error "Unknown message -- REGISTER" message))))
    dispatch))

(define-public (get-register-contents register)
  (register 'get))

(define-public (set-register-contents! register val)
  ((register 'set!) val))

;;; Memory

(define (make-memory n-memory-slots)
  (let ((memory (make-vector n-memory-slots)))
    (define (dispatch message)
      (cond ((eq? message 'get)
             (lambda (k)
               (if (and (>= k 0)
                        (< k n-memory-slots))
                   (vector-ref memory k)
                   (error "Index out of range -- GET-MEMORY" k))))
            ((eq? message 'set)
             (lambda (k val)
               (if (and (>= k 0)
                        (< k n-memory-slots))
                   (vector-set! memory k val)
                   (error "Index out of range -- SET-MEMORY" k))))
            (else
             (error "Unknown message -- MEMORY" message))))
    dispatch))

(define-public (set-memory! memory slot val)
  ((memory 'set) slot val))

(define-public (get-memory memory slot)
  ((memory 'get) slot))

;;; Machine

;;; User programs can interact directly with all registers except FLAG.
;;;
;;; Calling convention: push arguments in reverse order and CALL,
;;; first argument in [bp + 2] etc. Caller must save register 0 as
;;; used for return value (callee must save all other registers).
(define-public (make-machine n-registers n-memory-slots)
  (let ((pc (make-register))
        (flag (make-register))
        (sp (make-register))
        (bp (make-register))
        (registers (make-vector n-registers))
        (memory (make-memory n-memory-slots))
        (instruction-sequence '())
        (ops (list
              (list '+ +)
              (list '- -)
              (list '* *)
              (list '= =)
              (list '<= <=)
              (list 'logand logand)
              (list 'logior logior)))
        (trace #f))

    (define (start)
      (set-register-contents! pc instruction-sequence)
      (execute))

    (define (execute)
      (let ((insts (get-register-contents pc)))
        (if (null? insts)
            'done
            (let ((next-inst (car insts)))
              (if trace
                  (begin
                    (display "trace: ")
                    (display (instruction-text next-inst))
                    (newline)))
              ((instruction-execution-proc next-inst))
              (execute)))))

    (define (install-instruction-sequence! insts)
      (set! instruction-sequence insts))

    (define (get-register reg)
      (cond ((eq? reg 'sp) sp)
            ((eq? reg 'pc) pc)
            ((eq? reg 'bp) bp)
            ((number? reg)
             (vector-ref registers reg))
            (else
             (error "Invalid register -- GET-REGISTER" reg))))

    (define (set-trace b)
      (set! trace b))

    (define (dispatch message)
      (cond ((eq? message 'start)
             (start))
            ((eq? message 'install-instruction-sequence!)
             install-instruction-sequence!)
            ((eq? message 'get-flag) flag)
            ((eq? message 'get-sp) sp)
            ((eq? message 'get-registers) registers)
            ((eq? message 'get-register) get-register)
            ((eq? message 'get-memory) memory)
            ((eq? message 'get-ops) ops)
            ((eq? message 'set-trace) set-trace)
            (else
             (error "Unrecognised message -- MACHINE" message))))

    ;; Assign registers
    (vector-for-each
     (lambda (i _)
       (vector-set! registers i (make-register)))
     registers)

    ;; Assign sp
    (set-register-contents! sp n-memory-slots)

    dispatch))

(define-public (start-machine machine)
  (machine 'start))

(define-public (install-machine-instruction-sequence! machine insts)
  ((machine 'install-instruction-sequence!) insts))

(define-public (get-machine-flag machine)
  (machine 'get-flag))

(define-public (get-machine-registers machine)
  (machine 'get-registers))

(define-public (get-machine-register machine reg)
  ((machine 'get-register) reg))

(define-public (get-machine-memory machine)
  (machine 'get-memory))

(define-public (get-machine-ops machine)
  (machine 'get-ops))

(define-public (set-machine-trace machine b)
  ((machine 'set-trace) b))

;;; Assembler

(define (make-instruction instruction-text)
  (list instruction-text #f))

(define (instruction-text inst)
  (car inst))

(define (instruction-execution-proc inst)
  (cadr inst))

(define (set-instruction-execution-proc! inst proc)
  (set-car! (cdr inst) proc))

(define (make-label name insts)
  (cons name insts))

(define (label-name label)
  (car label))

(define (label-inst label)
  (cdr label))

(define-public (assemble controller-text machine)
  (preprocess controller-text
              '()
              (lambda (text)
                (extract-labels text
                                (lambda (insts labels)
                                  (update-insts! insts labels machine)
                                  insts)))))

(define (preprocess text aliases cont)
  (if (null? text)
      (cont '())
      (let ((next-inst (car text)))
        (if (tagged-list? next-inst 'alias)
            (preprocess (cdr text)
                        (acons (alias-value next-inst)
                               (alias-target next-inst)
                               aliases)
                        cont)
            (preprocess
             (cdr text)
             aliases
             (lambda (insts)
               (cont
                (cons (replace-aliases next-inst aliases)
                      insts))))))))

(define (replace-aliases inst aliases)
  (if (list? inst)
      (map
       (lambda (sub-expr)
         (if (and (pair? sub-expr)
                  (register-exp? sub-expr))
             (let ((mapped (assoc (register-exp-reg sub-expr)
                                  aliases)))
               (list 'reg
                     (if mapped
                         (cdr mapped)
                         (register-exp-reg sub-expr))))
             sub-expr))
       inst)
      inst))

(define (alias-target inst)
  (cadr inst))

(define (alias-value inst)
  (caddr inst))

(define (extract-labels text cont)
  (if (null? text)
      (cont '() '())
      (let ((next-inst (car text)))
        (if (symbol? next-inst)
            (extract-labels (cdr text)
                            (lambda (insts labels)
                              (if (assoc next-inst labels)
                                  (error "Label already seen -- ASSEMBLE" next-inst)
                                  (cont insts (cons (make-label next-inst insts)
                                                    labels)))))
            (extract-labels (cdr text)
                            (lambda (insts labels)
                              (cont (cons (make-instruction next-inst) insts)
                                    labels)))))))

(define (lookup-label labels label-name)
  (let ((val (assoc label-name labels)))
    (if val
        (cdr val)
        (error "Undefined label -- ASSEMBLE" label-name))))

(define (update-insts! insts labels machine)
  (for-each
   (lambda (inst)
     (set-instruction-execution-proc!
      inst
      (make-execution-procedure (instruction-text inst) machine labels)))
   insts))

(define (make-execution-procedure inst machine labels)
  (cond ((eq? (car inst) 'assign)
         (make-assign inst machine labels))
        ((eq? (car inst) 'test)
         (make-test inst machine labels))
        ((eq? (car inst) 'jez)
         (make-jez inst machine labels))
        ((eq? (car inst) 'jne)
         (make-jne inst machine labels))
        ((eq? (car inst) 'goto)
         (make-goto inst machine labels))
        ;; ((eq? (car inst) 'perform)
        ;;  #f)
        ((eq? (car inst) 'mem-store)
         (make-mem-store inst machine labels))
        ((eq? (car inst) 'mem-load)
         (make-mem-load inst machine labels))
        ((eq? (car inst) 'stack-push)
         (make-stack-push inst machine labels))
        ((eq? (car inst) 'stack-pop)
         (make-stack-pop inst machine labels))
        ((eq? (car inst) 'call)
         (make-call inst machine labels))
        ((eq? (car inst) 'ret)
         (make-ret inst machine labels))
        ((eq? (car inst) 'error)
         (make-error-instruction inst machine labels))
        (else
         (error "Unknown instruction -- ASSEMBLE" inst))))

(define (advance-pc pc)
  (set-register-contents! pc (cdr (get-register-contents pc))))

(define (make-assign inst machine labels)
  (if (register-exp? (assign-reg inst))
      (let ((reg-name (register-exp-reg (assign-reg inst))))
        (let ((target (get-machine-register machine reg-name))
              (value-exp (assign-value-exp inst)))
          (let ((value-proc
                 (if (operation-exp? value-exp)
                     (make-operation-exp value-exp machine labels)
                     (make-primitive-exp (car value-exp) machine labels)))
                (pc (get-machine-register machine 'pc)))
            (lambda ()
              (set-register-contents! target (value-proc))
              (advance-pc pc)))))
      (error
       "Bad ASSIGN instruction -- ASSEMBLE" inst)))

(define (assign-reg assign-instruction)
  (cadr assign-instruction))

(define (assign-value-exp assign-instruction)
  (cddr assign-instruction))

;;; Primitive expressions

(define (make-primitive-exp exp machine labels)
  (cond ((constant-exp? exp)
         (let ((c (constant-exp-value exp)))
           (lambda () c)))
        ((label-exp? exp)
         (let ((insts
                (lookup-label labels
                              (label-exp-label exp))))
           (lambda () insts)))
        ((register-exp? exp)
         (let ((reg-name (register-exp-reg exp)))
           (let ((r (get-machine-register machine reg-name)))
             (lambda ()
               (get-register-contents r)))))
        (else
         (error "Unknown expression type -- ASSEMBLE" exp))))

(define (register-exp? exp)
  (tagged-list? exp 'reg))

(define (register-exp-reg exp)
  (cadr exp))

(define (constant-exp? exp)
  (and (tagged-list? exp 'const)
       (number? (constant-exp-value exp))))

(define (constant-exp-value exp)
  (cadr exp))

(define (label-exp? exp)
  (tagged-list? exp 'label))

(define (label-exp-label exp)
  (cadr exp))

;;; Operation expressions

(define (make-operation-exp exp machine labels)
  (let ((op (lookup-machine-prim machine (operation-exp-op exp)))
        (aprocs
         (map (lambda (e)
                (if (label-exp? e)
                    (error "Unexpected label expression -- ASSEMBLE" e)
                    (make-primitive-exp e machine labels)))
              (operation-exp-operands exp))))
    (lambda ()
      (apply op (map (lambda (p) (p)) aprocs)))))

(define (operation-exp? exp)
  (and (pair? exp) (tagged-list? (car exp) 'op)))

(define (operation-exp-op operation-exp)
  (cadr (car operation-exp)))

(define (operation-exp-operands operation-exp)
  (cdr operation-exp))

(define (lookup-machine-prim machine symbol)
  (let ((val (assoc symbol (get-machine-ops machine))))
    (if val
        (cadr val)
        (error "Unknown operation -- ASSEMBLE" symbol))))

;;; Test

(define (make-test inst machine labels)
  (let ((condition (test-condition inst)))
    (if (operation-exp? condition)
        (let ((condition-proc
               (make-operation-exp condition machine labels))
              (flag (get-machine-flag machine))
              (pc (get-machine-register machine 'pc)))
          (lambda ()
            (set-register-contents! flag (if (condition-proc) 1 0))
            (advance-pc pc)))
        (error "Bad TEST instruction -- ASSEMBLE" inst))))

(define (test-condition test-instruction)
  (cdr test-instruction))

;;; Jez

(define (make-jez inst machine labels)
  (let ((dest (jez-dest inst)))
    (if (label-exp? dest)
        (let ((insts (lookup-label labels (label-exp-label dest)))
              (flag (get-machine-flag machine))
              (pc (get-machine-register machine 'pc)))
          (lambda ()
            (if (= 0 (get-register-contents flag))
                (set-register-contents! pc insts)
                (advance-pc pc))))
        (error "Bad JEZ instruction -- ASSEMBLE" inst))))

(define (jez-dest inst)
  (cadr inst))

;;; Jne

(define (make-jne inst machine labels)
  (let ((dest (jne-dest inst)))
    (if (label-exp? dest)
        (let ((insts (lookup-label labels (label-exp-label dest)))
              (flag (get-machine-flag machine))
              (pc (get-machine-register machine 'pc)))
          (lambda ()
            (if (not (= 0 (get-register-contents flag)))
                (set-register-contents! pc insts)
                (advance-pc pc))))
        (error "Bad JNE instruction -- ASSEMBLE" inst))))

(define (jne-dest inst)
  (cadr inst))

;;; Branch

(define (make-goto inst machine labels)
  (let ((dest (goto-dest inst)))
    (cond ((label-exp? dest)
           (let ((insts (lookup-label labels (label-exp-label dest)))
                 (pc (get-machine-register machine 'pc)))
             (lambda ()
               (set-register-contents! pc insts))))
          ((register-exp? dest)
           (let ((reg (get-machine-register machine (register-exp-reg dest)))
                 (pc (get-machine-register machine 'pc)))
             (lambda ()
               (set-register-contents! pc (get-register-contents reg)))))
          (else
           (error "Bad GOTO instruction -- ASSEMBLE" inst)))))

(define (goto-dest inst)
  (cadr inst))

;;; Mem-store

;;; The MEM-STORE instruciton supports storing constant expressions
;;; (not labels) or values in registers in memory.
(define (make-mem-store inst machine labels)
  (let* ((slot-exp (mem-store-slot inst))
         (slot-proc
          (cond ((not (label-exp? slot-exp))
                 (make-primitive-exp slot-exp machine labels))
                (else
                 (error "Bad MEM-STORE instruction -- ASSEMBLE" inst))))
         (val-proc (make-primitive-exp (mem-store-val inst) machine labels))
         (memory (get-machine-memory machine))
         (pc (get-machine-register machine 'pc)))
    (lambda ()
      (set-memory! memory (slot-proc) (val-proc))
      (advance-pc pc))))

(define (mem-store-slot inst)
  (cadr inst))

(define (mem-store-val inst)
  (caddr inst))

;;; Mem-load

;;; Slot may be a primitive or operator expression, but not a label.
(define (make-mem-load inst machine labels)
  (let* ((pc (get-machine-register machine 'pc))
        (memory (get-machine-memory machine))
        (reg (get-machine-register machine (register-exp-reg (mem-load-reg inst))))
        (slot-exp (mem-load-slot-exp inst))
        (slot-proc
         (cond ((operation-exp? slot-exp)
                (make-operation-exp slot-exp machine labels))
               ((and (pair? slot-exp)
                     (or (constant-exp? (car slot-exp))
                         (register-exp? (car slot-exp))))
                (make-primitive-exp (car slot-exp) machine labels))
               (else "Bad MEM-LOAD instruction" inst))))
    (lambda ()
      (set-register-contents! reg (get-memory memory (slot-proc)))
      (advance-pc pc))))

(define (mem-load-reg inst)
  (cadr inst))

(define (mem-load-slot-exp inst)
  (cddr inst))

;;; Stack push

(define (make-stack-push inst machine labels)
  (let ((sp (get-machine-register machine 'sp))
        (proc (make-primitive-exp (stack-push-value inst) machine labels))
        (memory (get-machine-memory machine))
        (pc (get-machine-register machine 'pc)))
    (lambda ()
      (set-register-contents! sp (1- (get-register-contents sp)))
      (set-memory! memory (get-register-contents sp) (proc))
      (advance-pc pc))))

(define (stack-push-value inst)
  (cadr inst))

;;; Stack pop

(define (make-stack-pop inst machine labels)
  (let ((sp (get-machine-register machine 'sp))
        (memory (get-machine-memory machine))
        (pc (get-machine-register machine 'pc)))
    (cond ((and (pair? (cdr inst))
                (register-exp? (stack-pop-target inst)))
           (let ((target
                   (get-machine-register machine (register-exp-reg (stack-pop-target inst)))))
             (lambda ()
               (set-register-contents! target
                                       (get-memory memory (get-register-contents sp)))
               (set-register-contents! sp
                                       (1+ (get-register-contents sp)))
               (advance-pc pc))))
          ((null? (cdr inst))
           (lambda ()
             (set-register-contents! sp
                                     (1+ (get-register-contents sp)))
             (advance-pc pc)))
          (else
           (error "Bad STACK-POP instruction" inst)))))

(define (stack-pop-target inst)
  (cadr inst))

;;; Call

(define (make-call inst machine labels)
  (let ((pc (get-machine-register machine 'pc))
        (memory (get-machine-memory machine))
        (sp (get-machine-register machine 'sp))
        (bp (get-machine-register machine 'bp))
        (next-inst (lookup-label labels (call-target inst))))
    (lambda ()
      (let ((current-sp (get-register-contents sp)))
        (set-memory! memory (1- current-sp) (cdr (get-register-contents pc)))
        (set-memory! memory (- current-sp 2) (get-register-contents bp))
        (set-register-contents! sp (- current-sp 2))
        (set-register-contents! bp (- current-sp 2))
        (set-register-contents! pc next-inst)))))

(define (call-target inst)
  (cadr inst))

;;; Ret

(define (make-ret inst machine labels)
  (let ((pc (get-machine-register machine 'pc))
        (memory (get-machine-memory machine))
        (sp (get-machine-register machine 'sp))
        (bp (get-machine-register machine 'bp)))
    (lambda ()
      (set-register-contents! sp
                              (get-register-contents bp))
      (let ((current-sp (get-register-contents sp)))
        (set-register-contents! bp
                                (get-memory memory current-sp))
        (set-register-contents! pc
                                (get-memory memory (1+ current-sp)))
        (set-register-contents! sp
                                (+ current-sp 2))))))

;;; Error

(define (make-error-instruction inst machine labels)
  (let ((error-code-exp (error-inst-code inst)))
    (if (constant-exp? error-code-exp)
        (let ((error-code (constant-exp-value error-code-exp)))
          (lambda ()
            (error "The program has exited with an error" error-code)))
        (error "Invalid ERROR instruction" inst))))

(define (error-inst-code inst)
  (cadr inst))

;;; Utilities

(define-public (make-machine-load-text n-registers n-memory-slots controller-text)
  (let ((machine (make-machine n-registers n-memory-slots)))
    (let ((insts (assemble controller-text machine)))
      (install-machine-instruction-sequence! machine insts)
      machine)))

;;; Test suite

(test-begin "virt-machine-test")

;;; Test primitive assignment of constant
(let ((machine
       (make-machine-load-text 1 0 '((assign (reg 0) (const 0))))))
  (start-machine machine)
  (let ((register (get-machine-register machine 0)))
    (test-eqv (get-register-contents register) 0)))

;;; Test primitive assignment to multiple registers
(let ((machine
       (make-machine-load-text 2 0 '((assign (reg 0) (const 0))
                                     (assign (reg 1) (const 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 0)
  (test-eqv (get-register-contents (get-machine-register machine 1)) 1))

;;; Test primitive assignment and update
(let ((machine
       (make-machine-load-text 1 0 '((assign (reg 0) (const 0))
                                     (assign (reg 0) (const 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 1))

;;; Test primitive assignment of label
(let ((machine
       (make-machine-load-text 1 0 '(label
                                     (assign (reg 0) (label label))))))
  (start-machine machine)
  (let ((insts (get-register-contents (get-machine-register machine 0))))
    (test-assert (and (pair? insts)
                      (= (length insts) 1)))))

;;; Test constant operator assignment
(let ((machine
       (make-machine-load-text 1 0 '((assign (reg 0) (op +) (const 1) (const 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 2))

;;; Test register operator assignment
(let ((machine
       (make-machine-load-text 3 0 '((assign (reg 0) (const 1))
                                     (assign (reg 1) (const 2))
                                     (assign (reg 2) (op +) (reg 0) (reg 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 2)) 3))

;;; Test const and register operator assignment
(let ((machine
       (make-machine-load-text 2 0 '((assign (reg 0) (const 1))
                                     (assign (reg 1) (op +) (reg 0) (const 2))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 1)) 3))

;;; Test assignment involving stack pointer
(let ((machine
       (make-machine-load-text 1 8 '((assign (reg sp) (const 10))
                                     (assign (reg 0) (op +) (const 1) (reg sp))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 'sp)) 10)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 11))

;;; Test test instruction: true
(let ((machine
       (make-machine-load-text 1 0 '((assign (reg 0) (const 1))
                                     (test (op =) (reg 0) (const 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-flag machine)) 1))

;;; Test test instruction: false
(let ((machine
       (make-machine-load-text 1 0 '((assign (reg 0) (const 0))
                                     (test (op =) (reg 0) (const 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-flag machine)) 0))

;;; Test jez instruction: true
(let ((machine
       (make-machine-load-text 1 0 '((assign (reg 0) (const 0))
                                     (test (op =) (const 0) (const 1)) ; False
                                     (jez (label end))
                                     (assign (reg 0) (const 1)) ; Should not be executed
                                     end))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 0))

;;; Test jez instruction: false
(let ((machine
       (make-machine-load-text 1 0 '((assign (reg 0) (const 0))
                                     (test (op =) (const 0) (const 0)) ; True
                                     (jez (label end))
                                     (assign (reg 0) (const 1)) ; Should be executed
                                     end))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 1))

;;; Test jne instruction: true
(let ((machine
       (make-machine-load-text 1 0 '((assign (reg 0) (const 0))
                                     (test (op =) (const 0) (const 0)) ; True
                                     (jne (label end))
                                     (assign (reg 0) (const 1)) ; Should not be executed
                                     end))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 0))

;;; Test jne instruction: false
(let ((machine
       (make-machine-load-text 1 0 '((assign (reg 0) (const 0))
                                     (test (op =) (const 0) (const 1)) ; False
                                     (jne (label end))
                                     (assign (reg 0) (const 1)) ; Should be executed
                                     end))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 1))

;;; Test goto instruction: label
(let ((machine
       (make-machine-load-text 1 0 '((assign (reg 0) (const 0))
                                     (goto (label end))
                                     (assign (reg 0) (const 1)) ; Should not be executed
                                     end))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 0))

;;; Test goto instruction: register
(let ((machine
       (make-machine-load-text 2 0 '((assign (reg 0) (const 0))
                                     (assign (reg 1) (label end))
                                     (goto (reg 1))
                                     (assign (reg 0) (const 1)) ; Should not be executed
                                     end))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 0))

;;; Test mem-store: slot and val both from registers
(let ((machine
       (make-machine-load-text 2 8 '((assign (reg 0) (const 1)) ; Slot
                                     (assign (reg 1) (const 2)) ; Val
                                     (mem-store (reg 0) (reg 1))))))
  (start-machine machine)
  (test-eqv (get-memory (get-machine-memory machine) 1) 2))

;;; Test mem-store: slot from register, val constant
(let ((machine
       (make-machine-load-text 1 8 '((assign (reg 0) (const 1)) ; Slot
                                     (mem-store (reg 0) (const 1))))))
  (start-machine machine)
  (test-eqv (get-memory (get-machine-memory machine) 1) 1))

;;; Test mem-store: slot constant, val from register
(let ((machine
       (make-machine-load-text 1 8 '((assign (reg 0) (const 1)) ; Val
                                     (mem-store (const 2) (reg 0))))))
  (start-machine machine)
  (test-eqv (get-memory (get-machine-memory machine) 2) 1))

;;; Test mem-store: slot and val constant
(let ((machine
       (make-machine-load-text 1 8 '((mem-store (const 2) (const 10))))))
  (start-machine machine)
  (test-eqv (get-memory (get-machine-memory machine) 2) 10))

;;; Test mem-store: val label
(let ((machine
       (make-machine-load-text 1 8 '((mem-store (const 2) (const 10))))))
  (start-machine machine)
  (test-eqv (get-memory (get-machine-memory machine) 2) 10))

;;; Test mem-load: slot from register
(let ((machine
       (make-machine-load-text 2 8 '((assign (reg 0) (const 0))
                                     (mem-store (reg 0) (const 10))
                                     (mem-load (reg 1) (reg 0))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 1)) 10))

;;; Test mem-load: slot constant
(let ((machine
       (make-machine-load-text 1 8 '((mem-store (const 0) (const 10))
                                     (mem-load (reg 0) (const 0))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 10))

;;; Test stack push
(let ((machine
       (make-machine-load-text 1 8 '((assign (reg 0) (const 1))
                                     (stack-push (reg 0))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 'sp)) 7)
  (test-eqv (get-memory (get-machine-memory machine) 7) 1))

;;; Test mem-load: slot operator expression
(let ((machine
       (make-machine-load-text 1 8 '((stack-push (const 10))
                                     (stack-push (const 15))
                                     (mem-load (reg 0) (op +) (reg sp) (const 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 10))

;;; Test stack pop
(let ((machine
       (make-machine-load-text 2 8 '((assign (reg 0) (const 1))
                                     (stack-push (reg 0))
                                     (stack-pop (reg 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 'sp)) 8)
  (test-eqv (get-register-contents (get-machine-register machine 1)) 1))

;;; Test stack pop, discarding result
(let ((machine
       (make-machine-load-text 2 8 '((stack-push (const 0))
                                     (stack-pop)))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 'sp)) 8))

;;; Test alias
(let ((machine
       (make-machine-load-text 2 0 '((alias 0 n)
                                     (assign (reg n) (const 0))
                                     (alias 1 n)
                                     (assign (reg n) (const 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 0)
  (test-eqv (get-register-contents (get-machine-register machine 1)) 1))

;;; Test call and ret
(let ((machine
       (make-machine-load-text 4 16 '((goto (label start))
                                      sub
                                      (assign (reg 0) (const 1))
                                      (ret)
                                      start
                                      (call sub)))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 1))

(let ((machine
       (make-machine-load-text 4 16 '((goto (label start))
                                      sub
                                      (mem-load (reg 0) (op +) (reg bp) (const 2)) ; arg 1
                                      (mem-load (reg 1) (op +) (reg bp) (const 3)) ; arg 2
                                      (assign (reg 0) (op +) (reg 0) (reg 1))
                                      (ret)
                                      start
                                      (stack-push (const 2))
                                      (stack-push (const 1))
                                      (call sub)))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 3))

;;; Test error
(let ((machine
       (make-machine-load-text 0 0 '((error (const 1))))))
  (test-error #t (start-machine machine)))

;;; Test factorial iterative implementation
(let* ((code
       ;; Assume register 0 holds n, output n! into register 1
       '((assign (reg 1) (const 1))
         before-test
         (test (op <=) (reg 0) (const 1))
         (jne (label after-loop))
         (assign (reg 1) (op *) (reg 0) (reg 1))
         (assign (reg 0) (op -) (reg 0) (const 1))
         (goto (label before-test))
         after-loop))
       (machine (make-machine-load-text 2 0 code))
       (reg0 (get-machine-register machine 0))
       (reg1 (get-machine-register machine 1)))
  (set-register-contents! reg0 5)
  (start-machine machine)
  (test-eqv (get-register-contents reg1) 120))

;;; Test factorial recursive implementation
(let* ((code
        ;; Input: n in register 0
        ;; Ouput: n! in register 1
        '((alias 0 n)
          (alias 1 ret)
          (alias 2 continue)
          (assign (reg continue) (label fact-end))
          factorial-test
          (test (op <=) (reg n) (const 1))
          (jne (label base-case))
          (stack-push (reg n))          ; Save n
          (stack-push (reg continue))   ; Save continue register
          (assign (reg continue) (label after-recursion))
          (assign (reg n) (op -) (reg n) (const 1))
          (goto (label factorial-test))
          after-recursion
          (stack-pop (reg continue))                 ; Restore continue
          (stack-pop (reg n))                        ; Restore n
          (assign (reg ret) (op *) (reg n) (reg 1))
          (goto (reg continue))
          base-case
          (assign (reg ret) (const 1))
          (goto (reg continue))
          fact-end))
       (machine (make-machine-load-text 4 512 code))
       (reg0 (get-machine-register machine 0))
       (reg1 (get-machine-register machine 1)))
  (set-register-contents! reg0 5)
  (start-machine machine)
  (test-eqv (get-register-contents reg1) 120))

;;; Test factorial recursive implementation
(let ((machine
       (make-machine-load-text
        4
        512
        '((alias 0 ret)
          (alias 1 rax)
          (alias 2 rbx)
          (goto (label start))
          factorial
          (stack-push (reg rax))
          (stack-push (reg rbx))
          (mem-load (reg rax) (op +) (reg bp) (const 2)) ; n
          (test (op <=) (reg rax) (const 1))
          (jne (label base-case))
          (assign (reg rbx) (op -) (reg rax) (const 1)) ; n - 1
          (stack-push (reg rbx))
          (call factorial)
          (stack-pop)
          (assign (reg rbx) (reg ret)) ; (n - 1)!
          (assign (reg ret) (op *) (reg rax) (reg rbx))
          (goto (label factorial-end))
          base-case
          (assign (reg ret) (reg rax))
          factorial-end
          (stack-pop (reg rbx))
          (stack-pop (reg rax))
          (ret)                         ; return n
          start
          (stack-push (const 5))
          (call factorial)))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 120))

(test-end "virt-machine-test")
