(define-module (sicp virt-machine))

(use-modules (srfi srfi-43)
             (srfi srfi-64)
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

(define (get-register-contents register)
  (register 'get))

(define (set-register-contents! register val)
  ((register 'set!) val))

;;; Memory

(define (make-memory n-memory-slots)
  (let ((memory (make-vector n-memory-slots)))
    (define (dispatch message)
      (cond ((eq? message 'get)
             (lambda (k)
               (vector-ref memory k)))
            ((eq? message 'set)
             (lambda (k val)
               (vector-set! memory k val)))
            (else
             (error "Unknown message -- MEMORY" message))))
    dispatch))

(define (set-memory! memory slot val)
  ((memory 'set) slot val))

(define (get-memory memory slot)
  ((memory 'get) slot))

;;; Machine

;;; User programs can interact directly with REGISTERS, SP and MEMORY, but
;;; only indirectly with the PC and FLAG registers.
(define (make-machine n-registers n-memory-slots)
  (let ((pc (make-register))
        (flag (make-register))
        (sp (make-register))
        (registers (make-vector n-registers))
        (memory (make-memory n-memory-slots))
        (instruction-sequence '())
        (ops (list
              (list '+ +)
              (list '- -)
              (list '= =))))

    (define (start)
      (set-register-contents! pc instruction-sequence)
      (execute))

    (define (execute)
      (let ((insts (get-register-contents pc)))
        (if (null? insts)
            'done
            (let ((next-inst (car insts)))
              ((instruction-execution-proc next-inst))
              (execute)))))

    (define (install-instruction-sequence! insts)
      (set! instruction-sequence insts))

    (define (get-register reg)
      (cond ((eq? reg 'sp) sp)
            ((number? reg)
             (vector-ref registers reg))
            (else
             (error "Invalid register -- GET-REGISTER" reg))))

    (define (dispatch message)
      (cond ((eq? message 'start)
             (start))
            ((eq? message 'install-instruction-sequence!)
             install-instruction-sequence!)
            ((eq? message 'get-pc) pc)
            ((eq? message 'get-flag) flag)
            ((eq? message 'get-sp) sp)
            ((eq? message 'get-registers) registers)
            ((eq? message 'get-register) get-register)
            ((eq? message 'get-memory) memory)
            ((eq? message 'get-ops) ops)))

    ;; Assign registers
    (vector-for-each
     (lambda (i _)
       (vector-set! registers i (make-register)))
     registers)

    ;; Assign sp
    (if (> n-memory-slots 0)
        (set-register-contents! sp (1- n-memory-slots)))

    dispatch))

(define (start-machine machine)
  (machine 'start))

(define (install-machine-instruction-sequence! machine insts)
  ((machine 'install-instruction-sequence!) insts))

(define (get-machine-pc machine)
  (machine 'get-pc))

(define (get-machine-flag machine)
  (machine 'get-flag))

(define (get-machine-registers machine)
  (machine 'get-registers))

(define (get-machine-register machine reg)
  ((machine 'get-register) reg))

(define (get-machine-memory machine)
  (machine 'get-memory))

(define (get-machine-ops machine)
  (machine 'get-ops))

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

(define (assemble controller-text machine)
  (extract-labels controller-text
                  (lambda (insts labels)
                    (update-insts! insts labels machine)
                    insts)))

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
        ;; ((eq? (car inst) 'save)
        ;;  #f)
        ;; ((eq? (car inst) 'restore)
        ;;  #f)
        (else
         (error "Unknown instruction -- ASSEMBLE" inst))))

(define (advance-pc pc)
  (set-register-contents! pc (cdr (get-register-contents pc))))

(define (make-assign inst machine labels)
  (let ((reg-name (assign-reg-name inst)))
    (let ((target (get-machine-register machine reg-name))
          (value-exp (assign-value-exp inst)))
      (let ((value-proc
             (if (operation-exp? value-exp)
                 (make-operation-exp value-exp machine labels)
                 (make-primitive-exp (car value-exp) machine labels)))
            (pc (get-machine-pc machine)))
        (lambda ()
          (set-register-contents! target (value-proc))
          (advance-pc pc))))))

(define (assign-reg-name assign-instruction)
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
              (pc (get-machine-pc machine)))
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
              (pc (get-machine-pc machine)))
          (lambda ()
            (if (= 0 (get-register-contents flag))
                (set-register-contents! pc insts)
                (advance-pc pc))))
        (error "Bad JEZ instruction -- ASSEMBLE"))))

(define (jez-dest inst)
  (cadr inst))

;;; Jne

(define (make-jne inst machine labels)
  (let ((dest (jne-dest inst)))
    (if (label-exp? dest)
        (let ((insts (lookup-label labels (label-exp-label dest)))
              (flag (get-machine-flag machine))
              (pc (get-machine-pc machine)))
          (lambda ()
            (if (not (= 0 (get-register-contents flag)))
                (set-register-contents! pc insts)
                (advance-pc pc))))
        (error "Bad JNE instruction -- ASSEMBLE"))))

(define (jne-dest inst)
  (cadr inst))

;;; Branch

(define (make-goto inst machine labels)
  (let ((dest (goto-dest inst)))
    (cond ((label-exp? dest)
           (let ((insts (lookup-label labels (label-exp-label dest)))
                 (pc (get-machine-pc machine)))
             (lambda ()
               (set-register-contents! pc insts))))
          ((register-exp? dest)
           (let ((reg (get-machine-register machine (register-exp-reg dest)))
                 (pc (get-machine-pc machine)))
             (lambda ()
               (set-register-contents! pc (get-register-contents reg)))))
          (else
           (error "Bad GOTO instruction -- ASSEMBLE")))))

(define (goto-dest inst)
  (cadr inst))

;;; Mem-store

;;; The MEM-STORE instruciton supports storing constant expressions
;;; (not labels) or values in registers in memory.
(define (make-mem-store inst machine labels)
  (let ((slot (mem-store-slot inst))
        (val (mem-store-val inst))
        (memory (get-machine-memory machine))
        (pc (get-machine-pc machine)))
    (cond ((and (register-exp? slot)
                (register-exp? val))
           ;; Read both slot and val at runtime
           (let ((slot-reg (get-machine-register machine (register-exp-reg slot)))
                 (val-reg (get-machine-register machine (register-exp-reg val))))
             (lambda ()
               (set-memory! memory (get-register-contents slot-reg) (get-register-contents val-reg))
               (advance-pc pc))))
          ((and (register-exp? slot)
                (constant-exp? val))
           ;; Read slot at runtime, value is constant
           (let ((slot-reg (get-machine-register machine (register-exp-reg slot)))
                 (value (constant-exp-value val)))
             (lambda ()
               (set-memory! memory (get-register-contents slot-reg) value)
               (advance-pc pc))))
          ((and (constant-exp? slot)
                (register-exp? val))
           ;; Read value at runtime, slot is constant
           (let ((slot-value (constant-exp-value slot))
                 (val-reg (get-machine-register machine (register-exp-reg val))))
             (lambda ()
               (set-memory! memory slot-value (get-register-contents val-reg))
               (advance-pc pc))))
          ((and (constant-exp? slot)
                (constant-exp? val))
           ;; Both slot and val are constant
           (let ((slot-val (constant-exp-value slot))
                 (value (constant-exp-value val)))
             (lambda ()
               (set-memory! memory slot-val value)
               (advance-pc pc))))
          (else
           (error "Bad MEM-STORE instruction" inst)))))

(define (mem-store-slot inst)
  (cadr inst))

(define (mem-store-val inst)
  (caddr inst))

;;; Mem-load

;;; Slot may be a constant or from a register
(define (make-mem-load inst machine labels)
  (let ((pc (get-machine-pc machine))
        (memory (get-machine-memory machine))
        (reg (get-machine-register machine (mem-load-reg inst)))
        (slot-exp (mem-load-slot inst)))
    (cond ((register-exp? slot-exp)
           ;; Load slot from register at runtime
           (let ((slot-reg (get-machine-register machine (register-exp-reg slot-exp))))
             (lambda ()
               (set-register-contents! reg (get-memory memory (get-register-contents slot-reg)))
               (advance-pc pc))))
          ((constant-exp? slot-exp)
           (let ((slot (constant-exp-value slot-exp)))
             (lambda ()
               (set-register-contents! reg (get-memory memory slot))
               (advance-pc pc))))
          (else
           (error "Bad MEM-LOAD instruction" inst)))))

(define (mem-load-reg inst)
  (cadr inst))

(define (mem-load-slot inst)
  (caddr inst))

;;; Utilities

(define (make-machine-load-text n-registers n-memory-slots controller-text)
  (let ((machine (make-machine n-registers n-memory-slots)))
    (let ((insts (assemble controller-text machine)))
      (install-machine-instruction-sequence! machine insts)
      machine)))

;;; Test suite

(test-begin "virt-machine-test")

;;; Test primitive assignment of constant
(let ((machine
       (make-machine-load-text 1 0 '((assign 0 (const 0))))))
  (start-machine machine)
  (let ((register (get-machine-register machine 0)))
    (test-eqv (get-register-contents register) 0)))

;;; Test primitive assignment to multiple registers
(let ((machine
       (make-machine-load-text 2 0 '((assign 0 (const 0))
                                     (assign 1 (const 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 0)
  (test-eqv (get-register-contents (get-machine-register machine 1)) 1))

;;; Test primitive assignment and update
(let ((machine
       (make-machine-load-text 1 0 '((assign 0 (const 0))
                                     (assign 0 (const 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 1))

;;; Test primitive assignment of label
(let ((machine
       (make-machine-load-text 1 0 '(label
                                     (assign 0 (label label))))))
  (start-machine machine)
  (let ((insts (get-register-contents (get-machine-register machine 0))))
    (test-assert (and (pair? insts)
                      (= (length insts) 1)))))

;;; Test constant operator assignment
(let ((machine
       (make-machine-load-text 1 0 '((assign 0 (op +) (const 1) (const 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 2))

;;; Test register operator assignment
(let ((machine
       (make-machine-load-text 3 0 '((assign 0 (const 1))
                                     (assign 1 (const 2))
                                     (assign 2 (op +) (reg 0) (reg 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 2)) 3))

;;; Test const and register operator assignment
(let ((machine
       (make-machine-load-text 2 0 '((assign 0 (const 1))
                                     (assign 1 (op +) (reg 0) (const 2))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 1)) 3))

;;; Test assignment involving stack pointer
(let ((machine
       (make-machine-load-text 1 8 '((assign sp (const 10))
                                     (assign 0 (op +) (const 1) (reg sp))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 'sp)) 10)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 11))

;;; Test test instruction: true
(let ((machine
       (make-machine-load-text 1 0 '((assign 0 (const 1))
                                     (test (op =) (reg 0) (const 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-flag machine)) 1))

;;; Test test instruction: false
(let ((machine
       (make-machine-load-text 1 0 '((assign 0 (const 0))
                                     (test (op =) (reg 0) (const 1))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-flag machine)) 0))

;;; Test jez instruction: true
(let ((machine
       (make-machine-load-text 1 0 '((assign 0 (const 0))
                                     (test (op =) (const 0) (const 1)) ; False
                                     (jez (label end))
                                     (assign 0 (const 1)) ; Should not be executed
                                     end))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 0))

;;; Test jez instruction: false
(let ((machine
       (make-machine-load-text 1 0 '((assign 0 (const 0))
                                     (test (op =) (const 0) (const 0)) ; True
                                     (jez (label end))
                                     (assign 0 (const 1)) ; Should be executed
                                     end))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 1))

;;; Test jne instruction: true
(let ((machine
       (make-machine-load-text 1 0 '((assign 0 (const 0))
                                     (test (op =) (const 0) (const 0)) ; True
                                     (jne (label end))
                                     (assign 0 (const 1)) ; Should not be executed
                                     end))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 0))

;;; Test jne instruction: false
(let ((machine
       (make-machine-load-text 1 0 '((assign 0 (const 0))
                                     (test (op =) (const 0) (const 1)) ; False
                                     (jne (label end))
                                     (assign 0 (const 1)) ; Should be executed
                                     end))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 1))

;;; Test goto instruction: label
(let ((machine
       (make-machine-load-text 1 0 '((assign 0 (const 0))
                                     (goto (label end))
                                     (assign 0 (const 1)) ; Should not be executed
                                     end))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 0))

;;; Test goto instruction: register
(let ((machine
       (make-machine-load-text 2 0 '((assign 0 (const 0))
                                     (assign 1 (label end))
                                     (goto (reg 1))
                                     (assign 0 (const 1)) ; Should not be executed
                                     end))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 0))

;;; Test mem-store: slot and val both from registers
(let ((machine
       (make-machine-load-text 2 8 '((assign 0 (const 1)) ; Slot
                                     (assign 1 (const 2)) ; Val
                                     (mem-store (reg 0) (reg 1))))))
  (start-machine machine)
  (test-eqv (get-memory (get-machine-memory machine) 1) 2))

;;; Test mem-store: slot from register, val constant
(let ((machine
       (make-machine-load-text 1 8 '((assign 0 (const 1)) ; Slot
                                     (mem-store (reg 0) (const 1))))))
  (start-machine machine)
  (test-eqv (get-memory (get-machine-memory machine) 1) 1))

;;; Test mem-store: slot constant, val from register
(let ((machine
       (make-machine-load-text 1 8 '((assign 0 (const 1)) ; Val
                                     (mem-store (const 2) (reg 0))))))
  (start-machine machine)
  (test-eqv (get-memory (get-machine-memory machine) 2) 1))

;;; Test mem-store: slot and val constant
(let ((machine
       (make-machine-load-text 1 8 '((mem-store (const 2) (const 10))))))
  (start-machine machine)
  (test-eqv (get-memory (get-machine-memory machine) 2) 10))

;;; Test mem-load: slot from register
(let ((machine
       (make-machine-load-text 2 8 '((assign 0 (const 0))
                                     (mem-store (reg 0) (const 10))
                                     (mem-load 1 (reg 0))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 1)) 10))

;;; Test mem-load: slot constant
(let ((machine
       (make-machine-load-text 1 8 '((mem-store (const 0) (const 10))
                                     (mem-load 0 (const 0))))))
  (start-machine machine)
  (test-eqv (get-register-contents (get-machine-register machine 0)) 10))

(test-end "virt-machine-test")
