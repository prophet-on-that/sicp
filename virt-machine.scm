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

;;; Machine

;;; User programs can interact directly with REGISTERS and MEMORY, but
;;; only indirectly with the PC, FLAG and SP registers.
(define (make-machine n-registers n-memory-slots)
  (let ((pc (make-register))
        (flag (make-register))
        (sp (make-register))
        (registers (make-vector n-registers))
        (memory (make-memory n-memory-slots))
        (instruction-sequence '())
        (ops (list
              (list '+ +)
              (list '- -))))

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

    (define (get-register k)
      (vector-ref registers k))

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

    dispatch))

(define (start-machine machine)
  (machine 'start))

(define (install-machine-instruction-sequence! machine insts)
  ((machine 'install-instruction-sequence!) insts))

(define (get-machine-pc machine)
  (machine 'get-pc))

(define (get-machine-flag machine)
  (machine 'get-flag))

(define (get-machine-sp machine)
  (machine 'get-sp))

(define (get-machine-registers machine)
  (machine 'get-registers))

(define (get-machine-register machine k)
  ((machine 'get-register) k))

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
        ;; ((eq? (car inst) 'test)
        ;;  #f)
        ;; ((eq? (car inst) 'branch)
        ;;  #f)
        ;; ((eq? (car inst) 'goto)
        ;;  #f)
        ;; ((eq? (car inst) 'perform)
        ;;  #f)
        ;; ((eq? (car inst) 'load)
        ;;  #f)
        ;; ((eq? (car inst) 'store)
        ;;  #f)
        ;; ((eq? (car inst) 'save)
        ;;  #f)
        ;; ((eq? (car inst) 'restore)
        ;;  #f)
        (else
         (error "Unknown instruction -- ASSEMBLE" inst))))

(define (advance-pc machine)
  (let ((pc (get-machine-pc machine)))
    (set-register-contents! pc (cdr (get-register-contents pc)))))

(define (make-assign inst machine labels)
  (let ((reg-name (assign-reg-name inst)))
    (let ((target (get-machine-register machine reg-name))
          (value-exp (assign-value-exp inst)))
      (let ((value-proc
             (if (operation-exp? value-exp)
                 (make-operation-exp value-exp machine labels)
                 (make-primitive-exp (car value-exp) machine labels))))
        (lambda ()
          (set-register-contents! target (value-proc))
          (advance-pc machine))))))

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
  (tagged-list? exp 'const))

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

(test-end "virt-machine-test")
