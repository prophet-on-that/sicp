(define-module (sicp reg-machine))

(use-modules (sicp eval-utils))

(define-public make-machine
  (lambda* (register-names ops controller-text #:key (stack-mode 'normal))
    (let ((machine (make-new-machine stack-mode)))
      (for-each (lambda (register-name)
                  ((machine 'allocate-register) register-name))
                register-names)
      (machine 'initialise-stack-controller)
      ((machine 'install-operations) ops)
      ((machine 'install-instruction-sequence)
       (assemble controller-text machine))
      machine)))

;;; Registers

(define (make-register name)
  (let ((contents '*unassigned*))
    (define (dispatch message)
      (cond ((eq? message 'get) contents)
            ((eq? message 'set)
             (lambda (value) (set! contents value)))
            (else
             (error "Unknown request -- REGISTER" message))))
    dispatch))

(define (get-contents register)
  (register 'get))

(define (set-contents! register value)
  ((register 'set) value))

;;; Stack

(define (make-stack)
  (let ((s '()))
    (define (push x)
      (set! s (cons x s)))
    (define (pop)
      (if (null? s)
          (error "Empty stack -- POP")
          (let ((top (car s)))
            (set! s (cdr s))
            top)))
    (define (initialise)
      (set! s '())
      'done)
    (define (dispatch message)
      (cond ((eq? message 'push) push)
            ((eq? message 'pop) (pop))
            ((eq? message 'initialise) (initialise))
            (else (error "Unknown request -- STACK" message))))
    dispatch))

(define (stack-pop stack)
  (stack 'pop))

(define (stack-push stack value)
  ((stack 'push) value))

;;; Stack controller

(define (make-stack-controller stack-mode)
  (let ((stacks '()))
    (define (initialise registers)
      (cond ((or (eq? stack-mode 'normal)
                 (eq? stack-mode 'strict))
             (set! stacks (list (make-stack))))
            ((eq? stack-mode 'per-register)
             (set! stacks
                   (map (lambda (register)
                          (cons register (make-stack)))
                        registers)))
            (else
             (error "Unknown stack mode -- ASSEMBLER" stack-mode))))
    (define (push value register)
      (cond ((or (eq? stack-mode 'normal)
                 (eq? stack-mode 'strict))
             (if (null? stacks)
                 (error "Uninitisalised stack controller stacks -- ASSEMBLER")
                 (let ((stack (car stacks)))
                   (if (eq? stack-mode 'normal)
                       (stack-push stack value)
                       (stack-push stack (cons register value))))))
            ((eq? stack-mode 'per-register)
             (let ((pair (assoc register stacks)))
               (if pair
                   (stack-push (cdr pair) value)
                   (error "No stack for given register -- ASSEMBLER" register))))
            (else
             (error "Unknown stack mode -- ASSEMBLER" stack-mode))))
    (define (pop register)
      (cond ((or (eq? stack-mode 'normal)
                 (eq? stack-mode 'strict))
             (if (null? stacks)
                 (error "Uninitisalised stack controller stacks -- ASSEMBLER")
                 (let ((stack (car stacks)))
                   (let ((val (stack-pop stack)))
                     (if (eq? stack-mode 'normal)
                         val
                         (if (eq? register (car val))
                             (cdr val)
                             (error "Attempt to pop to an invalid register -- POP"
                                    (list (list 'given register)
                                          (list 'expected (car val))))))))))
            ((eq? stack-mode 'per-register)
             (let ((pair (assoc register stacks)))
               (if pair
                   (stack-pop (cdr pair))
                   (error "No stack for given register -- POP" register))))
            (else
             (error "Unknown stack mode -- POP" stack-mode))))
    (define (dispatch message)
      (cond ((eq? message 'initialise) initialise)
            ((eq? message 'push) push)
            ((eq? message 'pop) pop)
            (else
             (error "Unknown message -- STACK-CONTROLLER" message))))
    dispatch))

(define (push stack-controller value register)
  ((stack-controller 'push) value register))

(define (pop stack-controller register)
  ((stack-controller 'pop) register))

;;; Basic machine

(define-public (start machine)
  (machine 'start))

(define-public (get-register-contents machine register-name)
  (get-contents (get-register machine register-name)))

(define-public (set-register-contents! machine register-name value)
  (set-contents! (get-register machine register-name) value)
  'done)

(define-public (get-register machine reg-name)
  ((machine 'get-register) reg-name))

(define (make-new-machine stack-mode)
  (let ((pc (make-register 'pc))
        (flag (make-register 'flag))
        (stack-controller (make-stack-controller stack-mode))
        (the-instruction-sequence '()))
    (let ((the-ops
           (list (list 'initialise-stack
                       (lambda () (stack-controller 'initialise)))))
          (register-table
           (list (list 'pc pc)
                 (list 'flag flag))))
      (define (allocate-register name)
        (if (assoc name register-table)
            (error "Register defined multiple times -- ALLOCATE-REGISTER" name)
            (set! register-table
                  (cons (list name (make-register name))
                        register-table)))
        'register-allocated)
      (define (lookup-register name)
        (let ((val (assoc name register-table)))
          (if val
              (cadr val)
              (error "Unknown register - LOOKUP-REGISTER" name))))
      (define (initialise-stack-controller)
        (let ((registers '()))
          (for-each (lambda (table-entry)
                      (let ((register (car table-entry)))
                        (if (and (not (eq? register 'pc))
                                 (not (eq? register 'flag)))
                            (set! registers (cons register registers)))))
                    register-table)
          ((stack-controller 'initialise) registers)))
      (define (execute)
        (let ((insts (get-contents pc)))
          (if (null? insts)
              'done
              (begin
                ((instruction-execution-proc (car insts)))
                (execute)))))
      (define (dispatch message)
        (cond ((eq? message 'start)
               (set-contents! pc the-instruction-sequence)
               (execute))
              ((eq? message 'install-instruction-sequence)
               (lambda (seq)
                 (set! the-instruction-sequence seq)))
              ((eq? message 'allocate-register) allocate-register)
              ((eq? message 'get-register) lookup-register)
              ((eq? message 'install-operations)
               (lambda (ops)
                 (set! the-ops (append the-ops ops))))
              ((eq? message 'stack-controller) stack-controller)
              ((eq? message 'operations) the-ops)
              ((eq? message 'initialise-stack-controller) (initialise-stack-controller))
              (else
               (error "Unknown request -- MACHINE" message))))
      dispatch)))

;;; Assembler

(define (assemble controller-text machine)
  (extract-labels controller-text
                  (lambda (insts labels)
                    (update-insts! insts labels machine)
                    insts)))

(define (extract-labels text receive)
  (if (null? text)
      (receive '() '())
      (extract-labels (cdr text)
                      (lambda (insts labels)
                        (let ((next-inst (car text)))
                          (if (symbol? next-inst)
                              (if (assoc next-inst labels)
                                  (error "Label already seen -- ASSEMBLE" next-inst)
                                  (receive
                                      insts
                                      (cons (make-label-entry next-inst insts)
                                            labels)))
                              (receive
                                  (cons (make-instruction next-inst) insts)
                                  labels)))))))

(define (update-insts! insts labels machine)
  (let ((pc (get-register machine 'pc))
        (flag (get-register machine 'flag))
        (stack-controller (machine 'stack-controller))
        (ops (machine 'operations)))
    (for-each
     (lambda (inst)
       (set-instruction-execution-proc!
        inst
        (make-execution-procedure (instruction-text inst) labels machine pc flag stack-controller ops)))
     insts)
    insts))

(define (make-instruction text)
  (cons text '()))

(define (instruction-text inst)
  (car inst))

(define (instruction-execution-proc inst)
  (cdr inst))

(define (set-instruction-execution-proc! inst proc)
  (set-cdr! inst proc))

(define (make-label-entry label-name insts)
  (cons label-name insts))

(define (lookup-label labels label-name)
  (let ((val (assoc label-name labels)))
    (if val
        (cdr val)
        (error "Undefined label -- ASSEMBLE" label-name))))

;;; Execution procedures

(define (make-execution-procedure inst labels machine pc flag stack-controller ops)
  (cond ((eq? (car inst) 'assign)
         (make-assign inst machine labels ops pc))
        ((eq? (car inst) 'test)
         (make-test inst machine labels ops flag pc))
        ((eq? (car inst) 'branch)
         (make-branch inst machine labels flag pc))
        ((eq? (car inst) 'goto)
         (make-goto inst machine labels pc))
        ((eq? (car inst) 'save)
         (make-save inst machine stack-controller pc))
        ((eq? (car inst) 'restore)
         (make-restore inst machine stack-controller pc))
        ((eq? (car inst) 'perform)
         (make-perform inst machine labels ops pc))
        (else
         (error "Unknown instruction type -- ASSEMBLE" inst))))

(define (advance-pc pc)
  (set-contents! pc (cdr (get-contents pc))))

;;; Assign

(define (make-assign inst machine labels operations pc)
  (let ((target
         (get-register machine (assign-reg-name inst)))
        (value-exp (assign-value-exp inst)))
    (let ((value-proc
           (if (operation-exp? value-exp)
               (make-operation-exp value-exp machine labels operations)
               (make-primitive-exp (car value-exp) machine labels))))
      (lambda ()
        (set-contents! target (value-proc))
        (advance-pc pc)))))

(define (assign-reg-name assign-instruction)
  (cadr assign-instruction))

(define (assign-value-exp assign-instruction)
  (cddr assign-instruction))

;;; Test

(define (make-test inst machine labels operations flag pc)
  (let ((condition (test-condition inst)))
    (if (operation-exp? condition)
        (let ((condition-proc
               (make-operation-exp condition machine labels operations)))
          (lambda ()
            (set-contents! flag (condition-proc))
            (advance-pc pc)))
        (error "Bad TEST instruction -- ASSEMBLE" inst))))

(define (test-condition test-instruction)
  (cdr test-instruction))

;;; Branch

(define (make-branch inst machine labels flag pc)
  (let ((dest (branch-dest inst)))
    (if (label-exp? dest)
        (let ((insts
               (lookup-label labels (label-exp-label dest))))
          (lambda ()
            (if (get-contents flag)
                (set-contents! pc insts)
                (advance-pc pc))))
        (error "Bad BRANCH instruction -- ASSEMBLE" inst))))

(define (branch-dest branch-instruction)
  (cadr branch-instruction))

;;; GOTO

(define (make-goto inst machine labels pc)
  (let ((dest (goto-dest inst)))
    (cond ((label-exp? dest)
           (let ((insts
                  (lookup-label labels
                                (label-exp-label dest))))
             (lambda ()
               (set-contents! pc insts))))
          ((register-exp? dest)
           (let ((reg
                  (get-register machine (register-exp-reg dest))))
             (lambda ()
               (set-contents! pc (get-contents reg)))))
          (else
           (error "Bad GOTO instruction -- ASSEMBLE" inst)))))

(define (goto-dest goto-instruction)
  (cadr goto-instruction))

;;; Save

(define (make-save inst machine stack-controller pc)
  (let ((reg-name (stack-inst-reg-name inst)))
    (let ((reg (get-register machine reg-name)))
      (lambda ()
        (push stack-controller (get-contents reg) reg-name)
        (advance-pc pc)))))

(define (stack-inst-reg-name stack-instruction)
  (cadr stack-instruction))

;;; Restore

(define (make-restore inst machine stack-controller pc)
  (let ((reg-name (stack-inst-reg-name inst)))
    (let ((reg (get-register machine reg-name)))
      (lambda ()
        (set-contents! reg (pop stack-controller reg-name))
        (advance-pc pc)))))

;;; Perform

(define (make-perform inst machine labels operations pc)
  (let ((action (perform-action inst)))
    (if (operation-exp? action)
        (let ((action-proc
               (make-operation-exp action machine labels operations)))
          (lambda ()
            (action-proc)
            (advance-pc pc)))
        (error "Bad PERFORM instruction -- ASSEMBLE" inst))))

(define (perform-action inst) (cdr inst))

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
         (let ((r (get-register machine
                                (register-exp-reg exp))))
           (lambda ()
             (get-contents r))))
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

(define (make-operation-exp exp machine labels operations)
  (let ((op (lookup-prim (operation-exp-op exp) operations))
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

(define (lookup-prim symbol operations)
  (let ((val (assoc symbol operations)))
    (if val
        (cadr val)
        (error "Unknown operation -- ASSEMBLE" symbol))))
