(define-module (sicp reg-machine))

(use-modules (sicp eval-utils)
             (srfi srfi-1))

(define-public (make-machine ops controller-text)
  (let ((machine (make-new-machine)))
    ((machine 'install-operations) ops)
    ((machine 'install-instruction-sequence)
     (assemble controller-text machine))
    machine))

;;; Registers

(define (make-register name)
  (let ((contents '*unassigned*)
        (trace #f))
    (define (dispatch message)
      (cond ((eq? message 'get) contents)
            ((eq? message 'set)
             (lambda (value)
               (if trace
                   (begin
                     (display (list 'register name
                                    'old-value contents
                                    'new-value value))
                     (newline)))
               (set! contents value)))
            ((eq? message 'set-trace!)
             (lambda (t) (set! trace t)))
            (else
             (error "Unknown request -- REGISTER" message))))
    dispatch))

(define (get-contents register)
  (register 'get))

(define (set-contents! register value)
  ((register 'set) value))

;;; Stack

(define (make-stack)
  (let ((s '())
        (number-pushes 0)
        (max-depth 0)
        (current-depth 0))
    (define (push x)
      (set! s (cons x s))
      (set! number-pushes (+ 1 number-pushes))
      (set! current-depth (+ 1 current-depth))
      (set! max-depth (max current-depth max-depth)))
    (define (pop)
      (if (null? s)
          (error "Empty stack -- POP")
          (let ((top (car s)))
            (set! s (cdr s))
            (set! current-depth (- current-depth 1))
            top)))
    (define (initialise)
      (set! s '())
      (set! number-pushes 0)
      (set! max-depth 0)
      (set! current-depth 0)
      'done)
    (define (print-statistics)
      (newline)
      (display (list 'total-pushes '= number-pushes
                     'maximum-depth '= max-depth))
      (newline))
    (define (dispatch message)
      (cond ((eq? message 'push) push)
            ((eq? message 'pop) (pop))
            ((eq? message 'initialise) (initialise))
            ((eq? message 'print-statistics) (print-statistics))
            (else (error "Unknown request -- STACK" message))))
    dispatch))

(define (pop stack)
  (stack 'pop))

(define (push stack value)
  ((stack 'push) value))

;;; Machine stats

(define (make-machine-stats)
  (let ((instructions '())
        (entry-registers '())
        (stack-registers '())
        (register-sources '()))
    (define (initialise)
      (display "Initialise called!")
      (newline)
      (set! instructions '())
      (set! entry-registers '())
      (set! stack-registers '())
      (set! register-sources '()))
    (define (add-instruction inst)
      (set! instructions (lset-adjoin equal? instructions inst)))
    (define (add-entry-register register)
      (set! entry-registers (lset-adjoin eq? entry-registers register)))
    (define (add-stack-register register)
      (set! stack-registers (lset-adjoin eq? stack-registers register)))
    (define (add-register-source register source)
      (let ((sources (assq register register-sources)))
        (if sources
            (assq-set! register-sources register (lset-adjoin equal? (cdr sources) source))
            (set! register-sources (acons register source register-sources)))))
    (define (print)
      (display "Unique instructions:")
      (newline)
      (for-each (lambda (inst)
                  (display inst)
                  (newline))
                instructions)
      (newline)
      (display "Registers holding entry points:")
      (newline)
      (for-each (lambda (register)
                  (display register)
                  (newline))
                entry-registers)
      (newline)
      (display "Saved or restored registers:")
      (newline)
      (for-each (lambda (register)
                  (display register)
                  (newline))
                stack-registers)
      (newline)
      (display "Register sources:")
      (newline)
      (for-each (lambda (pair)
                  (display (car pair))
                  (newline)
                  (for-each (lambda (source)
                              (display source)
                              (newline))
                            (cdr pair))
                  (newline))
                register-sources)
      (newline))
    (define (dispatch message)
      (cond ((eq? message 'initialise) (initialise))
            ((eq? message 'add-instruction) add-instruction)
            ((eq? message 'add-entry-register) add-entry-register)
            ((eq? message 'add-stack-register) add-stack-register)
            ((eq? message 'add-register-source) add-register-source)
            ((eq? message 'register-sources) register-sources)
            ((eq? message 'print) (print))
            (else (error "Unknown message -- MAKE-MACHINE-STATS" message))))
    dispatch))

(define (initialise-machine-stats stats)
  (stats 'initialise))

(define (add-instruction-stat stats inst)
  ((stats 'add-instruction) inst))

(define (add-entry-register-stat stats register)
  ((stats 'add-entry-register) register))

(define (add-stack-register-stat stats register)
  ((stats 'add-stack-register) register))

(define (add-register-source! stats register source)
  ((stats 'add-register-source) register source))

;;; Breakpoints

(define (make-breakpoint label offset)
  (cons label offset))

(define (breakpoint-label bp)
  (car bp))

(define (breakpoint-offset bp)
  (cdr bp))

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

(define (make-new-machine)
  (let ((pc (make-register 'pc))
        (flag (make-register 'flag))
        (stack (make-stack))
        (the-instruction-sequence '())
        (stats (make-machine-stats))
        (executed-instruction-count 0)
        (trace #f)
        (breakpoints '()))
    (let ((the-ops
           (list (list 'initialise-stack
                       (lambda () (stack 'initialise)))
                 (list 'print-stack-statistics
                       (lambda () (stack 'print-statistics)))
                 (list 'read read)
                 (list 'print
                       (lambda (val)
                         (display val)
                         (newline)))))
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
      (define (execute)
        (let ((insts (get-contents pc)))
          (if (null? insts)
              'done
              (let ((next-inst (car insts)))
                (if trace
                    (begin
                      (if (and (instruction-label next-inst)
                               (= (instruction-label-offset next-inst) 1))
                          (begin
                            (display (instruction-label next-inst))
                            (newline)))
                      (display (instruction-text next-inst))
                      (newline)))
                (if (find (lambda (bp)
                            (and (eq? (breakpoint-label bp) (instruction-label next-inst))
                                 (= (breakpoint-offset bp) (instruction-label-offset next-inst))))
                          breakpoints)
                    'break
                    (proceed))))))

      ;; Pre: (not (null? (get-contents pc)))
      (define (proceed)
        (let ((next-inst (car (get-contents pc))))
          ((instruction-execution-proc next-inst))
          (set! executed-instruction-count (+ executed-instruction-count 1))
          (execute)))

      (define (print-executed-instruction-count)
        (display executed-instruction-count)
        (newline)
        (set! executed-instruction-count 0))
      (define (set-register-trace! reg-name value)
        (((lookup-register reg-name) 'set-trace!) value))

      (define (set-breakpoint label offset)
        (set! breakpoints (cons (make-breakpoint label offset)
                                breakpoints)))

      (define (cancel-breakpoint label offset)
        (set! breakpoints
              (filter (lambda (bp)
                        (not (and (eq? (breakpoint-label bp) label)
                                  (= (breakpoint-offset bp) offset))))
                      breakpoints)))

      (define (cancel-all-breakpoints)
        (set! breakpoints '()))

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
              ((eq? message 'stack) stack)
              ((eq? message 'operations) the-ops)
              ((eq? message 'stats) stats)
              ((eq? message 'register-table) register-table)
              ((eq? message 'print-executed-instruction-count)
               (print-executed-instruction-count))
              ((eq? message 'trace-on) (set! trace #t))
              ((eq? message 'trace-off) (set! trace #f))
              ((eq? message 'set-register-trace!) set-register-trace!)
              ((eq? message 'set-breakpoint) set-breakpoint)
              ((eq? message 'cancel-breakpoint) cancel-breakpoint)
              ((eq? message 'cancel-all-breakpoints) (cancel-all-breakpoints))
              ((eq? message 'proceed) (proceed))
              (else
               (error "Unknown request -- MACHINE" message))))
      dispatch)))

(define-public (print-stats machine)
  ((machine 'stats) 'print))

(define (allocate-register machine reg-name)
  (let ((register-table (machine 'register-table)))
    (if (not (assoc reg-name register-table))
        ((machine 'allocate-register) reg-name))))

(define-public (trace-on machine)
  (machine 'trace-on))

(define-public (trace-off machine)
  (machine 'trace-off))

(define-public (set-register-trace! machine reg-name value)
  ((machine 'set-register-trace!) reg-name value))

(define-public (set-breakpoint machine label offset)
  ((machine 'set-breakpoint) label offset))

(define-public (cancel-breakpoint machine label offset)
  ((machine 'cancel-breakpoint) label offset))

(define-public (cancel-all-breakpoints machine)
  (machine 'cancel-all-breakpoints))

(define-public (proceed machine)
  (machine 'proceed))

;;; Assembler

(define (assemble controller-text machine)
  (extract-labels controller-text
                  #f
                  1
                  (lambda (insts labels)
                    (update-insts! insts labels machine)
                    insts)))

(define (extract-labels text prev-label label-offset receive)
  (if (null? text)
      (receive '() '())
      (let ((next-inst (car text)))
        (if (symbol? next-inst)
            (extract-labels (cdr text)
                            next-inst
                            1
                            (lambda (insts labels)
                              (if (assoc next-inst labels)
                                  (error "Label already seen -- ASSEMBLE" next-inst)
                                  (receive
                                      insts
                                      (cons (make-label-entry next-inst insts)
                                            labels)))))
            (extract-labels (cdr text)
                            prev-label
                            (1+ label-offset)
                            (lambda (insts labels)
                              (receive
                                  (cons (make-instruction next-inst prev-label label-offset)
                                        insts)
                                  labels)))))))

(define (update-insts! insts labels machine)
  (let ((pc (get-register machine 'pc))
        (flag (get-register machine 'flag))
        (stack (machine 'stack))
        (ops (machine 'operations))
        (stats (machine 'stats)))
    (for-each
     (lambda (inst)
       (set-instruction-execution-proc!
        inst
        (make-execution-procedure (instruction-text inst) labels machine pc flag stack ops stats)))
     insts)
    insts))

(define (make-instruction text label label-offset)
  (list text '() label label-offset))

(define (instruction-text inst)
  (car inst))

(define (instruction-execution-proc inst)
  (cadr inst))

(define (instruction-label inst)
  (caddr inst))

(define (instruction-label-offset inst)
  (cadddr inst))

(define (set-instruction-execution-proc! inst proc)
  (set-car! (cdr inst) proc))

(define (make-label-entry label-name insts)
  (cons label-name insts))

(define (lookup-label labels label-name)
  (let ((val (assoc label-name labels)))
    (if val
        (cdr val)
        (error "Undefined label -- ASSEMBLE" label-name))))

;;; Execution procedures

(define (make-execution-procedure inst labels machine pc flag stack ops stats)
  (let ((proc
         (cond ((eq? (car inst) 'assign)
                (make-assign inst machine labels ops pc stats))
               ((eq? (car inst) 'test)
                (make-test inst machine labels ops flag pc))
               ((eq? (car inst) 'branch)
                (make-branch inst machine labels flag pc))
               ((eq? (car inst) 'goto)
                (make-goto inst machine labels pc stats))
               ((eq? (car inst) 'save)
                (make-save inst machine stack pc stats))
               ((eq? (car inst) 'restore)
                (make-restore inst machine stack pc stats))
               ((eq? (car inst) 'perform)
                (make-perform inst machine labels ops pc))
               (else
                (error "Unknown instruction type -- ASSEMBLE" inst)))))
    (add-instruction-stat stats inst)
    proc))

(define (advance-pc pc)
  (set-contents! pc (cdr (get-contents pc))))

;;; Assign

(define (make-assign inst machine labels operations pc stats)
  (let ((reg-name (assign-reg-name inst)))
    (allocate-register machine reg-name)
    (let ((target
           (get-register machine reg-name))
          (value-exp (assign-value-exp inst)))
      (let ((value-proc
             (if (operation-exp? value-exp)
                 (make-operation-exp value-exp machine labels operations)
                 (make-primitive-exp (car value-exp) machine labels))))
        (add-register-source! stats reg-name (list value-exp))
        (lambda ()
          (set-contents! target (value-proc))
          (advance-pc pc))))))

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

(define (make-goto inst machine labels pc stats)
  (let ((dest (goto-dest inst)))
    (cond ((label-exp? dest)
           (let ((insts
                  (lookup-label labels
                                (label-exp-label dest))))
             (lambda ()
               (set-contents! pc insts))))
          ((register-exp? dest)
           (let ((reg-name (register-exp-reg dest)))
             (allocate-register machine reg-name)
             (let ((reg
                    (get-register machine reg-name)))
               (add-entry-register-stat stats reg-name)
               (lambda ()
                 (set-contents! pc (get-contents reg))))))
          (else
           (error "Bad GOTO instruction -- ASSEMBLE" inst)))))

(define (goto-dest goto-instruction)
  (cadr goto-instruction))

;;; Save

(define (make-save inst machine stack pc stats)
  (let ((reg-name (stack-inst-reg-name inst)))
    (allocate-register machine reg-name)
    (let ((reg (get-register machine reg-name)))
      (add-stack-register-stat stats reg-name)
      (lambda ()
        (push stack (get-contents reg))
        (advance-pc pc)))))

(define (stack-inst-reg-name stack-instruction)
  (cadr stack-instruction))

;;; Restore

(define (make-restore inst machine stack pc stats)
  (let ((reg-name (stack-inst-reg-name inst)))
    (let ((reg (get-register machine reg-name)))
      (add-stack-register-stat stats reg-name)
      (allocate-register machine reg-name)
      (lambda ()
        (set-contents! reg (pop stack))
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
         (let ((reg-name (register-exp-reg exp)))
           (allocate-register machine reg-name)
           (let ((r (get-register machine reg-name)))
             (lambda ()
               (get-contents r)))))
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
