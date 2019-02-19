(define-module (sicp qeval))

(use-modules (sicp eval-utils)
             (srfi srfi-41)
             (sicp dispatch-table))

(define input-prompt ";;; Query input:")
(define output-prompt ";;; Query results:")

(define-public (query-driver-loop)
  (prompt-for-input input-prompt)
  (let ((q (query-syntax-process (read))))
    (cond ((assertion-to-be-added? q)
           (add-rule-or-assertion! (add-assertion-body q))
           (newline)
           (diplay "Assertion added to data base.")
           (query-driver-loop))
          (else
           (newline)
           (display-output-prompt)
           (display-stream
            (stream-map
             (lambda (frame)
               (instantiate q
                            frame
                            (lambda (v f)
                              (contract-question-mark v))))
             (qeval q (singleton-stream '()))))
           (query-driver-loop)))))

(define (instantiate exp frame unbound-var-handler)
  (define (copy exp)
    (cond ((var? exp)
           (let ((binding (binding-in-frame exp frame)))
             (if binding
                 (copy (binding-value binding))
                 (unbound-var-handler exp frame))))
          ((pair? exp)
           (cons (copy (car exp))
                 (copy (cdr exp))))
          (else exp)))
  (copy exp))

(define qeval-dispatch-table (create-dispatch-table))

(define (qeval query frame-stream)
  (let ((qproc (dispatch-table-get qeval-dispatch-table (type query))))
    (if qproc
        (qproc (contents query) frame-stream)
        (simple-query query frame-stream))))

(define (stream-flatmap proc stream)
  (stream-concat (stream-map proc stream)))

(define (simple-query query-pattern frame-stream)
  (stream-flatmap
   (lambda (frame)
     (stream-append-delayed
      (find-assertions query-pattern frame)
      (delay (apply-rules query-pattern frame))))
   frame-stream))

(define (conjoin conjuncts frame-stream)
  (if (empty-conjunction? conjuncts)
      frame-stream
      (conjoin (rest-conjuncts conjuncts)
               (qeval (first-conjunct conjuncts)
                      frame-stream))))

(dipatch-table-put qeval-dispatch-table 'and conjoin)

(define (disjoin disjuncts frame-stream)
  (if (empty-disjunction? disjuncts)
      stream-null
      (interleave-delayed
       (qeval (first-disjunct disjuncts) frame-stream)
       (delay (disjoin (rest-disjuncts disjuncts)
                       frame-stream)))))

(dispatch-table-put qeval-dispatch-table 'or disjoin)

(define (negate operands frame-stream)
  (stream-flatmap
   (lambda (frame)
     (if (stream-null? (qeval (negated-query operands)
                              (singleton-stream frame)))
         (singleton-stream frame)
         stream-null))
   frame-stream))

(dispatch-table-put qeval-dispatch-table 'not negate)

(define (lisp-value call frame-stream)
  (stream-flatmap
   (lambda (frame)
     (if (execute
          (instantiate
           call
           frame
           (lambda (v f)
             (error "Unknown pat var -- LISP-VALUE" v))))
         (singleton-stream frame)
         stream-null))))

(dispatch-table-put qeval-dispatch-table 'lisp-value lisp-value)

(define (execute exp)
  (apply (eval (predicate exp) (interaction-environment))
         (args exp)))

(define (always-true ignore frame-stream) frame-stream)

(dispatch-table-put qeval-dispatch-table 'always-true always-true)

(define (find-assertions pattern frame)
  (stream-flatmap (lambda (datum)
                    (check-an-assertion datum pattern frame))
                  (fetch-assertions pattern frame)))

(define (check-an-assertion assertion query-pat query-frame)
  (let ((match-result
         (pattern-match query-pat assertion query-frame)))
    (if (eq? match-result 'failed)
        null-stream
        (singleton-stream match-result))))

(define (pattern-match pat dat frame)
  (cond ((eq? frame 'failed) 'failed)
        ((equal? pat dat) frame)
        ((var? pat) (extend-if-consistent pat dat frame))
        ((and (pair? pat)
              (pair? dat))
         (pattern-match (cdr pat)
                        (cdr dat)
                        (pattern-match (car pat)
                                       (car dat
                                            frame))))
        (else 'failed)))

(define (extend-if-consistent var dat frame)
  (let ((binding (binding-in-frame var frame)))
    (if binding
        (pattern-match (binding-value binding) dat frame)
        (extend var dat frame))))

(define (apply-rules pattern frame)
  (stream-flatmap (lambda (rule)
                    (apply-a-rule rule pattern frame))
                  (fetch-rules pattern frame)))

(define (apply-a-rule rule query-pattern query-frame)
  (let ((clean-rule (rename-variables-in rule)))
    (let ((unify-result
           (unify-match query-pattern
                        (conclusion clean-rule)
                        query-frame)))
      (if (eq? unify-result 'failed)
          null-stream
          (qeval (rule-body clean-rule)
                 (singleton-stream unify-result))))))

(define (rename-variables-in rule)
  (let ((rule-application-id (new-rule-application-id)))
    (define (tree-walk exp)
      (cond ((var? exp)
             (make-new-variable exp rule-application-id))
            ((pair? exp)
             (cons (tree-walk (car exp))
                   (tree-walk (cdr exp))))
            (else exp)))
    (tree-walk rule)))

(define (unify-match p1 p2 frame)
  (cond ((eq? frame 'failed) 'failed)
        ((equal? p1 p2) frame)
        ((var? p1) (extend-if-possible p1 p2 frame))
        ((var? p2) (extend-if-possible p2 p1 frame))
        ((and (pair? p1) (pair? p2))
         (unify-match (cdr p1)
                      (cdr p2)
                      (unify-match (car p1)
                                   (car p2)
                                   frame)))
        (else 'failed)))

(define (extend-if-possible var val frame)
  (let ((binding (binding-in-frame var frame)))
    (cond (binding
           (unify-match (binding-value binding)
                        val
                        frame))
          ((var? val)
           (let ((binding (binding-in-frame val frame)))
             (if binding
                 (unify-match var
                              (binding-value binding)
                              frame)
                 (extend var val frame))))
          ((depends-on? val var frame)
           'failed)
          (else
           (extend var val frame)))))

(define (depends-on? exp var frame)
  (define (tree-walk e)
    (cond ((var? e)
           (if (equal? var e)
               #t
               (let ((b (binding-in-frame e frame)))
                 (if b
                     (tree-walk (binding-value b))
                     #f))))
          ((pair? e)
           (or (tree-walk (car e))
               (tree-walk (cdr e))))
          (else #f)))
  (tree-walk exp))

(define the-assertions the-empty-stream)

(define (fetch-assertions pattern frame)
  (if (use-index? pattern)
      (get-indexed-assertions pattern)
      (get-all-assertions)))

(define (get-all-assertions)
  the-assertions)

;;; TODO: use a more efficient data structure for indexed assertion
;;; lookup
(define indexed-assertions '())

(define (get-stream key alist)
  (let ((entry (assq key alist)))
    (if entry
        (cdr entry)
        the-empty-stream)))

(define (get-indexed-assertions pattern)
  (get-stream (index-key-of pattern) indexed-assertions))

(define the-rules the-empty-stream)

(define (fetch-rules pattern frame)
  (if (use-index? pattern)
      (get-indexed-rules pattern)
      (get-all-rules)))

(define (get-all-rules)
  the-rules)

;;; TODO: use a more efficient data structure than an alist
(define indexed-rules '())

(define (get-indexed-rules pattern)
  (stream-append
   (get-stream (index-key-of pattern) indexed-rules)
   (get-stream '? indexed-rules)))

(define (add-rule-or-assertion! assertion)
  (if (rule? assertion)
      (add-rule! assertion)
      (add-assertion! assertion)))

(define (add-assertion! assertion)
  (store-assertion-in-index assertion)
  (let ((old-assertions the-assertions))
    (set! the-assertions
          (stream-cons assertion old-assertions))
    'ok))

(define (add-rule! rule)
  (store-rule-in-index rule)
  (let ((old-rules the-rules))
    (set! the-rules (stream-cons rule old-rules))
    'ok))

(define (store-assertion-in-index assertion)
  (if (indexable? assertion)
      (let ((key (index-key-of assertion)))
        (let ((current-assertion-stream
               (get-stream key indexed-assertions)))
          (assq-set! indexed-assertions
                     key
                     (stream-cons assertion current-assertion-stream))))))

(define (store-rule-in-index rule)
  (let ((pattern (conclusion rule)))
    (if (indexable? pattern)
        (let ((key (index-key-of pattern)))
          (let ((current-rule-stream
                 (get-stream key indexed-rules)))
            (assq-set! indexed-rules
                       key
                       (stream-cons rule current-rule-stream)))))))

(define (indexable? pat)
  (or (constant-symbol? (car pat))
      (var? (car pat))))

(define (index-key-of pat)
  (let ((key (car pat)))
    (if (var? key) '? key)))

(define (use-index? pat)
  (constant-symbol? (car pat)))

