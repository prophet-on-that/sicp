(define-module (sicp qeval))

(use-modules (sicp eval-utils)
             (srfi srfi-41)
             (sicp dispatch-table))

(define-syntax-rule (singleton-stream e)
  (stream-cons e stream-null))

(define (stream-interleave-delayed s1 delayed-s2)
  (if (stream-null? s1)
      (force delayed-s2)
      (stream-cons (stream-car s1)
                   (stream-interleave-delayed (force delayed-s2)
                                              (delay (stream-cdr s1))))))

(define (stream-flatmap proc s)
  (flatten-stream (stream-map proc s)))

(define (flatten-stream stream)
  (if (stream-null? stream)
      stream-null
      (stream-interleave-delayed (stream-car stream)
                                 (delay (flatten-stream (stream-cdr stream))))))

(define (simple-stream-flatmap proc s)
  (simple-flatten (stream-map proc s)))

(define (simple-flatten stream)
  (stream-map stream-car
              (stream-filter (lambda (s)
                               (not (stream-null? s)))
                             stream)))

(define (display-stream s)
  (stream-for-each (lambda (elem)
                     (newline)
                     (display elem))
                   s))

(define (stream-any pred s)
  (cond ((stream-null? s)
         #f)
        ((pred (stream-car s))
         #t)
        (else
         (stream-any pred (stream-cdr s)))))

(define input-prompt ";;; Query input:")
(define output-prompt ";;; Query results:")

(define-public (query-driver-loop)
  (prompt-for-input input-prompt)
  (let ((q (query-syntax-process (read))))
    (cond ((eq? q 'quit)
           'quit)
          ((assertion-to-be-added? q)
           (add-rule-or-assertion! (add-assertion-body q))
           (newline)
           (display "Assertion added to data base.")
           (query-driver-loop))
          (else
           (let ((results-stream (qeval q (singleton-stream (make-empty-frame)))))
             (newline)
             (if (stream-any
                  (lambda (frame)
                    (not (null? (frame-filter-queries frame))))
                  results-stream)
                 (begin
                   (display ";;; Warning: at least one frame exists with an outstanding filter query.")
                   (newline)))
             (display output-prompt)
             (display-stream
              (stream-map
               (lambda (frame)
                 (instantiate q
                              frame
                              (lambda (v f)
                                (contract-question-mark v))))
               results-stream))
             (query-driver-loop))))))

(define-public (evaluate-and-instantiate query)
  (let ((q (query-syntax-process query)))
    (stream-map
     (lambda (frame)
       (instantiate q
                    frame
                    (lambda (v f)
                      (contract-question-mark v))))
     (qeval q (singleton-stream (make-empty-frame))))))

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

(define filter-query-types '(not lisp-value unique))

(define (qeval query frame-stream)
  (let ((results-stream (qeval-internal query frame-stream)))
    (simple-stream-flatmap
     (lambda (frame)
       (let ((filtered-frame (apply-partial-filter-queries frame)))
         (if filtered-frame
             (singleton-stream filtered-frame)
             stream-null)))
     results-stream)))

(define (qeval-internal query frame-stream)
  (let ((results-stream
         ;; Delay 'filter' type queries to be executed as either as
         ;; soon as all variables are available, or after all other
         ;; queries have been processed.
         (if (member (type query) filter-query-types)
             (stream-map
              (lambda (frame)
                (frame-add-filter-query query frame))
              frame-stream)
             (let ((qproc (dispatch-table-get qeval-dispatch-table (type query))))
               (if qproc
                   (qproc (contents query) frame-stream)
                   (simple-query query frame-stream))))))
    (simple-stream-flatmap
     (lambda (frame)
       (let ((filtered-frame (apply-completed-filter-queries frame)))
         (if filtered-frame
             (singleton-stream filtered-frame)
             stream-null)))
     results-stream)))

(define (apply-partial-filter-queries frame)
  (define (go filter-queries frame)
    (if (null? filter-queries)
        frame
        (let ((query (car filter-queries)))
          (let ((qproc (dispatch-table-get qeval-dispatch-table (type query))))
            (if qproc
                (if (stream-null? (qproc (contents query) (singleton-stream frame)))
                    #f
                    (go (cdr filter-queries) frame))
                (error "Unknown filter query -- APPLY-PARTIAL-FILTER-QUERIES" query))))))
  (go (frame-filter-queries frame)
      (make-frame (frame-bindings frame) '())))

(define (apply-completed-filter-queries frame)
  (define (go filter-queries frame)
    (if (null? filter-queries)
        frame
        (catch
          'unbound-var
          (lambda ()
            (let ((query (instantiate (car filter-queries)
                                      frame
                                      (lambda (exp f)
                                        (throw 'unbound-var)))))
              (let ((qproc (dispatch-table-get qeval-dispatch-table (type query))))
                (if qproc
                    (if (stream-null? (qproc (contents query) (singleton-stream frame)))
                        #f
                        (go (cdr filter-queries) frame))
                    (error "Unknown filter query -- APPLY-COMPLETED-FILTER-QUERIES" query)))))
          (lambda (key . args)
            (go (cdr filter-queries)
                (frame-add-filter-query (car filter-queries) frame))))))
  (go (frame-filter-queries frame)
      (make-frame (frame-bindings frame) '())))

(define (simple-query query-pattern frame-stream)
  (stream-flatmap
   (lambda (frame)
     (stream-append
      (find-assertions query-pattern frame)
      (apply-rules query-pattern frame)))
   frame-stream))

(define (conjoin conjuncts frame-stream)
  (if (empty-conjunction? conjuncts)
      frame-stream
      (conjoin (rest-conjuncts conjuncts)
               (qeval-internal (first-conjunct conjuncts)
                               frame-stream))))

(dispatch-table-put! qeval-dispatch-table 'and conjoin)

(define (disjoin disjuncts frame-stream)
  (if (empty-disjunction? disjuncts)
      stream-null
      (stream-interleave-delayed
       (qeval-internal (first-disjunct disjuncts) frame-stream)
       (delay (disjoin (rest-disjuncts disjuncts)
                       frame-stream)))))

(dispatch-table-put! qeval-dispatch-table 'or disjoin)

(define (negate operands frame-stream)
  (simple-stream-flatmap
   (lambda (frame)
     (if (stream-null? (qeval-internal (negated-query operands)
                                       (singleton-stream frame)))
         (singleton-stream frame)
         stream-null))
   frame-stream))

(dispatch-table-put! qeval-dispatch-table 'not negate)

(define (lisp-value call frame-stream)
  (simple-stream-flatmap
   (lambda (frame)
     (if (execute
          (instantiate
           call
           frame
           (lambda (v f)
             (error "Unknown pat var -- LISP-VALUE" v))))
         (singleton-stream frame)
         stream-null))
   frame-stream))

(dispatch-table-put! qeval-dispatch-table 'lisp-value lisp-value)

(define (execute exp)
  (apply (eval (predicate exp) (interaction-environment))
         (args exp)))

(define (always-true ignore frame-stream) frame-stream)

(dispatch-table-put! qeval-dispatch-table 'always-true always-true)

(define (uniquely-asserted exp frame-stream)
  (simple-stream-flatmap
   (lambda (frame)
     (let ((results-stream (qeval-internal (car exp)
                                           (singleton-stream frame))))
       (if (and (not (stream-null? results-stream))
                (stream-null? (stream-cdr results-stream)))
           (singleton-stream frame)
           stream-null)))
   frame-stream))

(dispatch-table-put! qeval-dispatch-table 'unique uniquely-asserted)

(define (find-assertions pattern frame)
  (simple-stream-flatmap (lambda (datum)
                           (check-an-assertion datum pattern frame))
                         (fetch-assertions pattern frame)))

(define (check-an-assertion assertion query-pat query-frame)
  (let ((match-result
         (pattern-match query-pat assertion query-frame)))
    (if (eq? match-result 'failed)
        stream-null
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
                                       (car dat)
                                       frame)))
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
          stream-null
          (qeval-internal (rule-body clean-rule)
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

(define the-assertions stream-null)

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
        stream-null)))

(define (get-indexed-assertions pattern)
  (get-stream (index-key-of pattern) indexed-assertions))

(define the-rules stream-null)

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

(define-public (add-rule-or-assertion! assertion)
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
          (set! indexed-assertions
                (assq-set! indexed-assertions
                           key
                           (stream-cons assertion current-assertion-stream)))))))

(define (store-rule-in-index rule)
  (let ((pattern (conclusion rule)))
    (if (indexable? pattern)
        (let ((key (index-key-of pattern)))
          (let ((current-rule-stream
                 (get-stream key indexed-rules)))
            (set! indexed-rules
                  (assq-set! indexed-rules
                             key
                             (stream-cons rule current-rule-stream))))))))

(define (indexable? pat)
  (or (constant-symbol? (car pat))
      (var? (car pat))))

(define (index-key-of pat)
  (let ((key (car pat)))
    (if (var? key) '? key)))

(define (use-index? pat)
  (constant-symbol? (car pat)))

(define (type exp)
  (if (pair? exp)
      (car exp)
      (error "Unknown expression TYPE" exp)))

(define (contents exp)
  (if (pair? exp)
      (cdr exp)
      (error "Unknown expressions CONTENTS" exp)))

(define (assertion-to-be-added? exp)
  (eq? (type exp) 'assert!))

(define (add-assertion-body exp)
  (car (contents exp)))

(define (empty-conjunction? exps)
  (null? exps))

(define (first-conjunct exps)
  (car exps))

(define (rest-conjuncts exps)
  (cdr exps))

(define (empty-disjunction? exps)
  (null? exps))

(define (first-disjunct exps)
  (car exps))

(define (rest-disjuncts exps)
  (cdr exps))

(define (negated-query exps)
  (car exps))

(define (predicate exps)
  (car exps))

(define (args exps)
  (cdr exps))

(define (rule? statement)
  (tagged-list? statement 'rule))

(define (conclusion rule)
  (cadr rule))

(define (rule-body rule)
  (if (null? (cddr rule))
      '(always-true)
      (caddr rule)))

(define-public (query-syntax-process exp)
  (map-over-symbols expand-question-mark exp))

(define (map-over-symbols proc exp)
  (cond ((pair? exp)
         (cons (map-over-symbols proc (car exp))
               (map-over-symbols proc (cdr exp))))
        ((symbol? exp) (proc exp))
        (else exp)))

(define (expand-question-mark symbol)
  (let ((chars (symbol->string symbol)))
    (if (string=? (substring chars 0 1) "?")
        (list '?
              (string->symbol
               (substring chars 1 (string-length chars))))
        symbol)))

(define (var? exp)
  (tagged-list? exp '?))

(define (constant-symbol? exp)
  (symbol? exp))

(define rule-counter 0)

(define (new-rule-application-id)
  (set! rule-counter (1+ rule-counter))
  rule-counter)

(define (make-new-variable var rule-application-id)
  (cons '? (cons rule-application-id (cdr var))))

(define (contract-question-mark variable)
  (string->symbol
   (string-append "?"
                  (if (number? (cadr variable))
                      (string-append (symbol->string (caddr variable))
                                     "-"
                                     (number->string (cadr variable)))
                      (symbol->string (cadr variable))))))

(define (make-binding variable value)
  (cons variable value))

(define (binding-variable binding)
  (car binding))

(define (binding-value binding)
  (cdr binding))

(define (make-empty-frame)
  (list '() '()))

(define (make-frame bindings filter-queries)
  (list bindings filter-queries))

(define (frame-bindings frame)
  (car frame))

(define (frame-filter-queries frame)
  (cadr frame))

(define (binding-in-frame variable frame)
  (assoc variable (frame-bindings frame)))

(define (extend variable value frame)
  "Create a new frame with extended bindings."
  (make-frame (cons (make-binding variable value)
                    (frame-bindings frame))
              (frame-filter-queries frame)))

(define (frame-add-filter-query query frame)
  "Create a new frame with extended filter queries."
  (make-frame (frame-bindings frame)
              (cons query (frame-filter-queries frame))))

(define-public (clear-database)
  (set! the-assertions stream-null)
  (set! indexed-assertions '())
  (set! indexed-rules '()))
