(define-module (sicp qeval-test))

(use-modules (srfi srfi-64)
             (srfi srfi-41)
             (srfi srfi-1)
             (sicp qeval))

;;; Test data

(define ben '(Bitdiddle Ben))
(define alyssa '(Hacker Alyssa P))
(define alyssa-address '(Cambridge (Mass Ave) 78))
(define cy '(Fect Cy D))
(define cy-address '(Cambridge (Ames Street) 3))
(define lem '(Tweakit Lem E))
(define louis '(Reasoner Louis))
(define oliver '(Warbucks Oliver))
(define oliver-salary 150000)
(define eben '(Scrooge Eben))
(define eben-salary 75000)
(define bob '(Cratchet Robert))
(define deWitt '(Aull DeWitt))

(define computer-programmer '(computer programmer))
(define computer-wizard '(computer wizard))
(define computer-technician '(computer technician))
(define computer-programmer-trainee '(computer programmer trainee))

(define assertions
  `((address ,ben (Slumberville (Ridge Road) 10))
    (job ,ben ,computer-wizard)
    (salary ,ben 60000)

    (address ,alyssa ,alyssa-address)
    (job ,alyssa ,computer-programmer)
    (salary ,alyssa 40000)
    (supervisor ,alyssa ,ben)

    (address ,cy ,cy-address)
    (job ,cy ,computer-programmer)
    (salary ,cy 35000)
    (supervisor ,cy ,ben)

    (address ,lem (Boston (Bay State Road) 22))
    (job ,lem ,computer-technician)
    (salary ,lem 25000)
    (supervisor ,lem ,ben)

    (address ,louis (Slumerville (Pine Tree Road) 80))
    (job ,louis ,computer-programmer-trainee)
    (salary ,louis 30000)
    (supervisor ,louis ,alyssa)

    (supervisor ,ben ,oliver)

    (address ,oliver (Swellesley (Top Heap Road)))
    (job ,oliver (administration big wheel))
    (salary ,oliver ,oliver-salary)

    (address ,eben (Weston (Shady Lane) 10))
    (job ,eben (accounting chief accountant))
    (salary ,eben ,eben-salary)
    (supervisor ,eben ,oliver)

    (address ,bob (Allston (N Harvard Street) 16))
    (job ,bob (accounting scrivener))
    (salary ,bob 18000)
    (supervisor ,bob ,eben)

    (address ,deWitt (Slumerville (Onion Square) 5))
    (job ,deWitt (administration secretary))
    (salary ,deWitt 25000)
    (supervisor ,deWitt ,oliver)

    (can-do-job ,computer-wizard ,computer-programmer)
    (can-do-job ,computer-wizard ,computer-technician)

    (can-do-job ,computer-programmer ,computer-programmer-trainee)

    (can-do-job (administration secretary) (administration big wheel))))

(define (load-db)
  (map add-rule-or-assertion! assertions))

;;; Test suite

(define (assert-query-results query expected)
  (let ((actual (stream->list
                 (evaluate-and-instantiate query))))
    (test-assert (format #f "~a" query)
      (and (eq? (length actual) (length expected))
           (every (lambda (e)
                    (member e actual))
                  expected)))))

;; Reset the current test runner
(test-runner-current (test-runner-simple))

(test-begin "qeval")

;;; Setup
(clear-database)
(load-db)

(test-begin "patterns")

(assert-query-results `(job ,ben ,computer-wizard)
                      `((job ,ben ,computer-wizard)))

(assert-query-results `(job ?x ,computer-programmer)
                      `((job ,alyssa ,computer-programmer)
                        (job ,cy ,computer-programmer)))

(assert-query-results '(supervisor ?x ?x)
                      '())

(assert-query-results '(job ?x (computer ?type))
                      `((job ,ben ,computer-wizard)
                        (job ,alyssa ,computer-programmer)
                        (job ,cy ,computer-programmer)
                        (job ,lem ,computer-technician)))

(assert-query-results '(job ?x (computer . ?type))
                      `((job ,ben ,computer-wizard)
                        (job ,alyssa ,computer-programmer)
                        (job ,cy ,computer-programmer)
                        (job ,lem ,computer-technician)
                        (job ,louis ,computer-programmer-trainee)))

(assert-query-results `(and (job ?person ,computer-programmer)
                            (address ?person ?where))
                      `((and (job ,alyssa ,computer-programmer)
                             (address ,alyssa ,alyssa-address))
                        (and (job ,cy ,computer-programmer)
                             (address ,cy ,cy-address))))

(assert-query-results `(or (supervisor ?x ,ben)
                           (supervisor ?x ,alyssa))
                      `((or (supervisor ,alyssa ,ben)
                            (supervisor ,alyssa ,alyssa))
                        (or (supervisor ,cy ,ben)
                            (supervisor ,cy ,alyssa))
                        (or (supervisor ,lem ,ben)
                            (supervisor ,lem ,alyssa))
                        (or (supervisor ,louis ,ben)
                            (supervisor ,louis ,alyssa))))

(assert-query-results `(and (supervisor ?x ,ben)
                            (not (job ?x ,computer-programmer)))
                      `((and (supervisor ,lem ,ben)
                             (not (job ,lem ,computer-programmer)))))

(define min-salary 60000)
(assert-query-results `(and (salary ?person ?amount)
                            (lisp-value > ?amount ,min-salary))
                      `((and (salary ,eben ,eben-salary)
                             (lisp-value > ,eben-salary ,min-salary))
                        (and (salary ,oliver ,oliver-salary)
                             (lisp-value > ,oliver-salary ,min-salary))))

(test-end "patterns")

(test-end "qeval")
