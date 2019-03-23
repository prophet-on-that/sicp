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
(define chief-accountant '(accounting chief accountant))

(define assertions
  `((address ,ben (Slumerville (Ridge Road) 10))
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
    (job ,eben ,chief-accountant)
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

(define rules
  `((rule (same ?x ?x))

    (rule (lives-near ?person-1 ?person-2)
          (and (address ?person-1 (?town . ?rest-1))
               (address ?person-2 (?town . ?rest-2))
               (not (same ?person-1 ?person-2))))

    (rule (outranked-by ?staff-person ?boss)
          (or (supervisor ?staff-person ?boss)
              (and (supervisor ?staff-person ?middle-manager)
                   (outranked-by ?middle-manager ?boss))))

    (rule (wheel ?person)
          (and (supervisor ?middle-manager ?person)
               (supervisor ?x ?middle-manager)))

    (rule (can-replace ?person-1 ?person-2)
          (and (job ?person-1 ?job-1)
               (job ?person-2 ?job-2)
               (or (same ?job-1 ?job-2)
                   (can-do-job ?job-1 ?job-2))
               (not (same ?person-1 ?person-2))))

    (rule (big-shot ?person)
          (and (job ?person (?division . ?rest))
               (not (and (supervisor ?person ?boss)
                         (job ?boss (?division . ?rest2))))))))

(define (load-db)
  (map add-rule-or-assertion! assertions)
  (map (lambda (rule)
         (add-rule-or-assertion! (query-syntax-process rule)))
       rules))

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
(assert-query-results `(and (lisp-value > ?amount ,min-salary)
                            (salary ?person ?amount))
                      `((and (lisp-value > ,eben-salary ,min-salary)
                             (salary ,eben ,eben-salary))
                        (and (lisp-value > ,oliver-salary ,min-salary)
                             (salary ,oliver ,oliver-salary))))

(assert-query-results `(unique (job ,ben ,computer-wizard))
                      `((unique (job ,ben ,computer-wizard))))

(assert-query-results `(unique (job ?x ,computer-programmer))
                      '())

(assert-query-results `(and (unique (supervisor ?person ?boss))
                            (job ?boss ?j))
                      `((and (unique (supervisor ?person ,eben))
                             (job ,eben ,chief-accountant))
                        (and (unique (supervisor ?person ,alyssa))
                             (job ,alyssa ,computer-programmer))))

(test-begin "rules")

(assert-query-results `(same ,ben ,ben)
                      `((same ,ben ,ben)))

(assert-query-results `(same ,ben ,alyssa)
                      '())

(assert-query-results `(lives-near ?x ,ben)
                      `((lives-near ,louis ,ben)
                        (lives-near ,deWitt ,ben)))

(assert-query-results `(and (job ?x (computer . ?rest))
                            (lives-near ?x ,ben))
                      `((and (job ,louis ,computer-programmer-trainee)
                             (lives-near ,louis ,ben))))

(assert-query-results `(outranked-by ,louis ?x)
                      `((outranked-by ,louis ,alyssa)
                        (outranked-by ,louis ,ben)
                        (outranked-by ,louis ,oliver)))

(assert-query-results `(can-replace ?x ,cy)
                      `((can-replace ,ben ,cy)
                        (can-replace ,alyssa ,cy)))

(assert-query-results '(big-shot ?x)
                      `((big-shot ,eben)
                        (big-shot ,oliver)
                        (big-shot ,ben)))

(test-end "rules")

(test-end "patterns")

(test-end "qeval")
