(define-module (sicp qeval-test))

(use-modules (sicp qeval))

(define ben '(Bitdiddle Ben))
(define alyssa '(Hacker Alyssa P))
(define cy '(Fect Cy D))
(define lem '(Tweakit Lem E))
(define louis '(Reasoner Louis))
(define oliver '(Warbucks Oliver))
(define eben '(Scrooge Eben))
(define bob '(Cratchet Robert))
(define deWitt '(Aull DeWitt))

(define assertions
  `((address ,ben (Slumberville (Ridge Road) 10))
    (job ,ben (computer wizard))
    (salary ,ben 60000)

    (address ,alyssa (Cambridge (Mass Ave) 78))
    (job ,alyssa (computer programmer))
    (salary ,alyssa 40000)
    (supervisor ,alyssa ,ben)

    (address ,cy (Cambridge (Ames Street) 3))
    (job ,cy (computer programmer))
    (salary ,cy 35000)
    (supervisor ,cy ,ben)

    (address ,lem (Boston (Bay State Road) 22))
    (job ,lem (computer technician))
    (salary ,lem 25000)
    (supervisor ,lem ,ben)

    (address ,louis (Slumerville (Pine Tree Road) 80))
    (job ,louis (computer programmer trainee))
    (salary ,louis 30000)
    (supervisor ,louis ,alyssa)

    (supervisor ,ben ,oliver)

    (address ,oliver (Swellesley (Top Heap Road)))
    (job ,oliver (administration big wheel))
    (salary ,oliver 150000)

    (address ,eben (Weston (Shady Lane) 10))
    (job ,eben (accounting chief accountant))
    (salary ,eben 75000)
    (supervisor ,eben ,oliver)

    (address ,bob (Allston (N Harvard Street) 16))
    (job ,bob (accounting scrivener))
    (salary ,bob 18000)
    (supervisor ,bob ,eben)

    (address ,deWitt (Slumerville (Onion Square) 5))
    (job ,deWitt (administration secretary))
    (salary ,deWitt 25000)
    (supervisor ,deWitt ,oliver)

    (can-do-job (computer wizard) (computer programmer))
    (can-do-job (computer wizard) (computer technician))

    (can-do-job (computer programmer) (computer programmer trainee))

    (can-do-job (administration secretary) (administration big wheel))))

(clear-database)
(map add-rule-or-assertion! assertions)
