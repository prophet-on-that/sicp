;;; Exercise 4.40

(define-module (sicp ch4))

(use-modules (srfi srfi-1)
             (ice-9 receive))

(define (multiple-dwelling)
  (let ((fletcher (amb 2 3 4))
        (cooper (amb 2 3 4 5)))
    (require (not (= (abs (- fletcher cooper))
                     1)))
    (let ((smith (amb 1 2 3 4 5)))
      (require (not (= (abs (- smith fletcher))
                       1)))
      (let ((miller (amb 1 2 3 4 5)))
        (require (> miller cooper))
        (let ((baker (amb 1 2 3 4 5)))
          (list (list 'baker baker)
                (list 'cooper cooper)
                (list 'fletcher fletcher)
                (list 'miller miller)
                (list 'smith smith)))))))

;;; Exercise 4.41

(define (permute l)
  (if (or (null? l)
          (= (length l) 1))
      (list l)
      (let ((permutations (permute (cdr l))))
        (append-map (lambda (permutation)
                      (map (lambda (index)
                             (receive (left right)
                                 (split-at permutation index)
                               (append left
                                       (list (car l))
                                       right)))
                           (iota (1+ (length permutation)))))
                    permutations))))

(define (multiple-dwellings')
  (filter (lambda (assignment)
            (let ((baker (list-ref assignment 0))
                  (cooper (list-ref assignment 1))
                  (fletcher (list-ref assignment 2))
                  (miller (list-ref assignment 3))
                  (smith (list-ref assignment 4)))
              (and (not (= baker 5))
                   (not (= cooper 1))
                   (not (= fletcher 5))
                   (not (= fletcher 1))
                   (> miller cooper)
                   (not (= (abs (- smith fletcher))
                           1))
                   (not (= (abs (- fletcher cooper))
                           1)))))
          (permute (list 1 2 3 4 5))))

;;; Exercise 4.43

(define (yachts)
  (let ((mary-ann-father 'moore)
        (melissa-father 'hood)
        (yachts '((hood gabrielle)
                  (moore lorna)
                  (hall rosalind)
                  (downing melissa)
                  (parker mary-ann)))
        (gabrielle-father (amb 'hall 'downing 'parker))
        (parker-daughter (amb 'rosalind 'lorna 'gabrielle)))
    (require (or (and (eq? parker-daughter 'gabrielle)
                      (eq? gabrielle-father 'parker))
                 #t))
    (require (member (list gabrielle-father parker-daughter) yachts))
    (let ((hall-daughter (amb 'lorna 'gabrielle))
          (downing-daughter (amb 'rosalind 'lorna 'gabrielle)))
      (require (distinct (list parker-daughter hall-daughter downing-daughter)))
      (require (or (and (eq? gabrielle-father 'hall)
                        (eq? hall-daughter 'gabrielle))
                   (and (eq? gabrielle-father 'downing)
                        (eq? downing-daughter 'gabrielle))))
      (list parker-daughter hall-daughter downing-daughter))))

;;; Exercise 4.44

;; This implemenetation uses SAFE? from ex. 2.42
(define (queens)
  (define (helper columns)
    (let ((pos (amb 1 2 3 4 5 6 7 8)))
      (let ((new-columns (cons pos columns)))
        (require (safe? new-columns))
       (if (= (length new-columns) 8)
           new-columns
           (helper new-columns)))))
  (helper '()))
