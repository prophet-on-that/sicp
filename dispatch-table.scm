(define-module (sicp dispatch-table))

(use-modules (srfi srfi-1))

(define-public (create-dispatch-table)
  (list '()))

(define (dispatch-table-alist dispatch-table)
  (car dispatch-table))

(define (set-dispatch-table-alist! dispatch-table alist)
  (set-car! dispatch-table alist))

(define-public (dispatch-table-put! dispatch-table symbol fn)
  (set-dispatch-table-alist! dispatch-table
                             (alist-cons symbol fn (dispatch-table-alist dispatch-table))))

(define-public (dispatch-table-get dispatch-table symbol)
  (let ((pair (assoc symbol (dispatch-table-alist dispatch-table))))
    (if pair
        (cdr pair)
        #f)))

