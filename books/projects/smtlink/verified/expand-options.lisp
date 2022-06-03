;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (April 19th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "hint-interface")

(local (in-theory (disable pseudo-termp pseudo-term-listp)))

(defalist symbol-smt-function-alist
  :key-type symbolp
  :val-type smt-function-p
  :true-listp t)

(defthm assoc-equal-of-symbol-smt-function-alist
  (implies (and (symbol-smt-function-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (smt-function-p (cdr (assoc-equal x alst))))))

(defprod expand-options
  ((functions symbol-smt-function-alist-p)
   (expand-with-vars booleanp)
   (wrld-fn-len natp)))

(define construct-function-info ((func-lst smt-function-list-p))
  :returns (alst symbol-smt-function-alist-p)
  :measure (len func-lst)
  (b* ((func-lst (smt-function-list-fix func-lst))
       ((unless (consp func-lst)) nil)
       ((cons func-hd func-tl) func-lst)
       (name (smt-function->name func-hd)))
    (acons name func-hd (construct-function-info func-tl))))

(define construct-expand-options ((hints smtlink-hint-p))
  :returns (eo expand-options-p)
  (b* ((hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       (functions (construct-function-info h.functions)))
    (make-expand-options :functions functions
                         :expand-with-vars h.expand-with-vars
                         :wrld-fn-len h.wrld-fn-len)))
