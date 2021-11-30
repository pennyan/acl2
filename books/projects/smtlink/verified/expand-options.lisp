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
   (type-fns symbol-symbol-alistp)
   (wrld-fn-len natp)))

(define construct-function-info ((func-lst smt-function-list-p))
  :returns (alst symbol-smt-function-alist-p)
  :measure (len func-lst)
  (b* ((func-lst (smt-function-list-fix func-lst))
       ((unless (consp func-lst)) nil)
       ((cons func-hd func-tl) func-lst)
       (name (smt-function->name func-hd)))
    (acons name func-hd (construct-function-info func-tl))))

(define construct-type-related-function ((func smt-function-p)
                                         (acc symbol-symbol-alistp))
  :returns (new-acc symbol-symbol-alistp)
  (b* ((func (smt-function-fix func))
       (acc (symbol-symbol-alist-fix acc))
       (name (smt-function->name func)))
    (acons name nil acc)))

(define construct-type-related-function-list ((func-lst smt-function-list-p)
                                              (acc symbol-symbol-alistp))
  :returns (alst symbol-symbol-alistp)
  :measure (len func-lst)
  (b* ((func-lst (smt-function-list-fix func-lst))
       (acc (symbol-symbol-alist-fix acc))
       ((unless (consp func-lst)) acc)
       ((cons func-hd func-tl) func-lst))
    (construct-type-related-function-list
     func-tl
     (construct-type-related-function func-hd acc))))

(define construct-sum-related-function ((sum smt-sum-p)
                                        (acc symbol-symbol-alistp))
  :returns (types symbol-symbol-alistp)
  (b* ((sum (smt-sum-fix sum))
       (acc (symbol-symbol-alist-fix acc))
       ((smt-sum s) sum)
       (acc-1 (construct-type-related-function s.constructor acc)))
    (construct-type-related-function-list s.destructors acc-1)))

(define construct-sum-related-function-list ((sum-lst smt-sum-list-p)
                                             (acc symbol-symbol-alistp))
  :returns (types symbol-symbol-alistp)
  :measure (len sum-lst)
  (b* ((sum-lst (smt-sum-list-fix sum-lst))
       (acc (symbol-symbol-alist-fix acc))
       ((unless (consp sum-lst)) acc)
       ((cons sum-hd sum-tl) sum-lst)
       (acc-1 (construct-sum-related-function sum-hd acc)))
    (construct-sum-related-function-list sum-tl acc-1)))

(define construct-type-related-functions ((types smt-type-list-p)
                                          (acc symbol-symbol-alistp))
  :returns (types symbol-symbol-alistp)
  :measure (len types)
  :verify-guards nil
  (b* ((types (smt-type-list-fix types))
       (acc (symbol-symbol-alist-fix acc))
       ((unless (consp types)) acc)
       ((cons types-hd types-tl) types)
       (acc-1 (construct-type-related-function
               (smt-type->recognizer types-hd) acc))
       (acc-2 (construct-type-related-function
               (smt-type->fixer types-hd) acc-1))
       (acc-3 (construct-sum-related-function-list
               (smt-type->sums types-hd) acc-2))
       ((unless (smt-type->kind types-hd))
        (construct-type-related-functions types-tl acc-3)))
    (construct-type-related-functions
     types-tl
     (construct-type-related-function (smt-type->kind types-hd) acc-3))))

(verify-guards construct-type-related-functions)

(define construct-expand-options ((hints smtlink-hint-p))
  :returns (eo expand-options-p)
  (b* ((hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       (functions (construct-function-info h.functions))
       (type-fns (construct-type-related-functions h.types nil)))
    (make-expand-options :functions functions
                         :type-fns type-fns
                         :wrld-fn-len h.wrld-fn-len)))
