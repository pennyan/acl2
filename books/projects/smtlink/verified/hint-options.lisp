;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (Oct 26th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "type-options")
(include-book "expand-options")

(defalist symbol-smt-type-alist
  :key-type symbolp
  :val-type smt-type-p
  :true-listp t)

(defprod hint-options
  ((supertype type-to-types-alist-p)
   (type symbol-smt-type-alist-p)
   (function symbol-smt-function-alist-p)))

(define construct-type-hint-alist ((types smt-type-list-p)
                                   (acc symbol-smt-type-alist-p))
  :returns (type-alst symbol-smt-type-alist-p)
  :measure (len types)
  (b* ((types (smt-type-list-fix types))
       (acc (symbol-smt-type-alist-fix acc))
       ((unless (consp types)) acc)
       ((cons t-hd t-tl) types)
       (rec (smt-function->name (smt-type->recognizer t-hd)))
       ((if (assoc-equal rec acc)) acc))
    (construct-type-hint-alist t-tl (acons rec t-hd acc))))

(define construct-function-hint-alist ((functions smt-function-list-p)
                                       (acc symbol-smt-function-alist-p))
  :returns (type-alst symbol-smt-function-alist-p)
  :measure (len functions)
  (b* ((functions (smt-function-list-fix functions))
       (acc (symbol-smt-function-alist-fix acc))
       ((unless (consp functions)) acc)
       ((cons f-hd f-tl) functions)
       (fn (smt-function->name f-hd))
       ((if (assoc-equal fn acc)) acc))
    (construct-function-hint-alist f-tl (acons fn f-hd acc))))

(define construct-hint-options ((smtlink-hint smtlink-hint-p))
  :returns (hint-options hint-options-p)
  (b* ((smtlink-hint (smtlink-hint-fix smtlink-hint))
       ((smtlink-hint h) smtlink-hint)
       ((mv & supertype) (construct-sub/supertype-alist h.types))
       (type-alst (construct-type-hint-alist h.types nil))
       (func-alst (construct-function-hint-alist h.functions nil)))
    (make-hint-options :supertype supertype
                       :type type-alst
                       :function func-alst)))
