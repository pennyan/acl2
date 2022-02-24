;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (11th October, 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "../../verified/hint-interface")
(include-book "../../verified/basics")
(include-book "../property/datatype-property")
(include-book "translate-variable")
(include-book "translate-quote")
(include-book "translate-sumtype")
(include-book "translate-array")
(include-book "translate-abstract")

(local (in-theory (e/d (paragraph-p word-p string-or-symbol-p)
                       (pseudo-termp
                        consp-of-pseudo-lambdap
                        pseudo-lambdap-of-fn-call-of-pseudo-termp
                        true-list-listp))))

(defprod assort-type
  ((basic symbol-smt-datatype-alist-p)
   (sumtype symbol-smt-datatype-alist-p)
   (array symbol-smt-datatype-alist-p)
   (abstract symbol-smt-datatype-alist-p)))

(define assort-type-list ((types symbol-smt-datatype-alist-p)
                          (acc assort-type-p))
  :returns (at assort-type-p)
  :measure (len (symbol-smt-datatype-alist-fix types))
  (b* ((types (symbol-smt-datatype-alist-fix types))
       (acc (assort-type-fix acc))
       ((assort-type a) acc)
       ((unless (consp types)) acc)
       ((cons type-hd type-tl) types)
       ((cons name type) type-hd)
       (new-acc (cond ((equal (smt-datatype-kind type) :basic)
                       (change-assort-type acc :basic (acons name type a.basic)))
                      ((equal (smt-datatype-kind type) :sumtype)
                       (change-assort-type acc :sumtype (acons name type a.sumtype)))
                      ((equal (smt-datatype-kind type) :array)
                       (change-assort-type acc :array (acons name type a.array)))
                      (t (change-assort-type acc :abstract (acons name type a.abstract))))))
    (assort-type-list type-tl new-acc)))

(define create-datatypes ((hint trusted-hint-p)
                          (symbol-map symbol-string-alistp))
  :returns (mv (translated paragraph-p)
               (properties pseudo-term-list-listp))
  (b* ((hint (trusted-hint-fix hint))
       ((trusted-hint h) hint)
       ((assort-type at) (assort-type-list h.user-types (make-assort-type)))
       ((mv trans1 prop1)
        (create-sumtype-list-top at.sumtype symbol-map h.user-types))
       ((mv trans2 prop2) (create-array-list at.array h prop1))
       ((mv trans3 prop3) (create-abstract-list at.abstract h.user-types prop2)))
    (mv `(,trans1 ,trans2 ,trans3) prop3)))
