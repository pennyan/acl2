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
(include-book "datatypes")

(local (in-theory (enable paragraph-p word-p string-or-symbol-p)))

(define create-basic-list ((basic symbol-smt-datatype-alist-p)
                           (types symbol-smt-datatype-alist-p)
                           (acc pseudo-term-list-listp))
  :returns (mv (translated paragraph-p)
               (new-acc pseudo-term-list-listp))
  :measure (len (symbol-smt-datatype-alist-fix basic))
  (b* ((basic (symbol-smt-datatype-alist-fix basic))
       (types (symbol-smt-datatype-alist-fix types))
       (acc (pseudo-term-list-list-fix acc))
       ((unless (consp basic)) (mv nil acc))
       ((cons basic-hd basic-tl) basic)
       ((cons & type) basic-hd)
       ((unless (equal (smt-datatype-kind type) :basic)) (mv nil acc))
       (acc-1 (datatype-property type types acc))
       ((mv & acc-2) (create-basic-list basic-tl types acc-1)))
    (mv nil acc-2)))
