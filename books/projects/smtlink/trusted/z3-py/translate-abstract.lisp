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
(include-book "translate-type")

(define create-abstract-type ((type smt-datatype-p))
  :guard (equal (smt-datatype-kind type) :abstract)
  :returns (translated paragraph-p)
  (b* ((type (smt-datatype-fix type))
       (name (translate-type type)))
    `(,name "= DeclareSort('" ,name "')" #\Newline)))

(define create-abstract-list ((abs symbol-smt-datatype-alist-p)
                              (acc pseudo-term-list-listp))
  :returns (mv (translated paragraph-p)
               (new-acc pseudo-term-list-listp))
  :measure (len (symbol-smt-datatype-alist-fix abs))
  (b* ((abs (symbol-smt-datatype-alist-fix abs))
       (acc (pseudo-term-list-list-fix acc))
       ((unless (consp abs)) (mv nil acc))
       ((cons abs-hd abs-tl) abs)
       ((cons & type) abs-hd)
       ((unless (equal (smt-datatype-kind type) :abstract)) (mv nil acc))
       (abs-decl (create-abstract-type type))
       (acc-1 (datatype-property type acc))
       ((mv trans-tl acc-2) (create-abstract-list abs-tl acc-1)))
    (mv (cons abs-decl trans-tl) acc-2)))
