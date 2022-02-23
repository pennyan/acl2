;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (19th October, 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "sumtype-property")
(include-book "array-property")
(include-book "abstract-property")
(include-book "basic-property")

(define datatype-property ((type smt-datatype-p)
                           (acc pseudo-term-list-listp))
  :returns (new-acc pseudo-term-list-listp)
  (b* ((type (smt-datatype-fix type))
       (acc (pseudo-term-list-list-fix acc)))
    (cond ((equal (smt-datatype-kind type) :sumtype)
           (sumtype-property type acc))
          ((equal (smt-datatype-kind type) :array)
           (array-property type acc))
          ((equal (smt-datatype-kind type) :abstract)
           (abstract-property type acc))
          (t (basic-property type acc)))))
