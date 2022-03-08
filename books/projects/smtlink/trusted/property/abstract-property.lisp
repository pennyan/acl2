;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (Feb 22nd 2022)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "../../utils/basics")
(include-book "../../utils/fresh-vars")
(include-book "recognizer-property")
(include-book "equality-property")

(define abstract-property ((type smt-datatype-p)
                           (acc pseudo-term-list-listp))
  :guard (equal (smt-datatype-kind type) :abstract)
  :returns (new-acc pseudo-term-list-listp)
  (b* ((type (smt-datatype-fix type))
       (acc (pseudo-term-list-list-fix acc))
       (acc-1 (recognizer-property type acc)))
    (equality-property type acc-1)))
