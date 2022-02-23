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
(include-book "../../verified/hint-interface")

(define abstract-property ((type smt-datatype-p)
                           (acc pseudo-term-list-listp))
  :guard (equal (smt-datatype-kind type) :abstract)
  :returns (new-acc pseudo-term-list-listp)
  :ignore-ok t
  (pseudo-term-list-list-fix acc))
