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

(define recognizer-property ((type smt-datatype-p)
                             (acc pseudo-term-list-listp))
  :returns (new-acc pseudo-term-list-listp)
  (b* ((type (smt-datatype-fix type))
       (acc (pseudo-term-list-list-fix acc))
       (rec (smt-datatype->recognizer type))
       ((smt-function r) rec))
    (cons (list `(booleanp (,r.name x))) acc)))
