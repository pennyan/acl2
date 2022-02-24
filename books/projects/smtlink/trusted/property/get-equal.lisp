;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (Feb 24th 2022)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "../../verified/hint-interface")

(define get-equal-from-type ((type smt-datatype-p))
  :returns (equal-name symbolp)
  (b* ((type (smt-datatype-fix type))
       (equal-fn (smt-datatype->equal type))
       ((smt-function e) equal-fn)
       ((if (equal e.name 'quote))
        (er hard? 'get-equal=>get-equal
            "Function name should not be 'quote.~%")))
    e.name)
  ///
  (more-returns
   (equal-name (not (equal equal-name 'quote))
               :name get-equal-from-type-not-quote)))

(define get-equal-from-type-alist ((type symbolp)
                                   (types symbol-smt-datatype-alist-p))
  :returns (equal symbolp)
  (b* ((type (symbol-fix type))
       (types (symbol-smt-datatype-alist-fix types))
       (exists? (assoc-equal type types))
       ((unless exists?)
        (er hard? 'get-equal=>get-equal
            "Type ~p0 doesn't exist in the hint.~%" type))
       (equal-fn (smt-datatype->equal (cdr exists?)))
       ((smt-function e) equal-fn)
       ((if (equal e.name 'quote))
        (er hard? 'get-equal=>get-equal
            "Function name should not be 'quote.~%")))
    e.name)
  ///
  (more-returns
   (equal (not (equal equal 'quote))
          :name get-equal-from-type-alist-not-quote)))
