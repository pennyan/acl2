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

(define construct-reorder-type-alist ((type-lst smt-acl2type-list-p))
  :returns (alst symbol-symbol-alistp)
  :measure (len type-lst)
  (b* ((type-lst (smt-acl2type-list-fix type-lst))
       ((unless (consp type-lst)) nil)
       ((cons type-hd type-tl) type-lst)
       ((smt-acl2type at) type-hd))
    (acons at.recognizer nil
           (construct-reorder-type-alist type-tl))))

(define construct-reorder-options ((hints smtlink-hint-p))
  :returns (type-alst symbol-symbol-alistp)
  (b* ((hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints))
    (construct-reorder-type-alist h.acl2types)))
