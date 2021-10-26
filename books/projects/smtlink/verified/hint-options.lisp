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

(defprod hint-options
  ((supertype type-to-types-alist-p)))

(define construct-hint-options ((smtlink-hint smtlink-hint-p))
  :returns (hint-options hint-options-p)
  (b* ((smtlink-hint (smtlink-hint-fix smtlink-hint))
       ((smtlink-hint h) smtlink-hint)
       ((mv & supertype) (construct-sub/supertype-alist h.types)))
    (make-hint-options :supertype supertype)))
