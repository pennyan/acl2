;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (September 22th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "hint-interface")
(include-book "type-options")

(defprod replace-options
  ((supertype type-to-types-alist-p)
   (replaces symbol-thm-spec-list-alist-p)))

(define construct-replace-alist ((replace-lst smt-replace-list-p)
                                 (acc symbol-thm-spec-list-alist-p))
  :returns (replace-alst symbol-thm-spec-list-alist-p)
  :measure (len replace-lst)
  (b* ((replace-lst (smt-replace-list-fix replace-lst))
       (acc (symbol-thm-spec-list-alist-fix acc))
       ((unless (consp replace-lst)) acc)
       ((cons rep-hd rep-tl) replace-lst)
       ((smt-replace r) rep-hd)
       (exists? (assoc-equal r.fn acc))
       ((if exists?) (construct-replace-alist rep-tl acc))
       (new-acc (acons r.fn r.thms acc)))
    (construct-replace-alist rep-tl new-acc)))

(define construct-replace-options ((hints smtlink-hint-p))
  :returns (type-alst replace-options-p)
  (b* ((hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       ((mv & supertype) (construct-sub/supertype-alist h.types))
       (replace-alst (construct-replace-alist h.replaces nil)))
    (make-replace-options :supertype supertype
                          :replaces replace-alst)))
