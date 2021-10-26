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

(define construct-replace-spec ((formals symbol-listp)
                                (replace-lst symbol-listp))
  :returns (replace-spec-lst thm-spec-list-p)
  :measure (len replace-lst)
  (b* ((formals (symbol-list-fix formals))
       (replace-lst (symbol-list-fix replace-lst))
       ((unless (consp replace-lst)) nil)
       ((cons replace-hd replace-tl) replace-lst))
    (cons (make-thm-spec :formals formals :thm replace-hd)
          (construct-replace-spec formals replace-tl))))

(define construct-replace-alist ((functions smt-function-list-p))
  :returns (replace-alst symbol-thm-spec-list-alist-p)
  :measure (len functions)
  (b* ((functions (smt-function-list-fix functions))
       ((unless (consp functions)) nil)
       ((cons f-hd f-tl) functions)
       ((smt-function f) f-hd))
    (acons f.name (construct-replace-spec f.formals f.replace-thms)
           (construct-replace-alist f-tl))))

(define construct-replace-options ((hints smtlink-hint-p))
  :returns (type-alst replace-options-p)
  (b* ((hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       ((mv & supertype) (construct-sub/supertype-alist h.types))
       (replace-alst (construct-replace-alist h.functions)))
    (make-replace-options :supertype supertype
                          :replaces replace-alst)))
