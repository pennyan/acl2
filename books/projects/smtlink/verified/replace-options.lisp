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

(define construct-function-replace-alist ((functions smt-function-list-p)
                                          (acc symbol-thm-spec-list-alist-p))
  :returns (replace-alst symbol-thm-spec-list-alist-p)
  :measure (len functions)
  (b* ((functions (smt-function-list-fix functions))
       (acc (symbol-thm-spec-list-alist-fix acc))
       ((unless (consp functions)) acc)
       ((cons f-hd f-tl) functions)
       ((smt-function f) f-hd))
    (construct-function-replace-alist
     f-tl
     (acons f.name
            (construct-replace-spec f.formals f.replace-thms)
            acc))))

(define construct-type-replace ((type smt-type-p)
                                (acc symbol-thm-spec-list-alist-p))
  :returns (replace-alst symbol-thm-spec-list-alist-p)
  (b* ((type (smt-type-fix type))
       (acc (symbol-thm-spec-list-alist-fix acc))
       ((smt-type tp) type)
       (acc-1 (construct-function-replace-alist tp.destructors acc))
       ((smt-function rf) tp.recognizer)
       (acc-2 (acons rf.name
                     (construct-replace-spec rf.formals rf.replace-thms)
                     acc-1))
       ((smt-function ff) tp.fixer)
       (acc-3 (acons ff.name
                     (construct-return-spec ff.formals ff.replace-thms)
                     acc-2))
       ((smt-function cf) tp.constructor))
    (acons cf.name
           (construct-return-spec cf.formals cf.replace-thms)
           acc-3)))

(define construct-type-replace-alist ((types smt-type-list-p)
                                      (acc symbol-thm-spec-list-alist-p))
  :returns (replace-alst symbol-thm-spec-list-alist-p)
  :measure (len types)
  (b* ((types (smt-type-list-fix types))
       (acc (symbol-thm-spec-list-alist-fix acc))
       ((unless (consp types)) acc)
       ((cons type-hd type-tl) types)
       (alst1 (construct-type-replace type-hd acc)))
    (construct-type-replace-alist type-tl alst1)))

(define construct-replace-alist ((funcs smt-function-list-p)
                                 (types smt-type-list-p))
  :returns (replace-alst symbol-thm-spec-list-alist-p)
  (b* ((funcs (smt-function-list-fix funcs))
       (types (smt-type-list-fix types))
       (alst1 (construct-function-replace-alist funcs nil)))
    (construct-type-replace-alist types alst1)))

(define construct-replace-options ((hints smtlink-hint-p))
  :returns (type-alst replace-options-p)
  (b* ((hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       ((mv & supertype) (construct-sub/supertype-alist h.types))
       (replace-alst (construct-replace-alist h.functions h.types)))
    (make-replace-options :supertype supertype
                          :replaces replace-alst)))
