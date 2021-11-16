;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "clause-processors/term-vars" :dir :system)

(include-book "hint-interface")

(defalist type-to-types-alist
  :key-type symbolp
  :val-type smt-sub/supertype-list-p
  :true-listp t)

(defthm assoc-equal-of-type-to-types-alist
  (implies (and (type-to-types-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (smt-sub/supertype-list-p (cdr (assoc-equal x alst))))))

(defprod thm-spec
  ((formals symbol-listp)
   (thm symbolp)))

(deflist thm-spec-list
  :elt-type thm-spec-p
  :true-listp t)

(defalist symbol-thm-spec-list-alist
  :key-type symbolp
  :val-type thm-spec-list-p
  :true-listp t)

(defthm assoc-equal-of-symbol-thm-spec-list-alist
  (implies (and (symbol-thm-spec-list-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (thm-spec-list-p (cdr (assoc-equal x alst))))))

(defprod type-options
  ((supertype type-to-types-alist-p)
   (subtype type-to-types-alist-p)
   (functions symbol-thm-spec-list-alist-p)
   (names symbol-listp)))

(define is-type? ((type symbolp)
                  (supertype-alst type-to-types-alist-p))
  :returns (ok booleanp)
  (b* ((supertype-alst (type-to-types-alist-fix supertype-alst))
       (type (symbol-fix type)))
    (not (null (assoc-equal type supertype-alst)))))

(define construct-sub/supertype-alist ((types smt-type-list-p))
  :returns (mv (subtype type-to-types-alist-p)
               (supertype type-to-types-alist-p))
  :measure (len types)
  (b* ((types (smt-type-list-fix types))
       ((unless (consp types)) (mv nil nil))
       ((cons types-hd types-tl) types)
       ((smt-type tp) types-hd)
       ((mv subtype-tl supertype-tl)
        (construct-sub/supertype-alist types-tl)))
    (mv (acons (smt-function->name tp.recognizer) tp.subtypes subtype-tl)
        (acons (smt-function->name tp.recognizer) tp.supertypes supertype-tl))))

(define construct-return-spec ((formals symbol-listp)
                               (return-lst symbol-listp))
  :returns (return-spec-lst thm-spec-list-p)
  :measure (len return-lst)
  (b* ((formals (symbol-list-fix formals))
       (return-lst (symbol-list-fix return-lst))
       ((unless (consp return-lst)) nil)
       ((cons return-hd return-tl) return-lst))
    (cons (make-thm-spec :formals formals :thm return-hd)
          (construct-return-spec formals return-tl))))

(define construct-function-alist ((funcs smt-function-list-p)
                                  (acc symbol-thm-spec-list-alist-p))
  :returns (func-alst symbol-thm-spec-list-alist-p)
  :measure (len funcs)
  (b* ((funcs (smt-function-list-fix funcs))
       (acc (symbol-thm-spec-list-alist-fix acc))
       ((unless (consp funcs)) acc)
       ((cons f-hd f-tl) funcs)
       ((smt-function f) f-hd)
       ((if (assoc-equal f.name acc))
        (construct-function-alist f-tl acc)))
    (construct-function-alist f-tl
                              (acons f.name
                                     (construct-return-spec f.formals f.returns)
                                     acc))))

(define construct-sum-function ((sum smt-sum-p)
                                (acc symbol-thm-spec-list-alist-p))
  :returns (func-alst symbol-thm-spec-list-alist-p)
  (b* ((sum (smt-sum-fix sum))
       (acc (symbol-thm-spec-list-alist-fix acc))
       ((smt-sum s) sum)
       (acc-1 (construct-function-alist s.destructors acc))
       ((smt-function cf) s.constructor))
    (acons cf.name
           (construct-return-spec cf.formals cf.returns)
           acc-1)))

(define construct-sum-function-list ((sum-lst smt-sum-list-p)
                                     (acc symbol-thm-spec-list-alist-p))
  :returns (func-alst symbol-thm-spec-list-alist-p)
  :measure (len sum-lst)
  (b* ((sum-lst (smt-sum-list-fix sum-lst))
       (acc (symbol-thm-spec-list-alist-fix acc))
       ((unless (consp sum-lst)) acc)
       ((cons sum-hd sum-tl) sum-lst)
       (acc-1 (construct-sum-function sum-hd acc)))
    (construct-sum-function-list sum-tl acc-1)))

(define construct-type-function ((type smt-type-p)
                                 (acc symbol-thm-spec-list-alist-p))
  :returns (func-alst symbol-thm-spec-list-alist-p)
  (b* ((type (smt-type-fix type))
       (acc (symbol-thm-spec-list-alist-fix acc))
       ((smt-type tp) type)
       ((smt-function rf) tp.recognizer)
       (acc-1 (acons rf.name
                     (construct-return-spec rf.formals rf.returns)
                     acc))
       ((smt-function ff) tp.fixer)
       (acc-2 (acons ff.name
                     (construct-return-spec ff.formals ff.returns)
                     acc-1)))
    (construct-sum-function-list tp.sums acc-2)))

(define construct-type-function-alist ((types smt-type-list-p)
                                       (acc symbol-thm-spec-list-alist-p))
  :returns (func-alst symbol-thm-spec-list-alist-p)
  :measure (len types)
  (b* ((types (smt-type-list-fix types))
       (acc (symbol-thm-spec-list-alist-fix acc))
       ((unless (consp types)) acc)
       ((cons type-hd type-tl) types)
       (alst1 (construct-type-function type-hd acc)))
    (construct-type-function-alist type-tl alst1)))

(define construct-all-functions ((funcs smt-function-list-p)
                                 (types smt-type-list-p))
  :returns (func-alst symbol-thm-spec-list-alist-p)
  (b* ((funcs (smt-function-list-fix funcs))
       (types (smt-type-list-fix types))
       (alst1 (construct-function-alist funcs nil)))
    (construct-type-function-alist types alst1)))

(define construct-type-options ((smtlink-hint smtlink-hint-p)
                                (term pseudo-termp))
  :returns (type-options type-options-p)
  (b* ((smtlink-hint (smtlink-hint-fix smtlink-hint))
       (term (pseudo-term-fix term))
       ((smtlink-hint h) smtlink-hint)
       ((mv subtype supertype) (construct-sub/supertype-alist h.types))
       (functions (construct-all-functions h.functions h.types))
       (names (acl2::simple-term-vars term)))
    (make-type-options :supertype supertype
                       :subtype subtype
                       :functions functions
                       :names names)))
