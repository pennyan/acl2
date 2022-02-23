;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (11th October, 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "../../verified/hint-interface")
(include-book "../../verified/basics")
(include-book "../property/datatype-property")
(include-book "translate-variable")
(include-book "translate-quote")
(include-book "translate-type")

(local (in-theory (enable paragraph-p word-p string-or-symbol-p)))

(define create-array-type ((type smt-datatype-p)
                           (types symbol-smt-datatype-alist-p))
  :guard (equal (smt-datatype-kind type) :array)
  :returns (translated paragraph-p)
  (b* ((type (smt-datatype-fix type))
       ((unless (mbt (equal (smt-datatype-kind type) :array))) nil)
       (types (symbol-smt-datatype-alist-fix types))
       (key-type (smt-datatype-array->key-type type))
       (key-exists? (assoc-equal key-type types))
       ((unless key-exists?)
        (er hard? 'translate-array=>create-array-type
            "Unrecognized type ~p0, consider adding it to the hint.~%"
            key-type))
       (val-type (smt-datatype-array->val-type type))
       (val-exists? (assoc-equal val-type types))
       ((unless val-exists?)
        (er hard? 'translate-array=>create-array-type
            "Unrecognized type ~p0, consider adding it to the hint.~%"
            val-type))
       (name (translate-type type)))
    `(,name " = ArraySort( "
            ,(translate-type (cdr key-exists?)) " ,"
            ,(translate-type (cdr val-exists?)) " )" #\Newline)))

(define create-array-init ((type smt-datatype-p)
                           (hint trusted-hint-p))
  :guard (equal (smt-datatype-kind type) :array)
  :returns (translated paragraph-p)
  (b* ((type (smt-datatype-fix type))
       (hint (trusted-hint-fix hint))
       ((trusted-hint h) hint)
       (key-type (smt-datatype-array->key-type type))
       (key-exists? (assoc-equal key-type h.user-types))
       ((unless key-exists?)
        (er hard? 'translate-array=>create-array-init
            "Unrecognized type ~p0, consider adding it to the hint.~%"
            key-type))
       (init (smt-datatype-array->init type))
       ((init i) init)
       (init-fn (translate-variable
                 (trans-hint->translation
                  (smt-function->translation-hint i.fn))))
       ((mv val to-const?) (translate-function-name i.val h))
       (val-const (if to-const? val `(,val "()"))))
    `("def " ,init-fn "(): return K("
      ,(translate-type (cdr key-exists?)) " ,"
      ,val-const ")" #\Newline)))

(define create-array-list ((arrays symbol-smt-datatype-alist-p)
                           (hint trusted-hint-p)
                           (acc pseudo-term-list-listp))
  :returns (mv (translated paragraph-p)
               (properties pseudo-term-list-listp))
  :measure (len (symbol-smt-datatype-alist-fix arrays))
  (b* ((arrays (symbol-smt-datatype-alist-fix arrays))
       (hint (trusted-hint-fix hint))
       (acc (pseudo-term-list-list-fix acc))
       ((trusted-hint h) hint)
       ((unless (consp arrays)) (mv nil acc))
       ((cons array-hd array-tl) arrays)
       ((cons & type) array-hd)
       ((unless (equal (smt-datatype-kind type) :array)) (mv nil acc))
       (array-decl (create-array-type type h.user-types))
       (array-init (create-array-init type h))
       (acc-1 (datatype-property type acc))
       ((mv trans-tl acc-2) (create-array-list array-tl h acc-1)))
    (mv (cons `(,array-decl ,array-init) trans-tl) acc-2)))
