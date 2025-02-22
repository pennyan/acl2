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
(include-book "scc")
(include-book "translate-variable")
(include-book "translate-quote")
(include-book "translate-sumtype")
(include-book "translate-array")
(include-book "translate-abstract")
(include-book "translate-basic")

(local (in-theory (e/d (paragraph-p word-p string-or-symbol-p)
                       (pseudo-termp
                        consp-of-pseudo-lambdap
                        pseudo-lambdap-of-fn-call-of-pseudo-termp
                        true-list-listp))))

(define which-scc-p ((types symbol-smt-datatype-alist-p)
                     (kind symbolp))
  :returns (okp booleanp)
  :measure (len (symbol-smt-datatype-alist-fix types))
  (b* ((types (symbol-smt-datatype-alist-fix types))
       (kind (symbol-fix kind))
       ((unless (consp types)) t)
       ((cons type-hd type-tl) types)
       ((cons & type) type-hd)
       ((unless (equal (smt-datatype-kind type) kind)) nil))
    (which-scc-p type-tl kind)))

(define create-datatype-scc ((types symbol-smt-datatype-alist-p)
                             (hint trusted-hint-p)
                             (symbol-map symbol-string-alistp)
                             (prop-acc pseudo-term-list-listp))
  :returns (mv (translated paragraph-p)
               (properties pseudo-term-list-listp))
  (b* ((types (symbol-smt-datatype-alist-fix types))
       (hint (trusted-hint-fix hint))
       ((trusted-hint h) hint)
       (symbol-map (symbol-string-alist-fix symbol-map))
       (prop-acc (pseudo-term-list-list-fix prop-acc)))
    (cond ((which-scc-p types :sumtype)
           (create-sumtype-list-top types symbol-map h.user-types))
          ((which-scc-p types :array) (create-array-list types h prop-acc))
          ((which-scc-p types :abstract)
           (create-abstract-list types h.user-types prop-acc))
          ((which-scc-p types :basic)
           (create-basic-list types h.user-types prop-acc))
          (t (prog2$ (er hard? 'translate-user-type=>create-datatype-scc
                         "Unsupported type declarations: ~q0" types)
                     (mv nil nil))))))

(define get-types-of-scc ((type-lst symbol-listp)
                          (types symbol-smt-datatype-alist-p))
  :returns (type-lst symbol-smt-datatype-alist-p)
  :measure (len type-lst)
  (b* ((type-lst (symbol-list-fix type-lst))
       (types (symbol-smt-datatype-alist-fix types))
       ((unless (consp type-lst)) nil)
       ((cons type-hd type-tl) type-lst)
       (exists? (assoc-equal type-hd types))
       ((unless exists?)
        (er hard? 'translate-user-type=>get-types-of-scc
            "INTERNAL: type ~p0 doesn't exist.~%" type-hd)))
    (acons type-hd (cdr exists?) (get-types-of-scc type-tl types))))

(define create-datatypes-helper ((hint trusted-hint-p)
                                 (symbol-map symbol-string-alistp)
                                 (scc-alst integer-symbol-list-alistp)
                                 (order-lst integer-listp)
                                 (prop-acc pseudo-term-list-listp))
  :measure (len order-lst)
  :returns (mv (translated paragraph-p)
               (properties pseudo-term-list-listp))
  (b* ((hint (trusted-hint-fix hint))
       ((trusted-hint h) hint)
       (scc-alst (integer-symbol-list-alist-fix scc-alst))
       (order-lst (acl2::integer-list-fix order-lst))
       (prop-acc (pseudo-term-list-list-fix prop-acc))
       ((unless (consp order-lst)) (mv nil prop-acc))
       ((cons order-hd order-tl) order-lst)
       (type-lst (cdr (assoc-equal order-hd scc-alst)))
       ((mv trans-hd prop-hd)
        (create-datatype-scc (get-types-of-scc type-lst h.user-types)
                             h symbol-map prop-acc))
       ((mv trans-tl prop-tl)
        (create-datatypes-helper hint symbol-map scc-alst order-tl prop-hd)))
    (mv (cons trans-hd trans-tl) prop-tl)))

(define create-datatypes ((hint trusted-hint-p)
                          (symbol-map symbol-string-alistp))
  :returns (mv (translated paragraph-p)
               (properties pseudo-term-list-listp))
  (b* ((hint (trusted-hint-fix hint))
       ((trusted-hint h) hint)
       ((scc-info i) h.scc-info))
    (create-datatypes-helper h symbol-map i.scc i.order nil)))
