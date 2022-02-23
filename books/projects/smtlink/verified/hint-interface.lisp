;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/alists/alist-fix" :dir :system)

(include-book "../config")
(include-book "../utils/basics")
(include-book "../utils/pseudo-term")

;; (defsection SMT-hint-interface
;;   :parents (verified)
;;   :short "Define default Smtlink hint interface"

(local (in-theory (disable pseudo-termp pseudo-term-listp
                           ACL2::PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP
                           ACL2::PSEUDO-TERM-LISTP-OF-CAR-WHEN-PSEUDO-TERM-LIST-LISTP
                           PSEUDO-TERM-LIST-LISTP
                           PSEUDO-LAMBDAP-OF-FN-CALL-OF-PSEUDO-TERMP)))

(defprod thm-spec
  ((thm symbolp)
   (formals symbol-listp)
   (hypotheses pseudo-termp :default ''t)
   (lhs pseudo-termp :default ''nil)
   (rhs pseudo-termp :default ''nil)
   (judgements pseudo-term-listp)
   (var-term pseudo-termp)
   (var-hyp pseudo-termp :default ''t)
   (hyp-judge pseudo-termp :default ''t)
   (hints true-listp)))

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

(defprod trans-hint
  ((type stringp :default "")
   (translation stringp :default "")
   (formal-types symbol-listp)
   (return-type symbolp)
   (fn-to-const booleanp)))

(defprod smt-function
  :parents (smtlink-hint)
  ((name symbolp)
   (returns thm-spec-list-p)
   (uninterpreted-hints true-listp)
   (depth natp :default 0)
   (kind symbolp) ;; :basic :type :uninterpreted
   (translation-hint trans-hint-p :default (make-trans-hint))))

(defoption maybe-smt-function smt-function-p)

(deflist smt-function-list
  :parents (smt-function)
  :elt-type smt-function-p
  :true-listp t)

(defprod smt-config
  ((smt-cnf smtlink-config-p :default (make-smtlink-config))
   (rm-file booleanp :default t)
   (smt-dir stringp :default "")
   (smt-fname stringp :default "")))

(deftagsum int-to-rat
  (:switch ((okp booleanp :default nil)))
  (:symbol-list ((lst symbol-listp :default nil))))

(defprod smt-hypo
  ((thm symbolp)
   (subst symbol-pseudo-term-alistp)))

(deflist smt-hypo-list
  :elt-type smt-hypo-p
  :true-listp t)

(defprod smt-sub/supertype
  ((type symbolp)
   (thm thm-spec-p :default (make-thm-spec))))

(deflist smt-sub/supertype-list
  :elt-type smt-sub/supertype-p
  :true-listp t)

(defprod smt-sum
  ((tag symbolp :default nil)
   (constructor smt-function-p :default (make-smt-function))
   (destructors smt-function-list-p)))

(deflist smt-sum-list
  :elt-type smt-sum-p
  :true-listp t)

(defprod init
  ((fn smt-function-p :default (make-smt-function))
   (val symbolp)))

(deftagsum smt-datatype
  (:basic ((recognizer smt-function-p :default (make-smt-function))))
  (:sumtype ((kind maybe-smt-function-p)
             (recognizer smt-function-p :default (make-smt-function))
             (sums smt-sum-list-p)))
  (:array ((recognizer smt-function-p :default (make-smt-function))
           (key-type symbolp)
           (val-type symbolp)
           (init init-p :default (make-init))
           (select smt-function-p :default (make-smt-function))
           (store smt-function-p :default (make-smt-function))
           (equal smt-function-p :default (make-smt-function))
           (equal-witness smt-function-p :default (make-smt-function))))
  (:abstract ((recognizer smt-function-p :default (make-smt-function)))))

(define smt-datatype->recognizer ((type smt-datatype-p))
  :returns (rec smt-function-p)
  (b* ((type (smt-datatype-fix type)))
    (cond ((equal (smt-datatype-kind type) :basic)
           (smt-datatype-basic->recognizer type))
          ((equal (smt-datatype-kind type) :sumtype)
           (smt-datatype-sumtype->recognizer type))
          ((equal (smt-datatype-kind type) :array)
           (smt-datatype-array->recognizer type))
          ((equal (smt-datatype-kind type) :abstract)
           (smt-datatype-abstract->recognizer type)))))

(deflist smt-datatype-list
  :elt-type smt-datatype-p
  :true-listp t)

(defoption maybe-smt-datatype
  smt-datatype-p)

(defprod smt-acl2type
  ((recognizer symbolp)
   (subtypes smt-sub/supertype-list-p :default nil)
   (supertypes smt-sub/supertype-list-p :default nil)))

(deflist smt-acl2type-list
  :elt-type smt-acl2type-p
  :true-listp t)

(defalist symbol-smt-acl2type-alist
  :key-type symbolp
  :val-type smt-acl2type-p
  :true-listp t)

(defalist symbol-smt-function-alist
  :key-type symbolp
  :val-type smt-function-p
  :true-listp t)

(defthm assoc-equal-of-symbol-smt-function-alist
  (implies (and (symbol-smt-function-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (smt-function-p (cdr (assoc-equal x alst))))))

(defalist symbol-smt-datatype-alist
  :key-type symbolp
  :val-type smt-datatype-p
  :true-listp t)

(defthm assoc-equal-of-symbol-smt-datatype-alist
  (implies (and (symbol-smt-datatype-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (smt-datatype-p (cdr (assoc-equal x alst))))))

(defalist symbol-trans-hint-alist
  :key-type symbolp
  :val-type trans-hint-p
  :true-listp t)

(defthm assoc-equal-of-symbol-trans-hint-alist
  (implies (and (symbol-trans-hint-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (trans-hint-p (cdr (assoc-equal x alst))))))

(defprod trusted-hint
  ((user-types symbol-smt-datatype-alist-p)
   (user-fns symbol-smt-function-alist-p)))

(local (in-theory (disable symbol-listp)))

(defprod smtlink-hint
  :parents (SMT-hint-interface)
  ((functions smt-function-list-p :default nil)
   (acl2types smt-acl2type-list-p :default nil)
   (datatypes smt-datatype-list-p :default nil)
   (replaces thm-spec-list-p :default nil)
   (hypotheses smt-hypo-list-p :default nil)
   (configurations smt-config-p :default (make-smt-config))
   (int-to-ratp int-to-rat-p :default (make-int-to-rat-switch :okp nil))
   (under-inductionp symbolp :default nil)
   (global-hint symbolp :default nil)
   (wrld-fn-len natp :default 0)
   (customp booleanp :default nil)
   (trusted-hint trusted-hint-p :default (make-trusted-hint))))

(defalist smtlink-hint-alist
  :key-type symbolp
  :val-type smtlink-hint-p
  :true-listp t)

(defthm assoc-equal-of-smtlink-hint-alist
  (implies (and (smtlink-hint-alist-p alst)
                (assoc-equal x alst))
           (smtlink-hint-p (cdr (assoc-equal x alst)))))

;; type-alst could be symbol-symbol-alistp or type-to-types-alist-p
(define is-type? ((type symbolp)
                  (type-alst alistp))
  :returns (ok booleanp)
  (b* ((type-alst (acl2::alist-fix type-alst))
       (type (symbol-fix type)))
    (not (null (assoc-equal type type-alst)))))
