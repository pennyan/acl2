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

(include-book "../config")
(include-book "../utils/basics")
(include-book "../utils/pseudo-term")

;; (defsection SMT-hint-interface
;;   :parents (verified)
;;   :short "Define default Smtlink hint interface"

(local (in-theory (disable pseudo-termp pseudo-term-listp)))

(defprod trans-hint
  ((type-translation symbolp)
   (function-translation symbolp)
   (formal-types symbol-listp)
   (return-type symbolp)
   (kind symbolp)))

(defprod smt-function
  :parents (smtlink-hint)
  ((name symbolp :default nil)
   (formals symbol-listp :default nil)
   (returns symbol-listp :default nil)
   (translation-hint trans-hint-p :default (make-trans-hint))
   (uninterpreted-hints true-listp :default nil)
   (depth natp :default 0)))

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
   (formals symbol-listp)
   (thm symbolp)))

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

(defprod smt-type
  ((kind maybe-smt-function-p)
   (recognizer smt-function-p :default (make-smt-function))
   (fixer smt-function-p :default (make-smt-function))
   (sums smt-sum-list-p)
   (subtypes smt-sub/supertype-list-p)
   (supertypes smt-sub/supertype-list-p)))

(deflist smt-type-list
  :elt-type smt-type-p
  :true-listp t)

(defoption maybe-smt-type
  smt-type-p)

(defalist symbol-smt-function-alist
  :key-type symbolp
  :val-type smt-function-p
  :true-listp t)

(defthm assoc-equal-of-symbol-smt-function-alist
  (implies (and (symbol-smt-function-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (smt-function-p (cdr (assoc-equal x alst))))))

(defalist symbol-smt-type-alist
  :key-type symbolp
  :val-type smt-type-p
  :true-listp t)

(defthm assoc-equal-of-symbol-smt-type-alist
  (implies (symbol-smt-type-alist-p alst)
           (maybe-smt-type-p (cdr (assoc-equal x alst)))))

(defprod smt-replace
  ((fn symbolp)
   (formals symbol-listp)
   (thms symbol-listp)))

(deflist smt-replace-list
  :elt-type smt-replace-p
  :true-listp t)

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
  ((user-fns symbol-trans-hint-alist-p)
   (user-types symbol-smt-type-alist-p)))

(local (in-theory (disable symbol-listp)))

(defprod smtlink-hint
  :parents (SMT-hint-interface)
  ((functions smt-function-list-p :default nil)
   (types smt-type-list-p :default nil)
   (replaces smt-replace-list-p :default nil)
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
