;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (7th March 2022)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "stringify")
(include-book "hint-interface")

(local (in-theory (enable stringable-list-p)))

(define property-name ((type symbolp)
                       (constructor symbolp)
                       (which symbolp))
  :returns (thm-name symbolp)
  (b* ((type (symbol-fix type))
       (constructor (symbol-fix constructor))
       (which (symbol-fix which)))
    (case which
      ;; recognizer
      (:type-of-recognizer (mk-symbol `("type" "of" ,type) type))
      ;; equal
      (:type-of-equal (mk-symbol `("type" "of" ,type "equal") type))
      (:reflexivity-of-equal
       (mk-symbol `("reflexivity" "of" ,type "equal") type))
      (:symmetricity-of-equal
       (mk-symbol `("symmetricity" "of" ,type "equal") type))
      (:transitivity-of-equal
       (mk-symbol `("transitivity" "of" ,type "equal") type))
      ;; sumtype
      (:type-of-constructor
       (mk-symbol `("type" "of" ,constructor) type))
      (:type-of-destructors
       (mk-symbol `("type" "of" ,constructor "destructors") type))
      (:constructor-of-destructor
       (mk-symbol `("uniqueness" "of" ,type "constructor" "of" "destructors") type))
      (:destructor-of-constructor
       (mk-symbol `("destructors" "of" ,constructor) type))
      (:constructor-of-destructor-with-tag
       (mk-symbol `(,constructor "of" "destructors") type))
      (:tag-of-constructor (mk-symbol `("tag" "of" ,constructor) type))
      (:tag-uniqueness (mk-symbol `("tag" "uniqueness" "of" ,type) type))
      ;; array
      (:type-of-init (mk-symbol `("type" "of" ,type "init") type))
      (:equal-of-init (mk-symbol `("equal" "of" ,type "init") type))
      (:type-of-array-select (mk-symbol `("type" "of" ,type "select") type))
      (:array-select-equal (mk-symbol `(,type "select" "equal") type))
      (:array-select-distinct (mk-symbol `(,type "select" "distinct") type))
      (:type-of-array-store (mk-symbol `("type" "of" ,type "store") type))
      (:array-equal-implies-select-equal
       (mk-symbol `(,type "equal" "implies" "select" "equal") type))
      (:select-of-witness-equal-implies-array-equal
       (mk-symbol
        `("select" "of" "witness" "equal" "implies" ,type "equal") type))
      (otherwise (er hard? 'property-name=>property-name
                     "INTERNAL: Unrecognized property theorem kind.~%")))))

(define get-hints ((type symbolp)
                   (constructor symbolp)
                   (which symbolp)
                   (property-hints symbol-hints-alist-p))
  :returns (hints true-listp)
  (b* ((type (symbol-fix type))
       (constructor (symbol-fix constructor))
       (which (symbol-fix which))
       (property-hints (symbol-hints-alist-fix property-hints))
       (thm-name (property-name type constructor which))
       (exists? (assoc-equal thm-name property-hints))
       ((if exists?) (cdr exists?)))
    `(:in-theory (enable ,thm-name))))
