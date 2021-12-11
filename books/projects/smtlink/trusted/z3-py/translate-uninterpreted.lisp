;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (19th October, 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "../../verified/hint-interface")
(include-book "../property/uninterpreted-property")
(include-book "translate-declarations")
(include-book "datatypes")

(local (in-theory (enable paragraph-p word-p string-or-symbol-p)))

(define generate-uninterpreted-property ((name symbolp)
                                         (hints smt-function-p))
  :returns (property pseudo-term-listp)
  (b* ((name (symbol-fix name))
       (hints (smt-function-fix hints))
       ((smt-function h) hints)
       ((trans-hint th) h.translation-hint))
    (uninterpreted-property name th.formal-types th.return-type)))

(define translate-uninterpreted-arguments ((types symbol-listp)
                                           (type-alst symbol-smt-type-alist-p))
  :returns (translated paragraph-p)
  :measure (len types)
  (b* ((types (symbol-list-fix types))
       (type-alst (symbol-smt-type-alist-fix type-alst))
       ((unless (consp types)) nil)
       ((cons first rest) types)
       (translated-type (translate-type first (cdr (assoc-equal first type-alst)))))
    (cons `(#\, #\Space ,translated-type)
          (translate-uninterpreted-arguments rest type-alst))))

(define translate-one-uninterpreted ((name symbolp)
                                     (hints smt-function-p)
                                     (types symbol-smt-type-alist-p))
  :returns (translated paragraph-p)
  (b* ((name (symbol-fix name))
       (hints (smt-function-fix hints))
       (types (symbol-smt-type-alist-fix types))
       ((smt-function h) hints)
       ((trans-hint th) h.translation-hint)
       (translated-formals
        (translate-uninterpreted-arguments th.formal-types types))
       (translated-returns
        (translate-uninterpreted-arguments (list th.return-type) types)))
    `(,(translate-variable name) "= z3.Function("
      #\' ,name #\' ,translated-formals ,translated-returns
      ")" #\Newline)))

(define translate-uninterpreted ((uninterpreted symbol-smt-function-alist-p)
                                 (types symbol-smt-type-alist-p))
  :returns (mv (py-term paragraph-p)
               (smt-property pseudo-term-list-listp))
  :measure (len (symbol-smt-function-alist-fix uninterpreted))
  (b* ((uninterpreted (symbol-smt-function-alist-fix uninterpreted))
       (types (symbol-smt-type-alist-fix types))
       ((unless (consp uninterpreted)) (mv nil nil))
       ((cons first rest) uninterpreted)
       ((cons name hints) first)
       (first-decl (translate-one-uninterpreted name hints types))
       (first-property (generate-uninterpreted-property name hints))
       ((mv rest-decl rest-property) (translate-uninterpreted rest types)))
    (mv (cons first-decl rest-decl)
        (cons first-property rest-property))))
