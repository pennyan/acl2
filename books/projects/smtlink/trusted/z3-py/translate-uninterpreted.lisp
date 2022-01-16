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
                                         (func smt-function-p))
  :returns (property pseudo-term-listp)
  (b* ((name (symbol-fix name))
       (func (smt-function-fix func))
       ((smt-function f) func)
       ((trans-hint th) f.translation-hint))
    (uninterpreted-property name th.formal-types th.return-type)))

(define translate-uninterpreted-arguments ((types symbol-listp)
                                           (type-alst symbol-smt-datatype-alist-p))
  :returns (translated paragraph-p)
  :measure (len types)
  (b* ((types (symbol-list-fix types))
       (type-alst (symbol-smt-datatype-alist-fix type-alst))
       ((unless (consp types)) nil)
       ((cons first rest) types)
       (exists? (assoc-equal first type-alst))
       ((unless exists?)
        (er hard? 'translate-uninterpreted=>translate-uninterpreted-arguments
            "Unrecognized type ~p0, consider adding it to the hint.~%" first))
       (translated-type (translate-type (cdr exists?))))
    (cons `(#\, #\Space ,translated-type)
          (translate-uninterpreted-arguments rest type-alst))))

(define translate-one-uninterpreted ((name symbolp)
                                     (func smt-function-p)
                                     (types symbol-smt-datatype-alist-p))
  :returns (translated paragraph-p)
  (b* ((name (symbol-fix name))
       (func (smt-function-fix func))
       (types (symbol-smt-datatype-alist-fix types))
       ((smt-function f) func)
       ((trans-hint th) f.translation-hint)
       (translated-formals
        (translate-uninterpreted-arguments th.formal-types types))
       (translated-returns
        (translate-uninterpreted-arguments (list th.return-type) types)))
    `(,(translate-variable name) "= z3.Function("
      #\' ,name #\' ,translated-formals ,translated-returns
      ")" #\Newline)))

(define translate-uninterpreted ((funcs symbol-smt-function-alist-p)
                                 (types symbol-smt-datatype-alist-p))
  :returns (mv (py-term paragraph-p)
               (smt-property pseudo-term-list-listp))
  :measure (len (symbol-smt-function-alist-fix funcs))
  (b* ((funcs (symbol-smt-function-alist-fix funcs))
       (types (symbol-smt-datatype-alist-fix types))
       ((unless (consp funcs)) (mv nil nil))
       ((cons first rest) funcs)
       ((cons name func) first)
       ((unless (equal (smt-function->kind func) :uninterpreted))
        (translate-uninterpreted rest types))
       (first-decl (translate-one-uninterpreted name func types))
       (first-property (generate-uninterpreted-property name func))
       ((mv rest-decl rest-property) (translate-uninterpreted rest types)))
    (mv (cons first-decl rest-decl)
        (cons first-property rest-property))))
