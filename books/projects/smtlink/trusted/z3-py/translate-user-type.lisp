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
(include-book "../property/construct-product")
(include-book "datatypes")
(include-book "translate-variable")

(local (in-theory (enable paragraph-p word-p string-or-symbol-p)))

(define translate-type ((type symbolp)
                        (type-info maybe-smt-type-p))
  :returns (translated stringp)
  (b* ((type (symbol-fix type))
       (type-info (maybe-smt-type-fix type-info))
       (basic? (assoc-equal type *SMT-types*))
       ((if basic?) (cdr basic?))
       ((unless type-info) (translate-variable type)))
    (translate-variable
     (smt-function->translation (smt-type->recognizer type-info))))
  ///
  (more-returns
   (translated (paragraph-p translated)
               :name paragraph-of-translate-type)))

(define create-destructor ((destructor smt-function-p)
                           (type smt-type-p))
  :returns (translated paragraph-p)
  (b* ((destructor (smt-function-fix destructor))
       ((smt-function f) destructor))
    `("('" ,(translate-variable f.translation) "', "
      ,(translate-type f.return-type type) ")")))

(define create-destructors ((destructors smt-function-list-p)
                            (type smt-type-p))
  :returns (translated paragraph-p)
  :measure (len destructors)
  (b* ((destructors (smt-function-list-fix destructors))
       (type (smt-type-fix type))
       ((unless (consp destructors)) nil)
       ((cons des-hd des-tl) destructors))
    `(", " ,(create-destructor des-hd type)
      ,@(create-destructors des-tl type))))

(define create-product-type ((type smt-type-p)
                             (acc pseudo-term-list-listp))
  :returns (mv (translated paragraph-p)
               (properties pseudo-term-list-listp))
  (b* ((type (smt-type-fix type))
       (acc (pseudo-term-list-list-fix acc))
       ((smt-type tp) type)
       (- (cw "smt-type: ~q0" type))
       (name (translate-type (smt-function->name tp.recognizer) type))
       (constructor (translate-variable (smt-function->translation tp.constructor)))
       (translated-destructors (create-destructors tp.destructors type))
       (new-acc (construct-product type acc)))
    (mv `((,name " = Datatype( '" ,name "' )" #\Newline)
          (,name ".declare( '" ,constructor
                 "'" ,translated-destructors " )" #\Newline))
        new-acc)))

(define create-type ((type smt-type-p)
                     (acc pseudo-term-list-listp))
  :returns (mv (translated paragraph-p)
               (properties pseudo-term-list-listp))
  (b* ((type (smt-type-fix type))
       (acc (pseudo-term-list-list-fix acc))
       ((smt-type tp) type))
    (case tp.kind
      (:prod (create-product-type type acc))
      (t (mv nil acc)))))

(local (in-theory (enable paragraph-p word-p)))

(define create-datatypes ((types symbol-smt-type-alist-p))
  :returns (created-names paragraph-p)
  :measure (len (symbol-smt-type-alist-fix types))
  (b* ((types (symbol-smt-type-alist-fix types))
       ((unless (consp types)) nil)
       ((cons t-hd t-tl) types)
       ((cons & tp) t-hd)
       (translated-name
        (translate-variable
         (smt-function->translation (smt-type->recognizer tp))))
       (names-tl (create-datatypes t-tl)))
    (cons `(,translated-name ", ") names-tl)))

(define create-type-list ((types symbol-smt-type-alist-p)
                          (acc pseudo-term-list-listp))
  :returns (mv (translated paragraph-p)
               (properties pseudo-term-list-listp))
  :measure (len (symbol-smt-type-alist-fix types))
  (b* ((types (symbol-smt-type-alist-fix types))
       (acc (pseudo-term-list-list-fix acc))
       ((unless (consp types)) (mv nil acc))
       ((cons t-hd t-tl) types)
       ((cons & tp) t-hd)
       ((mv trans acc-1) (create-type tp acc))
       ((if (null trans)) (create-type-list t-tl acc))
       ((mv translated-tl properties-tl) (create-type-list t-tl acc-1)))
    (mv (cons trans translated-tl) properties-tl)))

(define create-type-list-top ((types symbol-smt-type-alist-p))
  :returns (mv (translated paragraph-p)
               (properties pseudo-term-list-listp))
  (b* ((types (symbol-smt-type-alist-fix types))
       ((if (null types)) (mv nil nil))
       (names (create-datatypes types))
       (create-datatypes `((,names " = " "CreateDatatypes( " ,names " )" #\Newline)))
       ((mv translated properties) (create-type-list types nil)))
    (mv `(,translated ,create-datatypes) properties)))
