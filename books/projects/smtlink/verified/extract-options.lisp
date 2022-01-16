;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (April 19th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "hint-interface")
(include-book "judgements")

(defprod extract-options
  ((acl2type symbol-symbol-alistp)
   (datatype symbol-symbol-alistp)
   (alltype symbol-symbol-alistp)))

(define construct-extract-acl2types ((acl2types smt-acl2type-list-p))
  :returns (acl2type-alst symbol-symbol-alistp)
  :measure (len acl2types)
  (b* ((acl2types (smt-acl2type-list-fix acl2types))
       ((unless (consp acl2types)) nil)
       ((cons hd tl) acl2types)
       ((smt-acl2type at) hd))
    (acons at.recognizer nil (construct-extract-acl2types tl))))

(define construct-extract-datatypes ((datatypes smt-datatype-list-p))
  :returns (datatype-alst symbol-symbol-alistp)
  :measure (len datatypes)
  (b* ((datatypes (smt-datatype-list-fix datatypes))
       ((unless (consp datatypes)) nil)
       ((cons hd tl) datatypes))
    (acons (smt-function->name (smt-datatype->recognizer hd)) nil
           (construct-extract-datatypes tl))))

(local
(defthm crock
  (implies (and (symbol-symbol-alistp x) (symbol-symbol-alistp y))
           (symbol-symbol-alistp (append x y))))
)

(define construct-extract-options ((hints smtlink-hint-p))
  :returns (op extract-options-p)
  (b* ((hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       (acl2types (construct-extract-acl2types h.acl2types))
       (datatypes (construct-extract-datatypes h.datatypes)))
    (make-extract-options :acl2type acl2types
                          :datatype datatypes
                          :alltype (append acl2types datatypes))))
