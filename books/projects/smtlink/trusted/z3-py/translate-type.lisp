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
(include-book "translate-variable")

(local (in-theory (enable paragraph-p word-p string-or-symbol-p)))

(define translate-type ((type smt-datatype-p))
  :returns (translated stringp)
  (b* ((type (smt-datatype-fix type))
       (dt.recognizer (smt-datatype->recognizer type))
       ((if (equal (smt-function->kind dt.recognizer) :basic))
        (trans-hint->translation
         (smt-function->translation-hint dt.recognizer))))
    (translate-variable
     (trans-hint->translation
      (smt-function->translation-hint dt.recognizer))))
  ///
  (more-returns
   (translated (paragraph-p translated)
               :name paragraph-of-translate-type)))
