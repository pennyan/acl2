;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (12th Oct 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "hint-interface")
(include-book "basic-theorems")

(define make-basic-types ()
  :returns (type-lst smt-type-list-p)
  (list (make-smt-type :recognizer (make-smt-function :name 'symbolp
                                                      :formals '(x)
                                                      :returns
                                                      '(return-of-symbolp))
                       :fixer (make-smt-function :name 'symbol-fix
                                                 :formals '(x)
                                                 :returns '(return-of-symbol-fix)
                                                 :replace-thms '(replace-of-symbol-fix)))
        (make-smt-type :recognizer (make-smt-function :name 'booleanp
                                                      :formals '(x)
                                                      :returns
                                                      '(return-of-booleanp))
                       :fixer (make-smt-function :name 'bool-fix
                                                 :formals '(x)
                                                 :returns '(return-of-bool-fix)
                                                 :replace-thms '(replace-of-bool-fix)))
        (make-smt-type :recognizer (make-smt-function :name 'integerp
                                                      :formals '(x)
                                                      :returns
                                                      '(return-of-integerp))
                       :fixer (make-smt-function :name 'ifix
                                                 :formals '(x)
                                                 :returns '(return-of-ifix)
                                                 :replace-thms '(replace-of-ifix))
                       :supertypes (list (make-smt-sub/supertype
                                          :type 'rationalp
                                          :formals '(x)
                                          :thm 'integerp-is-rationalp)))
        (make-smt-type :recognizer (make-smt-function :name 'rationalp
                                                      :formals '(x)
                                                      :returns
                                                      '(return-of-rationalp))
                       :fixer (make-smt-function :name 'rfix
                                                 :formals '(x)
                                                 :returns '(return-of-rfix)
                                                 :replace-thms '(replace-of-rfix)))))

(define make-basic-functions ()
  :returns (fun-lst smt-function-list-p)
  (list (make-smt-function :name 'not
                           :formals '(x)
                           :returns '(return-of-not))
        (make-smt-function :name 'equal
                           :formals '(x y)
                           :returns '(return-of-equal))
        (make-smt-function :name '<
                           :formals '(x y)
                           :returns '(return-of-<-rationalp
                                      return-of-<-integerp
                                      return-of-<-rationalp-integerp
                                      return-of-<-integerp-rationalp))
        (make-smt-function :name 'unary--
                           :formals '(x)
                           :returns '(return-of-unary---integerp
                                      return-of-unary---rationalp))
        (make-smt-function :name 'unary-/
                           :formals '(x)
                           :returns '(return-of-unary-/-integerp
                                      return-of-unary-/-rationalp))
        (make-smt-function :name 'binary-+
                           :formals '(x y)
                           :returns '(return-of-binary-+-rationalp
                                      return-of-binary-+-integerp
                                      return-of-binary-+-rationalp-integerp
                                      return-of-binary-+-integerp-rationalp))
        (make-smt-function :name 'binary-*
                           :formals '(x y)
                           :returns '(return-of-binary-*-rationalp
                                      return-of-binary-*-integerp
                                      return-of-binary-*-rationalp-integerp
                                      return-of-binary-*-integerp-rationalp))
        ))

(define make-basic-hints ()
  :returns (hint smtlink-hint-p)
  (make-smtlink-hint
   :types (make-basic-types)
   :functions (make-basic-functions)
   :configurations (make-smt-config :smt-cnf (default-smt-cnf))))
