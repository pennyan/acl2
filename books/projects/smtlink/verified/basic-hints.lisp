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
  (list (make-smt-type :recognizer (make-smt-function
                                    :name 'symbolp
                                    :returns
                                    (list (make-thm-spec
                                           :formals '(x)
                                           :thm 'return-of-symbolp)))
                       :fixer (make-smt-function
                               :name 'symbol-fix
                               :returns
                               (list (make-thm-spec
                                      :formals '(x)
                                      :thm 'return-of-symbol-fix))))
        (make-smt-type :recognizer (make-smt-function
                                    :name 'booleanp
                                    :returns
                                    (list (make-thm-spec
                                           :formals '(x)
                                           :thm 'return-of-booleanp)))
                       :fixer (make-smt-function
                               :name 'bool-fix
                               :returns
                               (list (make-thm-spec
                                      :formals '(x)
                                      :thm 'return-of-bool-fix))))
        (make-smt-type :recognizer (make-smt-function
                                    :name 'integerp
                                    :returns
                                    (list (make-thm-spec
                                           :formals '(x)
                                           :thm 'return-of-integerp)))
                       :fixer (make-smt-function
                               :name 'ifix
                               :returns
                               (list (make-thm-spec
                                      :formals '(x)
                                      :thm 'return-of-ifix)))
                       :supertypes (list (make-smt-sub/supertype
                                          :type 'rationalp
                                          :thm (make-thm-spec
                                                :formals '(x)
                                                :thm 'integerp-is-rationalp))))
        (make-smt-type :recognizer (make-smt-function
                                    :name 'rationalp
                                    :returns
                                    (list (make-thm-spec
                                           :formals '(x)
                                           :thm 'return-of-rationalp)))
                       :fixer (make-smt-function
                               :name 'rfix
                               :returns
                               (list (make-thm-spec
                                      :formals '(x)
                                      :thm 'return-of-rfix))))))

(define make-basic-functions ()
  :returns (fun-lst smt-function-list-p)
  (list (make-smt-function :name 'not
                           :returns (list (make-thm-spec
                                           :formals '(x)
                                           :thm 'return-of-not)))
        (make-smt-function :name 'equal
                           :returns (list (make-thm-spec
                                           :formals '(x y)
                                           :thm 'return-of-equal-booleanp)
                                          (make-thm-spec
                                           :formals '(x y)
                                           :thm 'return-of-equal-integerp)
                                          (make-thm-spec
                                           :formals '(x y)
                                           :thm 'return-of-equal-rationalp)
                                          (make-thm-spec
                                           :formals '(x y)
                                           :thm 'return-of-equal-symbolp)))
        (make-smt-function :name '<
                           :returns (list (make-thm-spec
                                           :formals '(x y)
                                           :thm 'return-of-<-integerp)
                                          (make-thm-spec
                                           :formals '(x y)
                                           :thm 'return-of-<-rationalp-integerp)
                                          (make-thm-spec
                                           :formals '(x y)
                                           :thm
                                           'return-of-<-integerp-rationalp)
                                          (make-thm-spec
                                           :formals '(x y)
                                           :thm 'return-of-<-rationalp)))
        (make-smt-function :name 'unary--
                           :returns (list (make-thm-spec
                                           :formals '(x)
                                           :thm 'return-of-unary---integerp)
                                          (make-thm-spec
                                           :formals '(x)
                                           :thm 'return-of-unary---rationalp)))
        (make-smt-function :name 'unary-/
                           :returns (list (make-thm-spec
                                           :formals '(x)
                                           :thm 'return-of-unary-/-integerp)
                                          (make-thm-spec
                                           :formals '(x)
                                           :thm
                                           'return-of-unary-/-rationalp)))
        (make-smt-function :name 'binary-+
                           :returns (list (make-thm-spec
                                           :formals '(x y)
                                           :thm 'return-of-binary-+-integerp)
                                          (make-thm-spec
                                           :formals '(x y)
                                           :thm 'return-of-binary-+-rationalp-integerp)
                                          (make-thm-spec
                                           :formals '(x y)
                                           :thm
                                           'return-of-binary-+-integerp-rationalp)
                                          (make-thm-spec
                                           :formals '(x y)
                                           :thm 'return-of-binary-+-rationalp)))
        (make-smt-function :name 'binary-*
                           :returns (list (make-thm-spec
                                           :formals '(x y)
                                           :thm 'return-of-binary-*-integerp)
                                          (make-thm-spec
                                           :formals '(x y)
                                           :thm 'return-of-binary-*-rationalp-integerp)
                                          (make-thm-spec
                                           :formals '(x y)
                                           :thm
                                           'return-of-binary-*-integerp-rationalp)
                                          (make-thm-spec
                                           :formals '(x y)
                                           :thm 'return-of-binary-*-rationalp)))))

(define make-basic-replaces ()
  :returns (replace-lst smt-replace-list-p)
  (list (make-smt-replace :fn 'symbol-fix
                          :thms (list (make-thm-spec
                                       :thm 'replace-of-symbol-fix)))
        (make-smt-replace :fn 'bool-fix
                          :thms (list (make-thm-spec
                                       :thm 'replace-of-bool-fix)))
        (make-smt-replace :fn 'ifix
                          :thms (list (make-thm-spec
                                       :thm 'replace-of-ifix)))
        (make-smt-replace :fn 'rfix
                          :thms (list (make-thm-spec
                                       :thm 'replace-of-rfix)))))

(define make-basic-hints ()
  :returns (hint smtlink-hint-p)
  (make-smtlink-hint
   :types (make-basic-types)
   :functions (make-basic-functions)
   :replaces (make-basic-replaces)
   :configurations (make-smt-config :smt-cnf (default-smt-cnf))))
