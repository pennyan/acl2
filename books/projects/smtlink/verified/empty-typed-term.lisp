;; Copyright (C) 2015, University of British Columbia
;; Originally written by Yan Peng (June 17th 2022)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "typed-term")
(include-book "typed-term-fns")

(defines make-empty-judgements-from-term
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil
  :hints (("Goal" :in-theory (e/d () ())))

  (define make-empty-judgements-from-if ((term pseudo-termp))
    :guard (and (consp term)
                (equal (car term) 'if))
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         ((unless (mbt (and (consp term) (equal (car term) 'if)))) ''t)
         ((cons & actuals) term)
         ((unless (equal (len actuals) 3))
          (prog2$ (er hard? 'empty-typed-term->make-empty-judgements-from-if
                      "Mangled if term: ~q0" term)
                  ''t))
         ((list cond then else) actuals)
         (judge-if-top ''t)
         (judge-cond (make-empty-judgements-from-term cond))
         (judge-then (make-empty-judgements-from-term then))
         (judge-else (make-empty-judgements-from-term else)))
      `(if ,judge-if-top
           (if ,judge-cond
               (if ,cond ,judge-then ,judge-else)
             'nil)
         'nil)))

  (define make-empty-judgements-from-fn ((term pseudo-termp))
    :guard (and (consp term)
                (symbolp (car term))
                (not (equal (car term) 'if))
                (not (equal (car term) 'quote)))
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         ((unless (mbt (and (consp term)
                            (symbolp (car term))
                            (not (equal (car term) 'quote))
                            (not (equal (car term) 'if)))))
          ''t)
         ((cons & actuals) term)
         (judge-fn-top ''t)
         (actuals-judgements (make-empty-judgements-from-term-list actuals)))
      `(if ,judge-fn-top
           ,actuals-judgements
         'nil)))

  (define make-empty-judgements-from-term ((term pseudo-termp))
    :measure (list (acl2-count (pseudo-term-fix term)) 1)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         ((if (acl2::variablep term)) ''t)
         ((if (acl2::quotep term)) ''t)
         ((cons fn &) term)
         ((if (pseudo-lambdap fn))
          (prog2$ (er hard? 'empty-typed-term=>make-empty-judgements-from-term
                      "Found lambda in the goal.~%")
                  ''t))
         ((if (equal fn 'if)) (make-empty-judgements-from-if term)))
      (make-empty-judgements-from-fn term)))
  
  (define make-empty-judgements-from-term-list ((term-lst pseudo-term-listp))
    :measure (list (acl2-count (pseudo-term-list-fix term-lst)) 1)
    :returns (judgements pseudo-termp)
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         ((unless (consp term-lst)) ''t)
         ((cons first rest) term-lst)
         (first-judge (make-empty-judgements-from-term first))
         (rest-judge (make-empty-judgements-from-term-list rest)))
      `(if ,first-judge
           ,rest-judge
         'nil)))
  )

(verify-guards make-empty-judgements-from-term)

(encapsulate ()
  (local (in-theory (e/d ()
                         (symbol-listp
                          consp-of-is-conjunct?
                          pseudo-term-listp-of-symbol-listp
                          acl2::symbol-listp-when-not-consp
                          correctness-of-path-test-list
                          pseudo-term-listp-of-cdr-of-pseudo-termp
                          acl2::true-listp-of-car-when-true-list-listp
                          true-list-listp true-listp
                          pseudo-lambdap-of-fn-call-of-pseudo-termp
                          member-equal
                          acl2::pseudo-termp-list-cdr))))

  (defthm-make-empty-judgements-from-term-flag
    (defthm correct-typed-term-of-make-empty-judgements-from-if
      (implies (and (pseudo-termp term) (alistp a))
               (ev-smtcp (make-empty-judgements-from-if term) a))
      :flag make-empty-judgements-from-if
      :hints ((and stable-under-simplificationp
                   '(:in-theory (e/d () ())
                     :expand (make-empty-judgements-from-if term)))))
    (defthm correct-typed-term-of-make-empty-judgements-from-fn
      (implies (and (pseudo-termp term) (alistp a))
               (ev-smtcp (make-empty-judgements-from-fn term) a))
      :flag make-empty-judgements-from-fn
      :hints ((and stable-under-simplificationp
                   '(:in-theory (e/d () ())
                     :expand (make-empty-judgements-from-fn term)))))
    (defthm correct-typed-term-of-make-empty-judgements-from-term
      (implies (and (pseudo-termp term) (alistp a))
               (ev-smtcp (make-empty-judgements-from-term term) a))
      :flag make-empty-judgements-from-term
      :hints ((and stable-under-simplificationp
                   '(:in-theory (e/d () ())
                     :expand (make-empty-judgements-from-term term)))))
    (defthm correct-typed-term-of-make-empty-judgements-from-term-list
      (implies (and (pseudo-term-listp term-lst) (alistp a))
               (ev-smtcp (make-empty-judgements-from-term-list term-lst) a))
      :flag make-empty-judgements-from-term-list
      :hints ((and stable-under-simplificationp
                   '(:in-theory (e/d () ())
                     :expand ((make-empty-judgements-from-term-list term-lst)
                              (make-empty-judgements-from-term-list nil)))))))
  )

(define make-empty-typed-term ((term pseudo-termp))
  (b* ((term (pseudo-term-fix term))
       (judgements (make-empty-judgements-from-term term)))
    (make-typed-term :term term
                     :path-cond ''t
                     :judgements judgements
                     :smt-judgements judgements)))

;; prove make-empty-typed-term is correct-typed-term
(defthm correct-typed-term-of-make-empty-typed-term
  (implies (and (pseudo-termp term) (alistp a))
           (ev-smtcp (correct-typed-term (make-empty-typed-term term)) a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable make-empty-typed-term
                              correct-typed-term))))
