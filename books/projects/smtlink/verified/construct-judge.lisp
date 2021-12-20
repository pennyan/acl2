;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (Jan 2nd 2022)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "hint-interface")

(define construct-judge-common ((term pseudo-termp)
                                (user-alst pseudo-term-alistp))
  :returns (judge pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (user-alst (pseudo-term-alist-fix user-alst))
       (exists? (assoc-equal term user-alst))
       ((unless exists?) ''t))
    (cdr exists?)))

(local
(defthm crock
 (implies (and (consp (pseudo-term-fix term))
               (symbolp (car (pseudo-term-fix term))))
          (< (acl2-count (pseudo-term-list-fix (cdr (pseudo-term-fix term))))
             (+ 1
                (acl2-count (cdr (pseudo-term-fix term))))))
 :hints (("Goal"
          :in-theory (enable pseudo-term-fix pseudo-term-list-fix))))
)

(defines construct-judge
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil

  (define construct-judge-fncall ((term pseudo-termp)
                                  (type-alst pseudo-term-alistp)
                                  (user-alst pseudo-term-alistp))
    :guard (and (consp term)
                (symbolp (car term))
                (not (equal (car term) 'if))
                (not (equal (car term) 'quote)))
    :returns (judge pseudo-termp)
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    (b* ((term (pseudo-term-fix term))
         (type-alst (pseudo-term-alist-fix type-alst))
         (user-alst (pseudo-term-alist-fix user-alst))
         ((unless (mbt (and (consp term)
                            (symbolp (car term))
                            (not (equal (car term) 'if))
                            (not (equal (car term) 'quote)))))
          ''t)
         ((cons & actuals) term)
         (actuals-judge (construct-judge-term-list actuals type-alst user-alst))
         (return-judge (construct-judge-common term user-alst)))
      `(if ,return-judge
           ,actuals-judge
         'nil)))

  (define construct-judge-term ((term pseudo-termp)
                                (type-alst pseudo-term-alistp)
                                (user-alst pseudo-term-alistp))
    :returns (judge pseudo-termp)
    :measure (list (acl2-count (pseudo-term-fix term)) 1)
    (b* ((term (pseudo-term-fix term))
         (type-alst (pseudo-term-alist-fix type-alst))
         (user-alst (pseudo-term-alist-fix user-alst))
         (exists? (assoc-equal term type-alst))
         ((if exists?) (cdr exists?))
         ((if (or (acl2::variablep term) (acl2::quotep term)))
          (construct-judge-common term user-alst))
         ((cons fn &) term)
         ((unless (or (equal fn 'if) (pseudo-lambdap fn)))
          (construct-judge-fncall term type-alst user-alst)))
      (prog2$ (er hard? 'construct-judge=>construct-judge-term
                  "Found lambda or if in the goal.~%")
              ''t)))

  (define construct-judge-term-list ((term-lst pseudo-term-listp)
                                     (type-alst pseudo-term-alistp)
                                     (user-alst pseudo-term-alistp))
    :returns (judge pseudo-termp)
    :measure (list (acl2-count (pseudo-term-list-fix term-lst)) 1)
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (type-alst (pseudo-term-alist-fix type-alst))
         (user-alst (pseudo-term-alist-fix user-alst))
         ((unless (consp term-lst)) ''t)
         ((cons term-hd term-tl) term-lst)
         (first-judge (construct-judge-term term-hd type-alst user-alst))
         (rest-judge (construct-judge-term-list term-tl type-alst user-alst)))
      `(if ,first-judge
           ,rest-judge
         'nil)))
  )

(verify-guards construct-judge-term)
