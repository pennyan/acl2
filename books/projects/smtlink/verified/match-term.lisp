;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (April 14th 2021)
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

(include-book "basics")
(include-book "evaluator")
(include-book "hint-interface")
(include-book "typed-term-fns")

(local (in-theory (disable (:executable-counterpart typed-term)
                           pseudo-termp pseudo-term-listp)))

(defalist pseudo-term-typed-term-alist
  :key-type pseudo-termp
  :val-type typed-term-p
  :true-listp t)

(Encapsulate ()

(define pseudo-term-typed-term-alist-or-fail-p ((x))
  :returns (okp booleanp)
  (or (pseudo-term-typed-term-alist-p x)
      (equal x :fail)))

(easy-fix pseudo-term-typed-term-alist-or-fail :fail)

(local
 (in-theory (enable pseudo-term-typed-term-alist-or-fail-p)))

(defthm either-of-pseudo-term-typed-term-alist
  (pseudo-term-typed-term-alist-or-fail-p
   (pseudo-term-typed-term-alist-fix x)))

(defthm either-of-cons-pseudo-term-typed-term-alist
  (implies (and (pseudo-termp pat)
                (typed-term-p tterm))
           (pseudo-term-typed-term-alist-or-fail-p
            (cons (cons pat tterm)
                  (pseudo-term-typed-term-alist-fix acc)))))

(defthm pseudo-term-typed-term-alist-of-either
  (implies (and (pseudo-term-typed-term-alist-or-fail-p x)
                (not (equal x :fail)))
           (pseudo-term-typed-term-alist-p x)))
)

(define match-variable ((tterm good-typed-term-p)
                        (pat pseudo-termp)
                        (acc pseudo-term-typed-term-alist-p))
  :guard (acl2::variablep pat)
  :returns (new-acc pseudo-term-typed-term-alist-or-fail-p)
  (b* ((tterm (typed-term-fix tterm))
       (pat (pseudo-term-fix pat))
       (acc (pseudo-term-typed-term-alist-fix acc))
       ((unless (mbt (and (good-typed-term-p tterm)
                          (acl2::variablep pat))))
        acc)
       (exists? (assoc-equal pat acc))
       ((if (and exists? (equal (cdr exists?) tterm))) acc)
       ((if exists?) :fail))
    (acons pat tterm acc)))

(define match-quote ((tterm good-typed-term-p)
                     (pat pseudo-termp)
                     (acc pseudo-term-typed-term-alist-p))
  :guard (acl2::quotep pat)
  :returns (new-acc pseudo-term-typed-term-alist-or-fail-p)
  (b* ((tterm (typed-term-fix tterm))
       (pat (pseudo-term-fix pat))
       (acc (pseudo-term-typed-term-alist-fix acc))
       ((unless (mbt (and (good-typed-term-p tterm)
                          (acl2::quotep pat))))
        acc)
       ((typed-term tt) tterm)
       ((if (equal tt.term pat)) acc))
    :fail))

(defines match-term
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil

  (define match-fncall ((tterm good-typed-term-p)
                        (pat pseudo-termp)
                        (acc pseudo-term-typed-term-alist-p))
    :guard (and (good-typed-term-p tterm)
                (consp pat) (not (acl2::quotep pat))
                (not (equal (car pat) 'if)))
    :measure (list (acl2-count (pseudo-term-fix pat)) 0)
    :returns (new-acc pseudo-term-typed-term-alist-or-fail-p)
    (b* ((tterm (typed-term-fix tterm))
         (pat (pseudo-term-fix pat))
         (acc (pseudo-term-typed-term-alist-fix acc))
         ((unless (mbt (and (good-typed-term-p tterm)
                            (consp pat) (not (acl2::quotep pat))
                            (not (equal (car pat) 'if)))))
          acc)
         ((unless (and (equal (typed-term->kind tterm) 'fncallp)
                       (good-typed-fncall-p tterm)))
          :fail)
         ((typed-term tt) tterm)
         (tt-actuals (typed-term-fncall->actuals tt))
         ((cons fn actuals) pat)
         ((unless (and (consp tt.term) (equal fn (car tt.term)))) :fail))
      (match-term-list tt-actuals actuals acc)))

  (define match-term ((tterm good-typed-term-p)
                      (pat pseudo-termp)
                      (acc pseudo-term-typed-term-alist-p))
    :guard (good-typed-term-p tterm)
    :measure (list (acl2-count (pseudo-term-fix pat)) 1)
    :returns (new-acc pseudo-term-typed-term-alist-or-fail-p)
    (b* ((tterm (typed-term-fix tterm))
         (pat (pseudo-term-fix pat))
         (acc (pseudo-term-typed-term-alist-fix acc))
         ((unless (mbt (good-typed-term-p tterm))) acc)
         ((if (acl2::variablep pat)) (match-variable tterm pat acc))
         ((if (acl2::quotep pat)) (match-quote tterm pat acc))
         ((cons fn &) pat)
         ((if (equal fn 'if))
          (prog2$ (er hard? 'pattern-match=>match-term
                      "Found if function in the pattern.~%")
                  :fail))
         ((if (symbolp fn)) (match-fncall tterm pat acc)))
      (prog2$ (er hard? 'pattern-match=>match-term
                  "Found lambda term in the pattern.~%")
              :fail)))

  (define match-term-list ((tterm-lst typed-term-list-p)
                           (pat-lst pseudo-term-listp)
                           (acc pseudo-term-typed-term-alist-p))
    :guard (good-typed-term-list-p tterm-lst)
    :measure (list (acl2-count (pseudo-term-list-fix pat-lst)) 1)
    :returns (new-acc pseudo-term-typed-term-alist-or-fail-p)
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         (pat-lst (pseudo-term-list-fix pat-lst))
         (acc (pseudo-term-typed-term-alist-fix acc))
         ((unless (mbt (good-typed-term-list-p tterm-lst))) acc)
         ((unless (and (consp tterm-lst) (consp pat-lst))) acc)
         ((cons tterm-hd tterm-tl) tterm-lst)
         ((cons pat-hd pat-tl) pat-lst)
         (acc-hd (match-term tterm-hd pat-hd acc))
         ((if (equal acc-hd :fail)) acc-hd))
      (match-term-list tterm-tl pat-tl acc-hd)))
  )

(verify-guards match-term
  :hints (("Goal" :in-theory (enable good-typed-fncall-p typed-term->kind))))

#|
(match-term '((term ifix x)
              (path-cond if (rationalp y)
                         (if (integerp x) 't 'nil)
                         'nil)
              (judgements if (if (rationalp (ifix x)) 't 'nil)
                          (if (if (integerp x) 't 'nil) 't 'nil)
                          'nil))
            '(ifix x)
            nil)
|#
