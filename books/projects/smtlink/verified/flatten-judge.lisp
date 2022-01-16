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

(include-book "typed-term-fns")

(local (in-theory (disable pseudo-termp pseudo-term-listp)))

(defines flatten-judge
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil
  :hints (("Goal"
           :in-theory (e/d ()
                           (acl2-count implies-of-fncall-kind))))

  (define flatten-judge-fncall ((tterm typed-term-p)
                                (term-lst pseudo-term-listp)
                                (acc pseudo-term-alistp))
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'fncallp))
    :returns (new-acc pseudo-term-alistp)
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (good-typed-term-p tterm)
                            (pseudo-term-listp term-lst)
                            (pseudo-term-alistp acc)
                            (equal (typed-term->kind tterm) 'fncallp))))
          nil)
         ((typed-term tt) tterm)
         (tt-actuals (typed-term-fncall->actuals tt))
         ((typed-term tt-top) (typed-term->top tt)))
      (flatten-judge-term-list tt-actuals term-lst acc)))

  (define flatten-judge-term ((tterm typed-term-p)
                              (term-lst pseudo-term-listp)
                              (acc pseudo-term-alistp))
    :guard (good-typed-term-p tterm)
    :returns (new-acc pseudo-term-alistp)
    :measure (list (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (good-typed-term-p tterm)
                            (pseudo-term-alistp acc))))
          nil)
         ((typed-term tt) tterm)
         (exists? (member-equal tt.term term-lst))
         ((if exists?) (acons tt.term tt.judgements acc))
         ((if (or (equal (typed-term->kind tterm) 'quotep)
                  (equal (typed-term->kind tterm) 'variablep)))
          (er hard? 'flatten-judge=>flatten-judge-term
              "Found quotep or variablep term that is not binded ~p0~%"
              tt.term))
         ((if (equal (typed-term->kind tterm) 'fncallp))
          (flatten-judge-fncall tterm term-lst acc)))
      (er hard? 'flatten-judge=>flatten-judge-term
          "Found lambda or if term in goal.~%")))

  (define flatten-judge-term-list ((tterm-lst typed-term-list-p)
                                   (term-lst pseudo-term-listp)
                                   (acc pseudo-term-alistp))
    :guard (good-typed-term-list-p tterm-lst)
    :returns (new-acc pseudo-term-alistp)
    :measure (list (acl2-count (typed-term-list->term-lst tterm-lst))
                   1)
    (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                            (good-typed-term-list-p tterm-lst)
                            (pseudo-term-listp term-lst)
                            (pseudo-term-alistp acc))))
          nil)
         ((unless (consp tterm-lst)) acc)
         ((cons tterm-hd tterm-tl) tterm-lst)
         (acc1 (flatten-judge-term tterm-hd term-lst acc)))
      (flatten-judge-term-list tterm-tl term-lst acc1)))
  )

(verify-guards flatten-judge-term)

(define flatten-judge ((tterm typed-term-p)
                       (term-lst pseudo-term-listp))
  :guard (good-typed-term-p tterm)
  :returns (type-alst pseudo-term-alistp)
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (good-typed-term-p tterm)
                          (pseudo-term-listp term-lst))))
        nil)
       ((typed-term tt) tterm)
       ((if (acl2::quotep tt.term)) nil))
    (flatten-judge-term tterm term-lst nil)))
