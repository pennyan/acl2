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

(include-book "../utils/basics")
(include-book "replace-options")
(include-book "judgement-fns")
(include-book "match-term")
(include-book "flatten-judge")
(include-book "construct-judge")

(local (in-theory (e/d ()
                       ((:executable-counterpart typed-term)
                        pseudo-termp pseudo-term-listp))))

(define make-subst ((pair-lst pseudo-term-typed-term-alist-p))
  :returns (mv (term-lst pseudo-term-listp) (term-pair pseudo-term-alistp))
  :measure (len (pseudo-term-typed-term-alist-fix pair-lst))
  (b* ((pair-lst (pseudo-term-typed-term-alist-fix pair-lst))
       ((unless (consp pair-lst)) (mv nil nil))
       ((cons pair-hd pair-tl) pair-lst)
       ((cons tm tt) pair-hd)
       ((typed-term tt) tt)
       ((mv term-tl pair-tl) (make-subst pair-tl)))
    (mv (cons tt.term term-tl)
        (acons tm tt.term pair-tl))))

(define find-judge-term ((judge pseudo-termp)
                         (supertype type-to-types-alist-p))
  :returns (mv (found booleanp) (term pseudo-termp))
  :measure (acl2-count (pseudo-term-fix judge))
  :verify-guards nil
  (b* ((judge (pseudo-term-fix judge))
       ((if (equal judge ''t)) (mv nil ''t))
       ((if (type-predicate-p judge supertype)) (mv t (cadr judge)))
       ((unless (is-conjunct? judge)) (mv nil ''t))
       ((list* & judge-hd judge-tl &) judge)
       ((mv found-hd term-hd) (find-judge-term judge-hd supertype))
       ((if found-hd) (mv found-hd term-hd)))
    (find-judge-term judge-tl supertype)))

(verify-guards find-judge-term
  :hints (("Goal" :in-theory (enable pseudo-termp))))

(define make-judge-alst ((judge-lst pseudo-term-listp)
                         (acc pseudo-term-alistp)
                         (supertype type-to-types-alist-p))
  :returns (judge-alst pseudo-term-alistp)
  :measure (len judge-lst)
  (b* ((judge-lst (pseudo-term-list-fix judge-lst))
       (supertype (type-to-types-alist-fix supertype))
       (acc (pseudo-term-alist-fix acc))
       ((unless (consp judge-lst)) acc)
       ((cons judge-hd judge-tl) judge-lst)
       ((mv found term) (find-judge-term judge-hd supertype))
       ((unless found)
        (er hard? 'term-replacement=>make-judge-alst
            "Cannot find term from judge: ~q0" judge-hd))
       (exists? (assoc-equal term acc))
       ((unless exists?)
        (make-judge-alst judge-tl (acons term judge-hd acc) supertype))
       (new-judge `(if ,judge-hd ,(cdr exists?) 'nil)))
    (make-judge-alst judge-tl (acons term new-judge acc) supertype)))

(skip-proofs
 (define match-and-replace ((tterm good-typed-term-p)
                            (supertype type-to-types-alist-p)
                            (rep thm-spec-p))
  :returns (new-tt good-typed-term-p)
  :verify-guards nil
  (b* (((unless (mbt (and (good-typed-term-p tterm)
                          (type-to-types-alist-p supertype)
                          (thm-spec-p rep))))
        (make-typed-term))
       ((thm-spec ts) rep)
       ((typed-term tt) tterm)
       ((typed-term tt-top) (typed-term->top tt))
       (tt-pair (match-term tterm ts.lhs nil))
       ((if (equal tt-pair :fail)) tterm)
       ((mv term-lst subst) (make-subst tt-pair))
       (substed-hypo (acl2::substitute-into-term ts.hypotheses subst))
       (substed-term (acl2::substitute-into-term ts.rhs subst))
       (substed-judge (acl2::substitute-into-list ts.judgements subst))
       (new-judge (make-judge-alst substed-judge nil supertype))
       (judgements (if (equal (typed-term->kind tterm) 'fncallp)
                       `(if ,(typed-term->judgements (typed-term->top tt))
                            ,(typed-term-list->judgements
                              (typed-term-fncall->actuals tt))
                          'nil)
                     tt.judgements))
       (ok (path-test-list `(if ,judgements ,tt.path-cond 'nil) substed-hypo))
       ((unless ok) tterm)
       (type-alst (flatten-judge-term tterm term-lst nil))
       (judge (construct-judge-term substed-term type-alst new-judge))
       (top-judge (generate-judge-from-equality substed-term tt-top.term
                                                tt-top.judgements
                                                supertype))
       ;; Remove top-judge from the judge
       ((mv okp arg-judge)
        (case-match judge
          (('if & arg-judge ''nil) (mv t arg-judge))
          (& (mv nil ''t))))
       ((unless okp)
        (prog2$ (er hard? 'term-replacement=>match-and-replace
                    "Judge is malformed: ~q0" judge)
                tt))
       ;; Add top-judge gotten from original term
       (total-judge `(if ,top-judge ,arg-judge 'nil)))
    (change-typed-term tterm :term substed-term :judgements total-judge)))
)

(skip-proofs
 (verify-guards match-and-replace)
 )

(define match-and-replace-list ((tterm good-typed-term-p)
                                (supertype type-to-types-alist-p)
                                (replaces thm-spec-list-p))
  :returns (new-tt good-typed-term-p)
  (b* (((unless (mbt (and (good-typed-term-p tterm)
                          (type-to-types-alist-p supertype)
                          (thm-spec-list-p replaces))))
        (make-typed-term))
       ((unless (consp replaces)) tterm)
       ((cons rep-hd rep-tl) replaces)
       (new-tt (match-and-replace tterm supertype rep-hd))
       ((unless (equal tterm new-tt)) new-tt))
    (match-and-replace-list tterm supertype rep-tl)))

(skip-proofs
(define replace-quote ((tterm good-typed-term-p)
                       (replace-options replace-options-p)
                       (path-cond pseudo-termp))
  :guard (equal (typed-term->kind tterm) 'quotep)
  :returns (new-tt good-typed-term-p)
  (b* (((unless (mbt (and (replace-options-p replace-options)
                          (equal (typed-term->kind tterm) 'quotep)
                          (good-typed-term-p tterm)
                          (pseudo-termp path-cond))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((replace-options ro) replace-options)
       (exists? (assoc-equal tt.term ro.replaces))
       ((unless exists?) (change-typed-term tt :path-cond path-cond))
       (tt1 (match-and-replace-list tt ro.supertype (cdr exists?))))
    (change-typed-term tt1 :path-cond path-cond))
  ///
  (defthm typed-term-of-replace-quote
    (typed-term-p (replace-quote tterm replace-options path-cond))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance
                    good-typed-term-implies-typed-term
                    (tterm
                     (replace-quote tterm replace-options path-cond))))))))
)

(skip-proofs
(defines replace-term
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil
  :returns-hints (("Goal"
                   :in-theory (e/d (good-typed-term-list-p)
                                   (pseudo-termp
                                    acl2-count
                                    lambda-of-pseudo-lambdap
                                    symbol-listp))))

  (define replace-if ((tterm good-typed-term-p)
                      (replace-options replace-options-p)
                      (path-cond pseudo-termp)
                      (clock natp)
                      state)
    :guard (equal (typed-term->kind tterm) 'ifp)
    :returns (new-tt good-typed-term-p)
    :measure (list (nfix clock) (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (replace-options-p replace-options)
                            (equal (typed-term->kind tterm) 'ifp)
                            (good-typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (natp clock))))
          (make-typed-term))
         ((replace-options ro) replace-options)
         ((typed-term tt) tterm)
         ((typed-term tt-cond) (typed-term-if->cond tt))
         ((typed-term tt-then) (typed-term-if->then tt))
         ((typed-term tt-else) (typed-term-if->else tt))
         ((typed-term tt-top) (typed-term->top tt))
         (new-cond (replace-term tt-cond ro path-cond clock state))
         ((typed-term new-ttc) new-cond)
         ((mv then-path-cond else-path-cond)
          (mv `(if ,(simple-transformer new-ttc.term) ,path-cond 'nil)
              `(if ,(simple-transformer `(not ,new-ttc.term)) ,path-cond
                 'nil)))
         (new-then (replace-term tt-then ro then-path-cond clock state))
         ((typed-term new-ttt) new-then)
         (new-else (replace-term tt-else ro else-path-cond clock state))
         ((typed-term new-tte) new-else)
         (new-term `(if ,new-ttc.term ,new-ttt.term ,new-tte.term))
         (new-top-judge (generate-judge-from-equality new-term tt-top.term
                                                      tt-top.judgements
                                                      ro.supertype))
         (new-top (change-typed-term tt-top
                                     :term new-term
                                     :path-cond path-cond
                                     :judgements new-top-judge)))
      (make-typed-if new-top new-cond new-then new-else)))

  (define replace-fncall ((tterm good-typed-term-p)
                          (replace-options replace-options-p)
                          (path-cond pseudo-termp)
                          (clock natp)
                          state)
    :guard (equal (typed-term->kind tterm) 'fncallp)
    :returns (new-tt good-typed-term-p)
    :measure (list (nfix clock) (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (replace-options-p replace-options)
                            (equal (typed-term->kind tterm) 'fncallp)
                            (good-typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (natp clock))))
          (make-typed-term))
         ((if (zp clock)) tterm)
         ((replace-options ro) replace-options)
         ((typed-term tt) tterm)
         ((cons fn &) tt.term)
         (exists? (assoc-equal fn ro.replaces))
         ((unless exists?)
          (b* ((tt-actuals (typed-term-fncall->actuals tt))
               ((typed-term tt-top) (typed-term->top tt))
               (tt1-actuals
                (replace-term-list tt-actuals ro path-cond clock state))
               (tt1a.term-lst (typed-term-list->term-lst tt1-actuals))
               (term1 `(,fn ,@tt1a.term-lst))
               (tt1-judge-top (generate-judge-from-equality term1 tt-top.term
                                                            tt-top.judgements
                                                            ro.supertype))
               (tt1-top (change-typed-term tt-top
                                           :term term1
                                           :path-cond path-cond
                                           :judgements tt1-judge-top))
               ((unless (make-typed-fncall-guard tt1-top tt1-actuals)) tt))
            (make-typed-fncall tt1-top tt1-actuals)))
         (tt1 (match-and-replace-list tt ro.supertype (cdr exists?)))
         ((if (equal tt1 tt))
          (b* ((tt-actuals (typed-term-fncall->actuals tt))
               ((typed-term tt-top) (typed-term->top tt))
               (tt1-actuals
                (replace-term-list tt-actuals ro path-cond clock state))
               (tt1a.term-lst (typed-term-list->term-lst tt1-actuals))
               (term1 `(,fn ,@tt1a.term-lst))
               (tt1-judge-top (generate-judge-from-equality term1 tt-top.term
                                                            tt-top.judgements
                                                            ro.supertype))
               (tt1-top (change-typed-term tt-top
                                           :term term1
                                           :path-cond path-cond
                                           :judgements tt1-judge-top))
               ((unless (make-typed-fncall-guard tt1-top tt1-actuals)) tt))
            (make-typed-fncall tt1-top tt1-actuals))))
      (replace-term (change-typed-term tt1 :path-cond path-cond)
                    ro path-cond (1- clock) state)))

  (define replace-term ((tterm good-typed-term-p)
                        (replace-options replace-options-p)
                        (path-cond pseudo-termp)
                        (clock natp)
                        state)
    :returns (new-tt good-typed-term-p)
    :measure (list (nfix clock) (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (good-typed-term-p tterm)
                            (replace-options-p replace-options)
                            (pseudo-termp path-cond)
                            (natp clock))))
          (make-typed-term))
         ((if (equal (typed-term->kind tterm) 'variablep))
          (change-typed-term tterm :path-cond path-cond))
         ((if (equal (typed-term->kind tterm) 'ifp))
          (replace-if tterm replace-options path-cond clock state))
         ((if (equal (typed-term->kind tterm) 'fncallp))
          (replace-fncall tterm replace-options path-cond clock state))
         ((if (equal (typed-term->kind tterm) 'quotep))
          (replace-quote tterm replace-options path-cond)))
      (prog2$ (er hard? 'term-replacement=>replace-term
                  "Found lambda term in goal.~%")
              tterm)))

  (define replace-term-list ((tterm-lst good-typed-term-list-p)
                             (replace-options replace-options-p)
                             (path-cond pseudo-termp)
                             (clock natp)
                             state)
    :returns (new-ttl good-typed-term-list-p)
    :measure (list (nfix clock) (acl2-count (typed-term-list->term-lst tterm-lst)) 1)
    (b* (((unless (mbt (and (good-typed-term-list-p tterm-lst)
                            (replace-options-p replace-options)
                            (pseudo-termp path-cond)
                            (natp clock))))
          nil)
         ((unless (consp tterm-lst)) nil)
         ((cons tterm-hd tterm-tl) tterm-lst)
         (tt-car (replace-term tterm-hd replace-options path-cond clock state))
         (tt-cdr (replace-term-list tterm-tl replace-options path-cond clock state))
         ((unless (implies (consp tt-cdr)
                           (equal (typed-term->path-cond tt-car)
                                  (typed-term-list->path-cond tt-cdr))))
          tterm-lst))
      (cons tt-car tt-cdr)))
  ///
  (defthm typed-term-of-replace-fncall
    (typed-term-p (replace-fncall tterm replace-options path-cond clock state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (replace-fncall tterm replace-options path-cond
                                               clock state)))))))
  (defthm typed-term-of-replace-if
    (typed-term-p (replace-if tterm replace-options path-cond clock state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (replace-if tterm replace-options path-cond
                                           clock state)))))))
  (defthm typed-term-of-replace-term
    (typed-term-p (replace-term tterm replace-options path-cond clock state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (replace-term tterm replace-options path-cond
                                             clock state)))))))
  (defthm typed-term-list-of-replace-term-list
    (typed-term-list-p
     (replace-term-list tterm-lst replace-options path-cond clock state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-list-implies-typed-term-list)
             :use ((:instance good-typed-term-list-implies-typed-term-list
                              (tterm-lst
                               (replace-term-list tterm-lst replace-options
                                                  path-cond clock state)))))))
  )
)

(skip-proofs
 (verify-guards replace-term)
 )

(define term-replacement-fn ((cl pseudo-term-listp)
                             (smtlink-hint t)
                             state)
  :returns (subgoal-lst pseudo-term-list-listp
                        :hints (("Goal" :in-theory (enable pseudo-termp))))
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint)) (list cl))
       (clock (smtlink-hint->wrld-fn-len smtlink-hint))
       (goal (disjoin cl))
       (h (construct-replace-options smtlink-hint state))
       ((mv okp tterm)
        (case-match goal
          (('implies judges term)
           (mv t (make-typed-term :term term
                                  :path-cond ''t
                                  :judgements judges)))
          (& (mv nil (make-typed-term)))))
       ((unless okp)
        (prog2$ (er hard? 'term-replacement=>term-replacement-fn
                    "The input term is of wrong shape. It should look like ~
                     (typed-goal ...) ~%")
                (list cl)))
       ((unless (good-typed-term-p tterm))
        (prog2$ (er hard? 'term-replacement=>term-replacement-fn
                    "Not a good-typed-term-p: ~q0" tterm)
                (list cl)))
       (replaced-tterm (replace-term tterm h ''t clock state))
       (replaced-judgements (typed-term->judgements replaced-tterm))
       (replaced-term (typed-term->term replaced-tterm))
       (new-cl `((implies ,replaced-judgements ,replaced-term)))
       (next-cp (cdr (assoc-equal 'term-replacement *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',smtlink-hint state)))
       (hinted-goal `((hint-please ',the-hint) ,@new-cl)))
    (list hinted-goal)))

(define term-replacement-cp ((cl pseudo-term-listp)
                             (hints t)
                             state)
  (b* ((new-clause (term-replacement-fn cl hints state)))
    (value new-clause)))

(skip-proofs
(defthm correctness-of-term-replacement-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (term-replacement-cp cl hint state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :rule-classes :clause-processor)
)
