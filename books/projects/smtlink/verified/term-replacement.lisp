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
(include-book "generalize-term")
(include-book "expand-cp")

(local (in-theory (e/d ()
                       ((:executable-counterpart typed-term)
                        pseudo-termp pseudo-term-listp))))

(defprod var-pair
  ((var-hyp pseudo-termp)
   (hyp-judge pseudo-termp)))

(defalist sym-var-pair-alist
  :key-type symbolp
  :val-type var-pair-p
  :pred sym-var-pair-alistp
  :true-listp t)

(defprod var-acc
  ((var-alst pseudo-term-sym-alistp)
   (hyp-alst sym-var-pair-alistp)
   (avoid symbol-listp)))

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

(define get-subst ((tterm good-typed-term-p)
                   (to-match pseudo-termp))
  :returns (mv (okp booleanp)
               (term-lst pseudo-term-listp)
               (subst pseudo-term-alistp))
  (b* (((unless (good-typed-term-p tterm))
        (mv nil nil nil))
       (to-match (pseudo-term-fix to-match))
       (tt-pair (match-term tterm to-match nil))
       ((if (equal tt-pair :fail)) (mv nil nil nil))
       ((mv term-lst subst) (make-subst tt-pair)))
    (mv t term-lst subst)))

(local
 (defthm symbol-pseudo-term-alist-is-pseudo-term-subst
   (implies (symbol-pseudo-term-alistp x) (acl2::pseudo-term-substp x))
   :hints (("Goal" :in-theory (enable acl2::pseudo-term-substp))))
 )

(define substitute-into-thm-spec ((rep thm-spec-p)
                                  (subst symbol-pseudo-term-alistp))
  :returns (substed thm-spec-p)
  :guard-hints (("Goal"
                 :in-theory (enable pseudo-termp pseudo-term-listp)))
  (b* ((rep (thm-spec-fix rep))
       (subst (symbol-pseudo-term-alist-fix subst))
       ((thm-spec r) rep)
       (new-hypo (acl2::substitute-into-term r.hypotheses subst))
       (new-lhs (acl2::substitute-into-term r.lhs subst))
       (new-rhs (acl2::substitute-into-term r.rhs subst))
       (new-judgements (acl2::substitute-into-list r.judgements subst))
       (new-var-term (acl2::substitute-into-term r.var-term subst))
       (new-var-hyp (acl2::substitute-into-term r.var-hyp subst))
       (new-hyp-judge (acl2::substitute-into-term r.hyp-judge subst)))
    (make-thm-spec :hypotheses new-hypo
                   :lhs new-lhs
                   :rhs new-rhs
                   :judgements new-judgements
                   :var-term new-var-term
                   :var-hyp new-var-hyp
                   :hyp-judge new-hyp-judge)))

(define generalize-thm-spec ((rep thm-spec-p)
                             (var symbolp))
  :returns (new-ts thm-spec-p)
  (b* ((rep (thm-spec-fix rep))
       (var (symbol-fix var))
       ((thm-spec ts) rep)
       (new-rhs (generalize-term ts.rhs ts.var-term var))
       (new-judgements (generalize-term-list ts.judgements ts.var-term var))
       (new-var-hyp (generalize-term ts.var-hyp ts.var-term var))
       (new-hyp-judge (generalize-term ts.hyp-judge ts.var-term var)))
    (change-thm-spec rep
                     :rhs new-rhs
                     :judgements new-judgements
                     :var-hyp new-var-hyp
                     :hyp-judge new-hyp-judge)))

(define reconstruct-judge ((tterm good-typed-term-p)
                           (term-lst pseudo-term-listp)
                           (rep thm-spec-p)
                           (var symbolp)
                           (supertype type-to-types-alist-p))
  :returns (total-judge pseudo-termp)
  :guard (or (equal (typed-term->kind tterm) 'ifp)
             (equal (typed-term->kind tterm) 'variablep)
             (equal (typed-term->kind tterm) 'fncallp))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp)))
  (b* (((unless (mbt (and (good-typed-term-p tterm)
                          (or (equal (typed-term->kind tterm) 'ifp)
                              (equal (typed-term->kind tterm) 'variablep)
                              (equal (typed-term->kind tterm) 'fncallp))
                          (type-to-types-alist-p supertype)
                          (thm-spec-p rep)
                          (symbolp var)
                          (pseudo-term-listp term-lst))))
        ''t)
       ((thm-spec ts) rep)
       ((typed-term tt) tterm)
       (ts-judge-alst
        (make-judge-alst ts.judgements (acons var ts.var-hyp nil) supertype))
       (tt-judge-alst (flatten-judge tt term-lst))
       (judge (construct-judge-term ts.rhs tt-judge-alst ts-judge-alst))
       ((typed-term tt-top)
        (if (equal (typed-term->kind tt) 'variablep) tt (typed-term->top tt)))
       (top-judge (generate-judge-from-equality ts.rhs tt-top.term
                                                tt-top.judgements
                                                supertype))
       ((mv okp arg-judge)
        (case-match judge
          (('if & arg-judge ''nil) (mv t arg-judge))
          (& (mv nil ''t))))
       ((unless okp)
        (prog2$ (er hard? 'term-replacement=>reconstruct-judge
                    "Judge is malformed: ~q0" judge)
                ''t)))
    `(if ,top-judge ,arg-judge 'nil)))

(skip-proofs
(define get-var ((rep thm-spec-p)
                 (acc var-acc-p))
  :returns (mv (exists? booleanp)
               (new-var symbolp)
               (new-var-acc var-acc-p))
  (b* ((rep (thm-spec-fix rep))
       (acc (var-acc-fix acc))
       ((thm-spec ts) rep)
       ((var-acc a) acc)
       ((unless ts.var-term) (mv t nil a))
       (exists? (assoc-equal ts.var-term a.var-alst))
       ((if exists?) (mv t (cdr exists?) a))
       ((mv new-var new-var-alst new-avoid)
        (new-var-for-term ts.var-term a.var-alst a.avoid)))
    (mv nil new-var
        (change-var-acc a
                        :var-alst new-var-alst
                        :avoid new-avoid))))
)

(skip-proofs
(define match-and-replace ((tterm good-typed-term-p)
                           (supertype type-to-types-alist-p)
                           (rep thm-spec-p)
                           (acc var-acc-p))
  :returns (mv (new-tt good-typed-term-p)
               (new-acc var-acc-p))
  (b* (((unless (mbt (and (good-typed-term-p tterm)
                          (type-to-types-alist-p supertype)
                          (thm-spec-p rep)
                          (var-acc-p acc))))
        (mv (make-typed-term) (make-var-acc)))
       ((thm-spec ts1) rep)
       ((typed-term tt) tterm)
       ((var-acc a) acc)
       ((mv ok term-lst subst) (get-subst tt ts1.lhs))
       ((unless ok) (mv tt a))
       ((thm-spec ts2) (substitute-into-thm-spec rep subst))
       ;; Check if hypotheses are satisfied
       (ok (path-test-list
            `(if ,tt.judgements ,tt.path-cond 'nil) ts2.hypotheses))
       ((unless ok) (mv tt a))
       ((mv exists? new-var new-var-acc) (get-var ts2 a))
       ((var-acc a2) new-var-acc)
       ((thm-spec ts3) (generalize-thm-spec ts2 new-var))
       (var-pair (make-var-pair :var-hyp ts3.var-hyp
                                :hyp-judge ts3.hyp-judge))
       (new-hyp-alst
        (if exists? a2.hyp-alst (acons new-var var-pair a2.hyp-alst)))
       (total-judge (reconstruct-judge tt term-lst ts3 new-var supertype)))
    (mv (change-typed-term tt :term ts3.rhs :judgements total-judge)
        (change-var-acc a2 :hyp-alst new-hyp-alst))))
)

(define match-and-replace-list ((tterm good-typed-term-p)
                                (supertype type-to-types-alist-p)
                                (replaces thm-spec-list-p)
                                (acc var-acc-p))
  :returns (mv (new-tt good-typed-term-p)
               (new-acc var-acc-p))
  (b* (((unless (mbt (and (good-typed-term-p tterm)
                          (type-to-types-alist-p supertype)
                          (thm-spec-list-p replaces)
                          (var-acc-p acc))))
        (mv (make-typed-term) (make-var-acc)))
       ((unless (consp replaces)) (mv tterm acc))
       ((cons rep-hd rep-tl) replaces)
       ((mv new-tt new-acc) (match-and-replace tterm supertype rep-hd acc))
       ((unless (equal tterm new-tt)) (mv new-tt new-acc)))
    (match-and-replace-list tterm supertype rep-tl new-acc)))

(skip-proofs
(define replace-quote ((tterm good-typed-term-p)
                       (replace-options replace-options-p)
                       (path-cond pseudo-termp)
                       (acc var-acc-p))
  :guard (equal (typed-term->kind tterm) 'quotep)
  :returns (mv (new-tt good-typed-term-p)
               (new-acc var-acc-p))
  (b* (((unless (mbt (and (replace-options-p replace-options)
                          (equal (typed-term->kind tterm) 'quotep)
                          (good-typed-term-p tterm)
                          (pseudo-termp path-cond)
                          (var-acc-p acc))))
        (mv (make-typed-term) (make-var-acc)))
       ((typed-term tt) tterm)
       ((replace-options ro) replace-options)
       (re-lst (find-replaces tt ro.replaces))
       ((mv tt1 new-acc)
        (match-and-replace-list tt ro.supertype re-lst acc)))
    (mv (change-typed-term tt1 :path-cond path-cond) new-acc))
  ///
  (defthm typed-term-of-replace-quote
    (typed-term-p (replace-quote tterm replace-options path-cond acc))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance
                    good-typed-term-implies-typed-term
                    (tterm
                     (replace-quote tterm replace-options path-cond acc))))))))
)

(skip-proofs
(define replace-variable ((tterm good-typed-term-p)
                          (replace-options replace-options-p)
                          (path-cond pseudo-termp)
                          (acc var-acc-p))
  :guard (equal (typed-term->kind tterm) 'variablep)
  :returns (mv (new-tt good-typed-term-p)
               (new-acc var-acc-p))
  (b* (((unless (mbt (and (replace-options-p replace-options)
                          (equal (typed-term->kind tterm) 'variablep)
                          (good-typed-term-p tterm)
                          (pseudo-termp path-cond)
                          (var-acc-p acc))))
        (mv (make-typed-term) (make-var-acc)))
       ((typed-term tt) tterm)
       ((replace-options ro) replace-options)
       (re-lst (find-replaces tt ro.replaces))
       ((mv tt1 acc1)
        (match-and-replace-list tt ro.supertype re-lst acc)))
    (mv (change-typed-term tt1 :path-cond path-cond) acc1)))
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
                      (acc var-acc-p)
                      state)
    :guard (equal (typed-term->kind tterm) 'ifp)
    :returns (mv (new-tt good-typed-term-p)
                 (new-acc var-acc-p))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (replace-options-p replace-options)
                            (equal (typed-term->kind tterm) 'ifp)
                            (good-typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (var-acc-p acc))))
          (mv (make-typed-term) (make-var-acc)))
         ((replace-options ro) replace-options)
         ((typed-term tt) tterm)
         ((typed-term tt-cond) (typed-term-if->cond tt))
         ((typed-term tt-then) (typed-term-if->then tt))
         ((typed-term tt-else) (typed-term-if->else tt))
         ((typed-term tt-top) (typed-term->top tt))
         ((mv new-cond acc-cond) (replace-term tt-cond ro path-cond acc state))
         ((typed-term new-ttc) new-cond)
         ((mv then-path-cond else-path-cond)
          (mv `(if ,(simple-transformer new-ttc.term) ,path-cond 'nil)
              `(if ,(simple-transformer `(not ,new-ttc.term)) ,path-cond
                 'nil)))
         ((mv new-then acc-then)
          (replace-term tt-then ro then-path-cond acc-cond state))
         ((typed-term new-ttt) new-then)
         ((mv new-else acc-else)
          (replace-term tt-else ro else-path-cond acc-then state))
         ((typed-term new-tte) new-else)
         (new-term `(if ,new-ttc.term ,new-ttt.term ,new-tte.term))
         (new-top-judge (generate-judge-from-equality new-term tt-top.term
                                                      tt-top.judgements
                                                      ro.supertype))
         (new-top (change-typed-term tt-top
                                     :term new-term
                                     :path-cond path-cond
                                     :judgements new-top-judge)))
      (mv (make-typed-if new-top new-cond new-then new-else) acc-else)))

  (define replace-fncall ((tterm good-typed-term-p)
                          (replace-options replace-options-p)
                          (path-cond pseudo-termp)
                          (acc var-acc-p)
                          state)
    :guard (equal (typed-term->kind tterm) 'fncallp)
    :returns (mv (new-tt good-typed-term-p)
                 (new-acc var-acc-p))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (replace-options-p replace-options)
                            (equal (typed-term->kind tterm) 'fncallp)
                            (good-typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (var-acc-p acc))))
          (mv (make-typed-term) (make-var-acc)))
         ((replace-options ro) replace-options)
         ((typed-term tt) tterm)
         ((cons fn &) tt.term)
         (tt-actuals (typed-term-fncall->actuals tt))
         ((typed-term tt-top) (typed-term->top tt))
         ((mv tt1-actuals actuals-acc)
          (replace-term-list tt-actuals ro path-cond acc state))
         (tt1a.term-lst (typed-term-list->term-lst tt1-actuals))
         (term1 `(,fn ,@tt1a.term-lst))
         (tt1-judge-top (generate-judge-from-equality term1 tt-top.term
                                                      tt-top.judgements
                                                      ro.supertype))
         (tt1-top (change-typed-term tt-top
                                     :term term1
                                     :path-cond path-cond
                                     :judgements tt1-judge-top))
         ((unless (make-typed-fncall-guard tt1-top tt1-actuals)) (mv tt acc))
         (tt1 (make-typed-fncall tt1-top tt1-actuals))
         (re-lst (find-replaces tt1 ro.replaces)))
      (match-and-replace-list tt1 ro.supertype re-lst actuals-acc)))

  (define replace-term ((tterm good-typed-term-p)
                        (replace-options replace-options-p)
                        (path-cond pseudo-termp)
                        (acc var-acc-p)
                        state)
    :returns (mv (new-tt good-typed-term-p)
                 (new-acc var-acc-p))
    :measure (list (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (good-typed-term-p tterm)
                            (replace-options-p replace-options)
                            (pseudo-termp path-cond)
                            (var-acc-p acc))))
          (mv (make-typed-term) (make-var-acc)))
         ((if (equal (typed-term->kind tterm) 'variablep))
          (replace-variable tterm replace-options path-cond acc))
         ((if (equal (typed-term->kind tterm) 'ifp))
          (replace-if tterm replace-options path-cond acc state))
         ((if (equal (typed-term->kind tterm) 'fncallp))
          (replace-fncall tterm replace-options path-cond acc state))
         ((if (equal (typed-term->kind tterm) 'quotep))
          (replace-quote tterm replace-options path-cond acc)))
      (prog2$ (er hard? 'term-replacement=>replace-term
                  "Found lambda term in goal.~%")
              (mv tterm acc))))

  (define replace-term-list ((tterm-lst good-typed-term-list-p)
                             (replace-options replace-options-p)
                             (path-cond pseudo-termp)
                             (acc var-acc-p)
                             state)
    :returns (mv (new-ttl good-typed-term-list-p)
                 (new-acc var-acc-p))
    :measure (list (acl2-count (typed-term-list->term-lst tterm-lst)) 1)
    (b* (((unless (mbt (and (good-typed-term-list-p tterm-lst)
                            (replace-options-p replace-options)
                            (pseudo-termp path-cond)
                            (var-acc-p acc))))
          (mv nil (make-var-acc)))
         ((unless (consp tterm-lst)) (mv nil acc))
         ((cons tterm-hd tterm-tl) tterm-lst)
         ((mv tt-car car-acc)
          (replace-term tterm-hd replace-options path-cond acc state))
         ((mv tt-cdr cdr-acc)
          (replace-term-list tterm-tl replace-options path-cond car-acc state))
         ((unless (implies (consp tt-cdr)
                           (equal (typed-term->path-cond tt-car)
                                  (typed-term-list->path-cond tt-cdr))))
          (mv tterm-lst acc)))
      (mv (cons tt-car tt-cdr) cdr-acc)))
  ///
  (defthm typed-term-of-replace-fncall
    (typed-term-p (replace-fncall tterm replace-options path-cond acc state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (replace-fncall tterm replace-options path-cond
                                               acc state)))))))
  (defthm typed-term-of-replace-if
    (typed-term-p (replace-if tterm replace-options path-cond acc state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (replace-if tterm replace-options path-cond
                                           acc state)))))))
  (defthm typed-term-of-replace-term
    (typed-term-p (replace-term tterm replace-options path-cond acc state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (replace-term tterm replace-options path-cond
                                             acc state)))))))
  (defthm typed-term-list-of-replace-term-list
    (typed-term-list-p
     (replace-term-list tterm-lst replace-options path-cond acc state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-list-implies-typed-term-list)
             :use ((:instance good-typed-term-list-implies-typed-term-list
                              (tterm-lst
                               (replace-term-list tterm-lst replace-options
                                                  path-cond acc state)))))))
  )
)

(skip-proofs
 (verify-guards replace-term)
 )

(skip-proofs
(define add-freevar-hypo ((tterm good-typed-term-p)
                          (pair var-pair-p))
  :returns (new-term good-typed-term-p)
  (b* (((unless (good-typed-term-p tterm)) (make-typed-term))
       (pair (var-pair-fix pair))
       ((typed-term tt) tterm)
       ((var-pair p) pair)
       (tt-cond (make-typed-term :term p.var-hyp
                                 :judgements `(if (if ,p.hyp-judge 't 'nil)
                                                 (if 't 't 'nil)
                                                'nil)))
       (top-term `(if ,p.var-hyp ,tt.term 't))
       (judge-top `(if (booleanp ,top-term) 't 'nil))
       (tt-top (make-typed-term :term top-term :judgements judge-top))
       (pc-then `(if ,(simple-transformer p.var-hyp) 't 'nil))
       (pc-else `(if ,(simple-transformer `(not ,p.var-hyp)) 't 'nil))
       (tt-then (change-typed-term tt :path-cond pc-then))
       (tt-else (make-typed-term :term ''t :path-cond pc-else
                                 :judgements `(if (booleanp 't) 't 'nil))))
    (make-typed-if tt-top tt-cond tt-then tt-else)))
)

(define add-freevar-hypo-list ((tterm good-typed-term-p)
                               (hyp-alst sym-var-pair-alistp))
  :returns (new-tterm good-typed-term-p)
  :measure (len (sym-var-pair-alist-fix hyp-alst))
  (b* (((unless (good-typed-term-p tterm)) (make-typed-term))
       (hyp-alst (sym-var-pair-alist-fix hyp-alst))
       ((unless (consp hyp-alst)) tterm)
       ((cons first rest) hyp-alst)
       ((cons & hypo) first)
       (tterm1 (add-freevar-hypo tterm hypo)))
    (add-freevar-hypo-list tterm1 rest)))

(define term-replacement-fn ((cl pseudo-term-listp)
                             (smtlink-hint t)
                             state)
  :returns (subgoal-lst pseudo-term-list-listp
                        :hints (("Goal" :in-theory (enable pseudo-termp))))
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint)) (list cl))
       (goal (disjoin cl))
       (h (construct-replace-options smtlink-hint state))
       ((mv okp tterm)
        (case-match goal
          (('implies ('if judges smt-judges ''nil) term)
           (mv t (make-typed-term :term term
                                  :path-cond ''t
                                  :judgements judges
                                  :smt-judgements smt-judges)))
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
       (va (make-var-acc :var-alst nil
                         :hyp-alst nil
                         :avoid (acl2::simple-term-vars goal)))
       ((mv replaced-tterm new-va) (replace-term tterm h ''t va state))
       ((var-acc a) new-va)
       (updated-tterm (add-freevar-hypo-list replaced-tterm a.hyp-alst))
       (updated-judgements (typed-term->judgements updated-tterm))
       (updated-smt-judgements (typed-term->smt-judgements updated-tterm))
       (updated-term (typed-term->term updated-tterm))
       (new-cl `((implies (if ,updated-judgements ,updated-smt-judgements 'nil)
                          ,updated-term)))
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
