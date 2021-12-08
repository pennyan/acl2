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
(include-book "returns-judgement")
(include-book "type-inference-bottomup")
(include-book "type-inference-topdown")
(include-book "replace-options")

(define fncallp ((x pseudo-termp))
  :returns (okp booleanp)
  (and (consp x)
       (symbolp (car x))
       (not (equal (car x) 'quote))))

(local (in-theory (e/d (fncallp)
                       ((:executable-counterpart typed-term)
                        pseudo-termp pseudo-term-listp))))

;; RUTs:
;; (implies (and (cond1 arg1) ...)
;;          (equal (f-user arg1 ...)
;;                 (f-smt arg1 arg2 ...)))
;; (implies (and (cond1 arg1) (cond2 arg1))
;;          (equal (f-fix arg1) arg1))
;; (implies (some-type-p nil)
;;          (equal nil (some-type-nil)))

(define rut ((term pseudo-termp))
  :returns (rut-lst pseudo-term-listp)
  (b* ((term (pseudo-term-fix term))
       ((unless (fncallp term)) (list term))
       ((cons & actuals) term))
    (cons term actuals)))

(define fncall-rut-p ((lhs pseudo-termp)
                      (rhs pseudo-termp))
  :returns (okp booleanp)
  (b* ((lhs (pseudo-term-fix lhs))
       (rhs (pseudo-term-fix rhs)))
    (and (fncallp rhs)
         (subsetp-equal (cdr rhs) (rut lhs)))))

(define non-fncall-rut-p ((lhs pseudo-termp)
                          (rhs pseudo-termp))
  :returns (okp booleanp)
  (b* ((lhs (pseudo-term-fix lhs))
       (rhs (pseudo-term-fix rhs)))
    (consp (member-equal rhs (rut lhs)))))

(define rut-p ((lhs pseudo-termp)
               (rhs pseudo-termp))
  :returns (okp booleanp)
  (b* ((lhs (pseudo-term-fix lhs))
       (rhs (pseudo-term-fix rhs)))
    (or (fncall-rut-p lhs rhs)
        (non-fncall-rut-p lhs rhs))))

(define make-term-list-judge-alist ((tterm-lst typed-term-list-p))
  :guard (good-typed-term-list-p tterm-lst)
  :returns (judge-alst pseudo-term-alistp)
  :verify-guards nil
  (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                          (good-typed-term-list-p tterm-lst))))
        nil)
       ((unless (consp tterm-lst)) nil)
       ((cons tterm-hd tterm-tl) tterm-lst)
       ((typed-term tt) tterm-hd))
    (acons tt.term tt.judgements (make-term-list-judge-alist tterm-tl))))

(verify-guards make-term-list-judge-alist)

(define rut-actual-judgements ((tterm typed-term-p))
  :guard (and (good-typed-term-p tterm)
              (or (equal (typed-term->kind tterm) 'fncallp)
                  (equal (typed-term->kind tterm) 'quotep)))
  :returns (actual-alst pseudo-term-alistp)
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (good-typed-term-p tterm)
                          (or (equal (typed-term->kind tterm) 'fncallp)
                              (equal (typed-term->kind tterm) 'quotep)))))
        nil)
       ((if (equal (typed-term->kind tterm) 'quotep)) nil)
       ((typed-term tt) tterm)
       (tt-actuals (typed-term-fncall->actuals tt)))
    (make-term-list-judge-alist tt-actuals)))

(local
 (defthm crock
   (implies (and (pseudo-term-alistp x) (assoc-equal y x))
            (pseudo-termp (cdr (assoc-equal y x)))))
 )

(define update-actual-judgements ((actual-lst pseudo-term-listp)
                                  (actual-alst pseudo-term-alistp))
  :returns (new-judges pseudo-termp)
  :measure (len actual-lst)
  (b* ((actual-lst (pseudo-term-list-fix actual-lst))
       (actual-alst (pseudo-term-alist-fix actual-alst))
       ((unless (consp actual-lst)) ''t)
       ((cons actual-hd actual-tl) actual-lst)
       (exists? (assoc-equal actual-hd actual-alst))
       ((unless exists?)
        (er hard? 'term-replacement=>update-actual-judgements
            "Actual ~p0 doesn't exist in alist ~p1~%"
            actual-hd actual-alst)))
    `(if ,(cdr exists?)
         ,(update-actual-judgements actual-tl actual-alst)
       'nil)))

(skip-proofs
(define update-judgements ((tterm typed-term-p)
                           (new-term pseudo-termp)
                           (supertype-alst type-to-types-alist-p))
  :guard (and (good-typed-term-p tterm)
              (or (equal (typed-term->kind tterm) 'fncallp)
                  (equal (typed-term->kind tterm) 'quotep))
              (rut-p (typed-term->term tterm) new-term))
  :returns (new-tterm good-typed-term-p)
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (good-typed-term-p tterm)
                          (pseudo-termp new-term)
                          (type-to-types-alist-p supertype-alst)
                          (or (equal (typed-term->kind tterm) 'fncallp)
                              (equal (typed-term->kind tterm) 'quotep))
                          (rut-p (typed-term->term tterm) new-term))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((if (equal (typed-term->kind tterm) 'quotep))
        (change-typed-term
         tt
         :term new-term
         :judgements (generate-judge-from-equality
                      new-term tt.term tt.judgements supertype-alst)))
       ((typed-term ttt) (typed-term->top tt))
       ;; Make an alist that maps terms to their judgements
       ;; Terms include all ruts terms including the term and its actuals
       (actual-alst (rut-actual-judgements tterm))
       (top-judge (generate-judge-from-equality new-term tt.term ttt.judgements
                                                supertype-alst))
       ((if (non-fncall-rut-p tt.term new-term))
        (b* ((exists? (assoc-equal new-term actual-alst))
             ((unless exists?)
              (prog2$ (er hard? 'term-replacement=>update-judgements
                          "Actual ~p0 doesn't exist in alist ~p1~%"
                          new-term actual-alst)
                      (make-typed-term))))
          (change-typed-term tt :term new-term :judgements (cdr exists?))))
       ((cons & actuals) tt.term)
       (actual-judges (update-actual-judgements actuals actual-alst))
       (all-judge `(if ,top-judge ,actual-judges 'nil)))
    (change-typed-term tt :term new-term :judgements all-judge)))
)

(define replace-with-spec ((tterm good-typed-term-p)
                           (replace-spec thm-spec-p)
                           (supertype-alst type-to-types-alist-p)
                           state)
  :guard (or (equal (typed-term->kind tterm) 'fncallp)
             (equal (typed-term->kind tterm) 'quotep))
  :returns (new-tterm good-typed-term-p)
  (b* (((unless (mbt (and (good-typed-term-p tterm)
                          (thm-spec-p replace-spec)
                          (type-to-types-alist-p supertype-alst)
                          (or (equal (typed-term->kind tterm) 'fncallp)
                              (equal (typed-term->kind tterm) 'quotep)))))
        (make-typed-term))
       ((typed-term tt) tterm)
       (fn (if (quotep tt.term) nil (car tt.term)))
       (actuals (if (quotep tt.term) nil (cdr tt.term)))
       (substed-theorem (get-substed-theorem replace-spec actuals state))
       ((mv ok hypo concl)
        (get-hypotheses-and-conclusion substed-theorem fn actuals))
       ((unless ok)
        (prog2$ (er hard? 'term-replacement=>replace-with-spec
                    "Malformed replacement theorem ~p0.~%" substed-theorem)
                tt))
       (judgements (if (equal (typed-term->kind tterm) 'fncallp)
                       `(if ,(typed-term->judgements (typed-term->top tt))
                            ,(typed-term-list->judgements
                              (typed-term-fncall->actuals tt))
                          'nil)
                     tt.judgements))
       (ok1 (path-test-list `(if ,judgements ,tt.path-cond 'nil) hypo))
       ((unless ok1) tterm)
       ((mv ok2 rhs)
        (case-match concl
          (('equal !tt.term rhs) (mv t rhs))
          (& (mv nil nil))))
       ((unless (and ok2 (rut-p tt.term rhs)))
        (prog2$ (er hard? 'term-replacement=>replace-with-spec
                    "Malformed replacement rhs ~p0.~%" concl)
                tt)))
    (update-judgements tt rhs supertype-alst)))

(define generate-replacement-loop ((tterm good-typed-term-p)
                                   (replace-specs thm-spec-list-p)
                                   (supertype-alst type-to-types-alist-p)
                                   state)
  :guard (or (equal (typed-term->kind tterm) 'fncallp)
             (equal (typed-term->kind tterm) 'quotep))
  :returns (new-tterm good-typed-term-p)
  (b* (((unless (mbt (and (good-typed-term-p tterm)
                          (thm-spec-list-p replace-specs)
                          (type-to-types-alist-p supertype-alst)
                          (or (equal (typed-term->kind tterm) 'fncallp)
                              (equal (typed-term->kind tterm) 'quotep)))))
        (make-typed-term))
       ((unless (consp replace-specs)) tterm)
       ((cons replace-hd replace-tl) replace-specs)
       (new-tterm (replace-with-spec tterm replace-hd supertype-alst state))
       ((unless (equal new-tterm tterm)) new-tterm))
    (generate-replacement-loop tterm replace-tl supertype-alst state)))

(skip-proofs
(define generate-replacement ((tterm good-typed-term-p)
                              (replaces symbol-thm-spec-list-alist-p)
                              (supertype-alst type-to-types-alist-p)
                              state)
  :guard (or (equal (typed-term->kind tterm) 'fncallp)
             (equal (typed-term->kind tterm) 'quotep))
  :returns (new-tterm good-typed-term-p)
  (b* (((unless (mbt (and (good-typed-term-p tterm)
                          (symbol-thm-spec-list-alist-p replaces)
                          (type-to-types-alist-p supertype-alst)
                          (or (equal (typed-term->kind tterm) 'fncallp)
                              (equal (typed-term->kind tterm) 'quotep)))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((if (equal (typed-term->kind tterm) 'quotep))
        (b* ((exists? (assoc-equal (cadr tt.term) replaces))
             ((unless exists?) tt))
          (generate-replacement-loop tt (cdr exists?) supertype-alst state)))
       ((cons fn &) tt.term)
       ;; currently only support replaces for symbols and function calls
       (exists? (assoc-equal fn replaces))
       ((unless exists?) tt))
    (generate-replacement-loop tterm (cdr exists?) supertype-alst state)))
)

(skip-proofs
(defthm correctness-of-generate-replacement
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (good-typed-term-p tterm)
                (symbol-thm-spec-list-alist-p replaces)
                (type-to-types-alist-p supertype-alst)
                (alistp a)
                (ev-smtcp (correct-typed-term term) a))
           (ev-smtcp (correct-typed-term
                      (generate-replacement tterm replaces
                                            supertype-alst state))
                     a)))
)

;; Support we have a replacement theorem statement:
;; (implies (and (cond1 arg1) …)
;;          (equal term-user term-smt))
;; Let reusable-user-terms (RUTs) be the set {term-user, arguments to the
;; top-level function call of term-user}.
;; We require that either term-smt is an element of RUTs, or term-smt is a
;; function call where each argument to the top-level function call of term-smt is
;; an element of RUTs. 
;; If the replacement satisfies these requirements, then you can construct the
;; typed-term for term-smt from the typed-terms of the elements of RUTs.

(skip-proofs
(defines replace-term
  :well-founded-relation l<
  :flag-local nil
  :returns-hints (("Goal"
                   :in-theory (e/d (good-typed-term-list-p)
                                   (pseudo-termp
                                    acl2-count
                                    lambda-of-pseudo-lambdap
                                    symbol-listp))))

  (define replace-rut ((tterm typed-term-p)
                       (replace-options replace-options-p)
                       (type-options type-options-p)
                       (path-cond pseudo-termp)
                       (clock natp)
                       state)
    :guard (and (good-typed-term-p tterm)
                (or (equal (typed-term->kind tterm) 'fncallp)
                    (equal (typed-term->kind tterm) 'quotep)))
    :returns (new-tt good-typed-term-p)
    :measure (list (nfix clock) (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (replace-options-p replace-options)
                            (type-options-p type-options)
                            (equal (typed-term->kind tterm) 'fncallp)
                            (good-typed-term-p tterm)
                            (natp clock))))
          (make-typed-term))
         ((if (zp clock)) tterm)
         ((replace-options ro) replace-options)
         ((type-options to) type-options)
         ((typed-term tt) tterm)
         (new-tterm (generate-replacement tt ro.replaces to.supertype state))
         ((if (and (equal new-tterm tt)
                   (equal (typed-term->kind tt) 'quotep)))
          (change-typed-term tt :path-cond path-cond))
         ((if (and (equal new-tterm tt)
                   (equal (typed-term->kind tt) 'fncallp)))
          (b* ((tt-actuals (typed-term-fncall->actuals tt))
               ((typed-term tt-top) (typed-term->top tt))
               ((cons fn &) tt.term)
               (tt1-actuals
                (replace-term-list tt-actuals ro to path-cond clock state))
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
      (replace-term (change-typed-term new-tterm :path-cond path-cond)
                    ro to path-cond (1- clock) state)))

  (define replace-if ((tterm typed-term-p)
                      (replace-options replace-options-p)
                      (type-options type-options-p)
                      (path-cond pseudo-termp)
                      (clock natp)
                      state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'ifp))
    :returns (new-tt good-typed-term-p)
    :measure (list (nfix clock) (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (replace-options-p replace-options)
                            (type-options-p type-options)
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
         (new-cond (replace-term tt-cond ro type-options path-cond clock state))
         ((typed-term new-ttc) new-cond)
         ((mv then-path-cond else-path-cond)
          (mv `(if ,(simple-transformer new-ttc.term) ,path-cond 'nil)
              `(if ,(simple-transformer `(not ,new-ttc.term)) ,path-cond
                 'nil)))
         (new-then (replace-term tt-then ro type-options then-path-cond clock state))
         ((typed-term new-ttt) new-then)
         (new-else (replace-term tt-else ro type-options else-path-cond clock state))
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

  (define replace-term ((tterm typed-term-p)
                        (replace-options replace-options-p)
                        (type-options type-options-p)
                        (path-cond pseudo-termp)
                        (clock natp)
                        state)
    :guard (good-typed-term-p tterm)
    :returns (new-tt good-typed-term-p)
    :measure (list (nfix clock) (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (good-typed-term-p tterm)
                            (replace-options-p replace-options)
                            (type-options-p type-options)
                            (pseudo-termp path-cond)
                            (natp clock))))
          (make-typed-term))
         ((if (equal (typed-term->kind tterm) 'variablep))
          (change-typed-term tterm :path-cond path-cond))
         ((if (equal (typed-term->kind tterm) 'ifp))
          (replace-if tterm replace-options type-options path-cond clock
                      state))
         ((if (or (equal (typed-term->kind tterm) 'quotep)
                  (equal (typed-term->kind tterm) 'fncallp)))
          (replace-rut tterm replace-options type-options path-cond clock
                       state)))
      (prog2$ (er hard? 'term-replacement=>replace-term
                  "Found lambda term in goal.~%")
              tterm)))

  (define replace-term-list ((tterm-lst typed-term-list-p)
                             (replace-options replace-options-p)
                             (type-options type-options-p)
                             (path-cond pseudo-termp)
                             (clock natp)
                             state)
    :returns (new-ttl good-typed-term-list-p)
    :guard (good-typed-term-list-p tterm-lst)
    :measure (list (nfix clock) (acl2-count (typed-term-list->term-lst tterm-lst)) 1)
    (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                            (good-typed-term-list-p tterm-lst)
                            (replace-options-p replace-options)
                            (type-options-p type-options)
                            (pseudo-termp path-cond)
                            (natp clock))))
          nil)
         ((unless (consp tterm-lst)) nil)
         ((cons tterm-hd tterm-tl) tterm-lst)
         (tt-car (replace-term tterm-hd replace-options type-options
                               path-cond clock state))
         (tt-cdr (replace-term-list tterm-tl replace-options type-options
                             path-cond clock state))
         ((unless (implies (consp tt-cdr)
                           (equal (typed-term->path-cond tt-car)
                                  (typed-term-list->path-cond tt-cdr))))
          tterm-lst))
      (cons tt-car tt-cdr)))
  ///
  (defthm typed-term-of-replace-rut
    (typed-term-p (replace-rut tterm replace-options type-options
                               path-cond clock state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (replace-rut tterm replace-options 
                                            type-options path-cond
                                            clock state)))))))
  (defthm typed-term-of-replace-if
    (typed-term-p (replace-if tterm replace-options type-options path-cond
                              clock state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (replace-if tterm replace-options type-options
                                           path-cond clock state)))))))
  (defthm typed-term-of-replace-term
    (typed-term-p (replace-term tterm replace-options type-options
                                path-cond clock state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (replace-term tterm replace-options type-options
                                             path-cond clock state)))))))
  (defthm typed-term-list-of-replace-term-list
    (typed-term-list-p
     (replace-term-list tterm-lst replace-options type-options path-cond
                        clock state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-list-implies-typed-term-list)
             :use ((:instance good-typed-term-list-implies-typed-term-list
                              (tterm-lst
                               (replace-term-list tterm-lst replace-options
                                                  type-options path-cond
                                                  clock state)))))))
  )
)

(skip-proofs
(defthm-replace-term-flag
  (defthm replace-if-maintains-path-cond
    (implies (and (replace-options-p replace-options)
                  (type-options-p type-options)
                  (equal (typed-term->kind tterm) 'ifp)
                  (good-typed-term-p tterm)
                  (pseudo-termp path-cond)
                  (natp clock))
             (equal (typed-term->path-cond
                     (replace-if tterm replace-options type-options
                                 path-cond clock state))
                    (typed-term->path-cond tterm)))
    :flag replace-if
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp symbol-listp))
                              :expand (replace-if tterm replace-options
                                                  type-options path-cond
                                                  clock state)))))
  (defthm replace-rut-maintains-path-cond
    (implies (and (replace-options-p replace-options)
                  (type-options-p type-options)
                  (equal (typed-term->kind tterm) 'fncallp)
                  (good-typed-term-p tterm)
                  (pseudo-termp path-cond)
                  (natp clock))
             (equal (typed-term->path-cond
                     (replace-rut tterm replace-options type-options
                                  path-cond clock state))
                    (typed-term->path-cond tterm)))
    :flag replace-rut
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp symbol-listp))
                   :expand ((replace-rut tterm replace-options type-options
                                         path-cond clock state)
                            (replace-rut tterm replace-options type-options
                                         path-cond 0 state))))))
  (defthm replace-term-maintains-path-cond
    (implies (and (replace-options-p replace-options)
                  (type-options-p type-options)
                  (good-typed-term-p tterm)
                  (pseudo-termp path-cond)
                  (natp clock))
             (equal (typed-term->path-cond
                     (replace-term tterm replace-options type-options
                                   path-cond clock state))
                    (typed-term->path-cond tterm)))
    :flag replace-term
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp symbol-listp))
                   :expand (replace-term tterm replace-options type-options
                                         path-cond clock state)))))
  (defthm replace-term-list-maintains-path-cond
    (implies (and (replace-options-p replace-options)
                  (type-options-p type-options)
                  (good-typed-term-list-p tterm-lst)
                  (pseudo-termp path-cond)
                  (natp clock))
             (equal (typed-term-list->path-cond
                     (replace-term-list tterm-lst replace-options type-options
                                        path-cond clock state))
                    (typed-term-list->path-cond tterm-lst)))
    :flag replace-term-list
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (typed-term-list->path-cond)
                                   (pseudo-termp symbol-listp))
                   :expand
                   ((replace-term-list tterm-lst replace-options type-options
                                       path-cond clock state)
                    (replace-term-list nil replace-options type-options
                                       path-cond clock state))))))
  :hints(("Goal"
          :in-theory (disable pseudo-termp symbol-listp))))
)

(skip-proofs
(defthm-replace-term-flag
  (defthm replace-if-maintains-term
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (replace-options-p replace-options)
                  (type-options-p type-options)
                  (equal (typed-term->kind tterm) 'ifp)
                  (good-typed-term-p tterm)
                  (pseudo-termp path-cond)
                  (natp clock)
                  (alistp a)
                  (ev-smtcp (typed-term->path-cond tterm) a)
                  (ev-smtcp (typed-term->judgements tterm) a))
             (equal (ev-smtcp (typed-term->term
                               (replace-if tterm replace-options type-options
                                           path-cond clock state))
                               a)
                    (ev-smtcp (typed-term->term tterm) a)))
    :flag replace-if
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (make-typed-if) ())
                              :expand (replace-if tterm replace-options
                                                  type-options path-cond
                                                  clock state)))))
  (defthm replace-rut-maintains-term
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (replace-options-p replace-options)
                  (type-options-p type-options)
                  (equal (typed-term->kind tterm) 'fncallp)
                  (good-typed-term-p tterm)
                  (pseudo-termp path-cond)
                  (natp clock)
                  (alistp a)
                  (ev-smtcp (typed-term->path-cond tterm) a)
                  (ev-smtcp (typed-term->judgements tterm) a))
             (equal (ev-smtcp (typed-term->term
                               (replace-rut tterm replace-options
                                            type-options path-cond clock
                                            state))
                              a)
                    (ev-smtcp (typed-term->term tterm) a)))
    :flag replace-rut
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () ())
                   :expand ((replace-rut tterm replace-options type-options
                                         path-cond clock state)
                            (replace-rut tterm replace-options type-options
                                         path-cond 0 state))))))
  (defthm replace-term-maintains-term
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (replace-options-p replace-options)
                  (type-options-p type-options)
                  (good-typed-term-p tterm)
                  (pseudo-termp path-cond)
                  (natp clock)
                  (alistp a)
                  (ev-smtcp (typed-term->path-cond tterm) a)
                  (ev-smtcp (typed-term->judgements tterm) a))
             (equal (ev-smtcp (typed-term->term
                               (replace-term tterm replace-options type-options
                                             path-cond clock state))
                              a)
                    (ev-smtcp (typed-term->term tterm) a)))
    :flag replace-term
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () ())
                   :expand (replace-term tterm replace-options type-options
                                         path-cond clock state)))))
  (defthm replace-term-list-maintains-term-lst
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (replace-options-p replace-options)
                  (type-options-p type-options)
                  (good-typed-term-list-p tterm-lst)
                  (pseudo-termp path-cond)
                  (natp clock)
                  (alistp a)
                  (ev-smtcp (typed-term-list->path-cond tterm-lst) a)
                  (ev-smtcp (typed-term-list->judgements tterm-lst) a))
             (equal (ev-smtcp-lst (typed-term-list->term-lst
                                   (replace-term-list tterm-lst replace-options
                                                      type-options
                                                      path-cond clock
                                                      state))
                                  a)
                    (ev-smtcp-lst (typed-term-list->term-lst tterm-lst) a)))
    :flag replace-term-list
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (typed-term-list->term-lst) ())
                   :expand
                   ((replace-term-list tterm-lst replace-options type-options
                                       path-cond clock state)
                    (replace-term-list nil replace-options type-options
                                       path-cond clock state)))))))
)

(skip-proofs
(defthm-replace-term-flag
  (defthm correctness-of-replace-if
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (replace-options-p replace-options)
                  (type-options-p type-options)
                  (equal (typed-term->kind tterm) 'ifp)
                  (good-typed-term-p tterm)
                  (pseudo-termp path-cond)
                  (natp clock)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (replace-if tterm replace-options type-options
                                    path-cond clock state))
                       a))
    :flag replace-if
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (correct-typed-term
                                    make-typed-if)
                                   (pseudo-termp symbol-listp))
                              :expand (replace-if tterm replace-options
                                                  type-options path-cond
                                                  clock state)))))
  (defthm correctness-of-replace-rut
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (replace-options-p replace-options)
                  (type-options-p type-options)
                  (equal (typed-term->kind tterm) 'fncallp)
                  (good-typed-term-p tterm)
                  (pseudo-termp path-cond)
                  (natp clock)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (replace-rut tterm replace-options type-options
                                     path-cond clock state))
                       a))
    :flag replace-rut
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (correct-typed-term make-typed-fncall)
                                   (pseudo-termp
                                    symbol-listp))
                              :expand ((replace-rut tterm replace-options
                                                    type-options path-cond
                                                    clock state)
                                       (replace-rut tterm replace-options
                                                    type-options path-cond 0
                                                    state))))))
  (defthm correctness-of-replace-term
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (replace-options-p replace-options)
                  (type-options-p type-options)
                  (good-typed-term-p tterm)
                  (pseudo-termp path-cond)
                  (natp clock)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (replace-term tterm replace-options type-options
                                      path-cond clock state))
                       a))
    :flag replace-term
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () (pseudo-termp))
                   :expand (replace-term tterm replace-options type-options
                                         path-cond clock state)))))
  (defthm correctness-of-replace-term-list
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (replace-options-p replace-options)
                  (type-options-p type-options)
                  (good-typed-term-list-p tterm-lst)
                  (pseudo-termp path-cond)
                  (natp clock)
                  (alistp a)
                  (ev-smtcp (correct-typed-term-list tterm-lst) a))
             (ev-smtcp
              (correct-typed-term-list
               (replace-term-list tterm-lst replace-options type-options
                                  path-cond clock state))
              a))
    :flag replace-term-list
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp))
                   :expand
                   ((replace-term-list tterm-lst replace-options type-options
                                       path-cond clock state)
                    (replace-term-list nil replace-options type-options
                                       path-cond clock state))))))
  :hints(("Goal"
          :in-theory (disable pseudo-termp symbol-listp))))
)

(define term-replacement-fn ((cl pseudo-term-listp)
                             (smtlink-hint t)
                             state)
  :returns (subgoal-lst pseudo-term-list-listp
                        :hints (("Goal" :in-theory (enable pseudo-termp))))
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint)) (list cl))
       (count (smtlink-hint->wrld-fn-len smtlink-hint))
       (goal (disjoin cl))
       (h (construct-replace-options smtlink-hint))
       ((type-options to) (construct-type-options smtlink-hint goal))
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
       (replaced-tterm (replace-term tterm h to ''t count state))
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
  :hints (("Goal"
           :do-not-induct t
           :case-split-limitations (0 1)
           :in-theory (e/d (term-replacement-cp
                            term-replacement-fn
                            correct-typed-term)
                           (ev-smtcp-of-if-call
                            correctness-of-path-test-list-corollary
                            symbol-listp
                            correctness-of-path-test-list))
           :use ((:instance correctness-of-replace-term
                            (tterm (typed-term (caddr (disjoin cl))
                                               ''t
                                               (cadr (disjoin cl))))
                            (replace-options (construct-replace-options hint))
                            (type-options
                             (construct-type-options hint (disjoin cl)))
                            (path-cond ''t)
                            (clock (smtlink-hint->wrld-fn-len hint))))))
  :rule-classes :clause-processor)
