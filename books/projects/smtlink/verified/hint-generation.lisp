;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (Oct 26th 2021)
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

(include-book "hint-options")
(include-book "typed-term-fns")
(include-book "judgement-fns")
(include-book "lambda-substitution")

(set-state-ok t)

(local (in-theory (disable (:executable-counterpart typed-term)
                           pseudo-termp pseudo-term-listp)))

(define get-type-helper ((term pseudo-termp)
                         (judge pseudo-termp)
                         (supertype type-to-types-alist-p))
  :returns (type symbolp)
  (b* ((term (pseudo-term-fix term))
       (judge (pseudo-term-fix judge))
       (supertype (type-to-types-alist-fix supertype))
       (type-pred-list (look-up-type-predicate term judge supertype))
       ((unless (equal (len type-pred-list) 1))
        (er hard? 'hint-generation=>get-type-helper
            "Found multiple type predicates: ~q0" type-pred-list)))
    (caar type-pred-list)))

(define get-type ((tterm typed-term-p)
                  (supertype type-to-types-alist-p))
  :guard (good-typed-term-p tterm)
  :returns (type symbolp)
  (b* ((tterm (typed-term-fix tterm))
       ((unless (good-typed-term-p tterm)) nil)
       (supertype (type-to-types-alist-fix supertype))
       ((typed-term tt) tterm)
       ((typed-term ttt)
        (if (or (equal (typed-term->kind tt) 'ifp)
                (equal (typed-term->kind tt) 'fncallp))
            (typed-term->top tt) tt)))
    (get-type-helper tt.term ttt.judgements supertype)))

(define get-type-list ((tterm-lst typed-term-list-p)
                       (supertype type-to-types-alist-p))
  :guard (good-typed-term-list-p tterm-lst)
  :returns (types symbol-listp)
  :measure (len tterm-lst)
  (b* ((tterm-lst (typed-term-list-fix tterm-lst))
       ((unless (good-typed-term-list-p tterm-lst)) nil)
       (supertype (type-to-types-alist-fix supertype))
       ((unless (consp tterm-lst)) nil)
       ((cons tterm-hd tterm-tl) tterm-lst))
    (cons (get-type tterm-hd supertype)
          (get-type-list tterm-tl supertype))))

(defines hint-generation
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil

  (define fncall-hint-generation ((tterm typed-term-p)
                                  (hint-options hint-options-p)
                                  (acc trusted-hint-p)
                                  state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'fncallp))
    :returns (trusted-hint trusted-hint-p)
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (hint-options-p hint-options)
                            (equal (typed-term->kind tterm) 'fncallp)
                            (good-typed-term-p tterm)
                            (trusted-hint-p acc))))
          (make-trusted-hint))
         ((hint-options ho) hint-options)
         ((trusted-hint th) acc)
         ((typed-term tt) tterm)
         ((cons fn &) tt.term)
         (tta (typed-term-fncall->actuals tt))
         ((if (assoc-equal fn th.user-fns))
          (hint-generation-list tta ho th state))
         ((if (assoc-equal fn ho.supertype))
          (hint-generation-list tta ho th state))
         (basic/uninter-exists? (assoc-equal fn ho.function))
         ((unless basic/uninter-exists?)
          (prog2$ (er hard? 'hint-generation=>fncall-hint-generation
                      "Unrecognized function: ~p0, consider adding it to the ~
                       hint.~%" fn)
                  acc))
         (func (cdr basic/uninter-exists?))
         ((smt-function f) func)
         (fn-trans (trans-hint->translation f.translation-hint))
         (new-fn (if (not (equal fn-trans "")) fn-trans (string fn)))
         (return-type (get-type tterm ho.supertype))
         (formal-types (get-type-list tta ho.supertype))
         (uninterpreted-hint (change-trans-hint
                              f.translation-hint
                              :translation new-fn
                              :formal-types formal-types
                              :return-type return-type)))
      (hint-generation-list
       tta ho
       (change-trusted-hint
        acc :user-fns (acons fn (change-smt-function
                                 func
                                 :translation-hint uninterpreted-hint
                                 :kind :uninterpreted)
                             th.user-fns))
       state)))

  (define if-hint-generation ((tterm typed-term-p)
                              (hint-options hint-options-p)
                              (acc trusted-hint-p)
                              state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'ifp))
    :returns (trusted-hint trusted-hint-p)
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (hint-options-p hint-options)
                            (equal (typed-term->kind tterm) 'ifp)
                            (good-typed-term-p tterm)
                            (trusted-hint-p acc))))
          (make-trusted-hint))
         ((hint-options ho) hint-options)
         ((typed-term tt) tterm)
         (ttc (typed-term-if->cond tt))
         (ttn (typed-term-if->then tt))
         (tte (typed-term-if->else tt))
         (acc-cond (hint-generation ttc ho acc state))
         (acc-then (hint-generation ttn ho acc-cond state)))
      (hint-generation tte ho acc-then state)))

  (define hint-generation ((tterm typed-term-p)
                           (hint-options hint-options-p)
                           (acc trusted-hint-p)
                           state)
    :guard (good-typed-term-p tterm)
    :returns (trusted-hint trusted-hint-p)
    :measure (list (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (good-typed-term-p tterm)
                            (hint-options-p hint-options)
                            (trusted-hint-p acc))))
          (make-trusted-hint))
         ((if (equal (typed-term->kind tterm) 'variablep)) acc)
         ((if (equal (typed-term->kind tterm) 'quotep)) acc)
         ((if (equal (typed-term->kind tterm) 'ifp))
          (if-hint-generation tterm hint-options acc state))
         ((if (equal (typed-term->kind tterm) 'fncallp))
          (fncall-hint-generation tterm hint-options acc state)))
      (prog2$ (er hard? 'hint-generation=>hint-generation
                  "Found lambda term in goal.~%")
              acc)))

  (define hint-generation-list ((tterm-lst typed-term-list-p)
                                (hint-options hint-options-p)
                                (acc trusted-hint-p)
                                state)
    :guard (good-typed-term-list-p tterm-lst)
    :returns (trusted-hint trusted-hint-p)
    :measure (list (acl2-count (typed-term-list->term-lst tterm-lst)) 1)
    (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                            (good-typed-term-list-p tterm-lst)
                            (hint-options-p hint-options)
                            (trusted-hint-p acc))))
          (make-trusted-hint))
         ((unless (consp tterm-lst)) acc)
         ((cons tterm-hd tterm-tl) tterm-lst)
         (acc-car (hint-generation tterm-hd hint-options acc state)))
      (hint-generation-list tterm-tl hint-options acc-car state)))
  )

(verify-guards hint-generation)

(define add-user-fns ((func-alst symbol-smt-function-alist-p))
  :returns (user-fns symbol-smt-function-alist-p)
  :measure (len (symbol-smt-function-alist-fix func-alst))
  (b* ((func-alst (symbol-smt-function-alist-fix func-alst))
       ((unless (consp func-alst)) nil)
       ((cons func-hd func-tl) func-alst)
       ((cons name func) func-hd)
       ((smt-function f) func)
       ((unless (or (equal f.kind :basic) (equal f.kind :type)))
        (add-user-fns func-tl)))
    (acons name f (add-user-fns func-tl))))

(define generate-trusted-hint ((options hint-options-p))
  :returns (th trusted-hint-p)
  (b* ((options (hint-options-fix options))
       ((hint-options h) options)
       (th1 (make-trusted-hint))
       (th2 (change-trusted-hint th1 :user-types h.datatype))
       (user-fns (add-user-fns h.function)))
    (change-trusted-hint th2 :user-fns user-fns)))

(define hint-generation-cp ((cl pseudo-term-listp)
                            (hints t)
                            state)
  (b* ((cl (pseudo-term-list-fix cl))
       ((unless (smtlink-hint-p hints)) (value (list cl)))
       (goal (disjoin cl))
       ((mv okp judges tterm)
        (case-match goal
          (('implies judges term)
           (mv t judges (make-typed-term :term term
                                         :path-cond ''t
                                         :judgements judges)))
          (& (mv nil ''t (make-typed-term)))))
       ((unless okp)
        (prog2$ (er hard? 'hint-generation=>hint-generation-cp
                    "The input term is of wrong shape.~%")
                (value (list cl))))
       ((unless (good-typed-term-p tterm))
        (prog2$ (er hard? 'hint-generation=>hint-generation-cp
                    "Not a good-typed-term-p: ~q0" tterm)
                (value (list cl))))
       (next-cp (cdr (assoc-equal 'hint-generation *SMT-architecture*)))
       ((if (null next-cp)) (value (list cl)))
       (options (construct-hint-options hints))
       (th (generate-trusted-hint options))
       (trusted-hint (hint-generation tterm options th state))
       (new-hint (change-smtlink-hint hints :trusted-hint trusted-hint))
       (the-hint `(:clause-processor (,next-cp clause ',new-hint))))
    (value (list `((hint-please ',the-hint) ,goal)))))

(defthm correctness-of-hint-generation-cp
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (hint-generation-cp cl hint state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :hints (("Goal"
           :in-theory (enable hint-generation-cp hint-generation)))
  :rule-classes :clause-processor)
