;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
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
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "basics")
(include-book "hint-please")
(include-book "empty-typed-term")
(include-book "typed-term-fns")
(include-book "judgement-fns")
(include-book "returns-judgement")
(include-book "../utils/fresh-vars")

(set-state-ok t)

(local (in-theory (disable (:executable-counterpart typed-term)
                           pseudo-termp pseudo-term-listp)))

;;-------------------------------------------------------
;; quoted judgements
;; nil judgements

(defthm ev-smtcp-of-fncall-with-nil
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (alistp a)
                (symbolp fn)
                (acl2::logicp fn (w state)))
           (equal (ev-smtcp (cons fn '('nil)) nil)
                  (ev-smtcp (cons fn '('nil)) a)))
  :hints (("Goal"
           :in-theory (disable ev-smtcp-of-fncall-args)
           :use ((:instance ev-smtcp-of-fncall-args
                            (x (cons fn '('nil)))
                            (a a))))))

(define type-judgement-nil-test ((supertype type-to-types-alist-p)
                                 (acc pseudo-termp)
                                 state)
  :returns (judgements pseudo-termp)
  :measure (len (type-to-types-alist-fix supertype))
  (b* ((supertype (type-to-types-alist-fix supertype))
       (acc (pseudo-term-fix acc))
       ((unless (consp supertype)) acc)
       ((cons (cons first-type &) rest) supertype)
       ((unless (acl2::logicp first-type (w state)))
        (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-nil-test
                    "~p0 is a program-mode function: ~q0" first-type)
                acc))
       (term `(,first-type 'nil))
       ((mv erp val) (magic-ev-fncall first-type '(nil) state t nil))
       ((if erp) (type-judgement-nil-test rest acc state))
       ((if val) (type-judgement-nil-test rest `(if ,term ,acc 'nil) state)))
    (type-judgement-nil-test rest acc state))
  ///
  (defthm correctness-of-type-judgement-nil-test
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (alistp a)
                  (pseudo-termp acc)
                  (type-to-types-alist-p supertype)
                  (ev-smtcp acc a))
             (ev-smtcp (type-judgement-nil-test supertype acc state)
                       a))))

(define type-judgement-nil ((supertype type-to-types-alist-p) state)
  :returns (judgements pseudo-termp)
  (type-judgement-nil-test supertype ''t state)
  ///
  (defthm correctness-of-type-judgement-nil
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (alistp a)
                  (type-to-types-alist-p supertype))
             (ev-smtcp (type-judgement-nil supertype state)
                       a))))

(define type-judgement-t ()
  :returns (judgements pseudo-termp)
  `(if (symbolp 't)
       (if (booleanp 't) 't 'nil)
     'nil))

(define type-judgement-quoted-helper ((term pseudo-termp)
                                      (options type-options-p)
                                      state)
  :guard (and (not (acl2::variablep term))
              (acl2::fquotep term))
  :guard-hints (("Goal"
                 :in-theory (enable pseudo-termp pseudo-term-listp)))
  :returns (judgements pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (options (type-options-fix options))
       ((unless (mbt (acl2::fquotep term))) ''t)
       (const (cadr term)))
    (cond ((integerp const)
           (extend-judgements `(if (integerp ',const) 't 'nil) ''t options state))
          ((rationalp const)
           (extend-judgements `(if (rationalp ',const) 't 'nil) ''t options state))
          ((equal const t)
           (extend-judgements (type-judgement-t) ''t options state))
          ((null const)
           (type-judgement-nil (type-options->supertype options) state))
          ((symbolp const)
           (extend-judgements `(if (symbolp ',const) 't 'nil) ''t options state))
          (t (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-quoted-helper
                         "Type inference for constant term ~p0 is not supported.~%"
                         term)
                     ''t))))
  ///
  (defthm correctness-of-type-judgement-quoted-helper
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (alistp a))
             (ev-smtcp (type-judgement-quoted-helper term options state) a))
    :hints (("Goal"
             :in-theory (e/d (pseudo-termp pseudo-term-listp)
                             (correctness-of-path-test-list-corollary
                              consp-of-is-conjunct?
                              acl2::symbol-listp-when-not-consp
                              correctness-of-path-test-list
                              ev-smtcp-of-variable))))))

(define type-judgement-quoted ((tterm typed-term-p)
                               (options type-options-p)
                               state)
  :guard (and (good-typed-term-p tterm)
              (equal (typed-term->kind tterm) 'quotep))
  :returns (new-tt good-typed-term-p
                   :hints (("Goal"
                            :in-theory (enable good-typed-quote-p))))
  :guard-hints (("Goal" :in-theory (enable typed-term->kind)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (equal (typed-term->kind tterm) 'quotep)
                          (good-typed-term-p tterm)
                          (type-options-p options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       (new-judgements (type-judgement-quoted-helper tt.term options state)))
    (change-typed-term tterm :judgements new-judgements))
  ///
  (more-returns
   (new-tt (implies (and (type-options-p options)
                         (equal (typed-term->kind tterm) 'quotep)
                         (good-typed-term-p tterm))
                    (equal (typed-term->path-cond new-tt)
                           (typed-term->path-cond tterm)))
           :name type-judgement-quoted-maintains-path-cond))
  (defthm correctness-of-type-judgement-quoted
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (good-typed-term-p tterm)
                  (equal (typed-term->kind tterm) 'quotep)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (type-judgement-quoted tterm options state))
                       a))
    :hints (("Goal"
             :in-theory (enable correct-typed-term))))
  (defthm type-judgement-quoted-maintains-term
    (implies (and (type-options-p options)
                  (equal (typed-term->kind tterm) 'quotep)
                  (good-typed-term-p tterm))
             (equal (typed-term->term
                     (type-judgement-quoted tterm options state))
                    (typed-term->term tterm)))))

;; ------------------------------------------------------------------
;;    Variable judgements

(define type-judgement-variable-helper ((term pseudo-termp)
                                        (path-cond pseudo-termp)
                                        (options type-options-p)
                                        state)
  :returns (judgements pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (path-cond (pseudo-term-fix path-cond))
       (options (type-options-fix options))
       (supertype (type-options->supertype options))
       (judge-from-path-cond (look-up-path-cond term path-cond supertype)))
    (extend-judgements judge-from-path-cond path-cond options state))
  ///
  (defthm correctness-of-type-judgement-variable-helper
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (pseudo-termp path-cond)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (type-judgement-variable-helper
                        term path-cond options state)
                       a))))

(define type-judgement-variable ((tterm typed-term-p)
                                 (options type-options-p)
                                 state)
  :guard (and (good-typed-term-p tterm)
              (equal (typed-term->kind tterm) 'variablep))
  :returns (new-tt good-typed-term-p
                   :hints (("Goal"
                            :in-theory (enable good-typed-variable-p))))
  (b* (((unless (mbt (and (equal (typed-term->kind tterm) 'variablep)
                          (good-typed-term-p tterm)
                          (type-options-p options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       (new-judgements
        (type-judgement-variable-helper tt.term tt.path-cond options state)))
    (change-typed-term tterm :judgements new-judgements))
  ///
  (more-returns
   (new-tt (implies (and (type-options-p options)
                         (equal (typed-term->kind tterm) 'variablep)
                         (good-typed-term-p tterm))
                    (equal (typed-term->path-cond new-tt)
                           (typed-term->path-cond tterm)))
           :name type-judgement-variable-maintains-path-cond))
  (defthm correctness-of-type-judgement-variable
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (good-typed-term-p tterm)
                  (equal (typed-term->kind tterm) 'variablep)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (type-judgement-variable tterm options state))
                       a))
    :hints (("Goal"
             :in-theory (enable correct-typed-term))))
  (defthm type-judgement-variable-maintains-term
    (implies (and (type-options-p options)
                  (equal (typed-term->kind tterm) 'variablep)
                  (good-typed-term-p tterm))
             (equal (typed-term->term
                     (type-judgement-variable tterm options state))
                    (typed-term->term tterm)))))

;; ------------------------------------------------------------------
;;    The main type-judgements

(define type-judgement-if-top ((judge-then pseudo-termp)
                               (then pseudo-termp)
                               (judge-else pseudo-termp)
                               (else pseudo-termp)
                               (cond pseudo-termp)
                               (names symbol-listp)
                               (options type-options-p))
  :returns (judge-if-top pseudo-termp)
  (b* ((judge-then (pseudo-term-fix judge-then))
       (then (pseudo-term-fix then))
       (judge-else (pseudo-term-fix judge-else))
       (else (pseudo-term-fix else))
       (names (symbol-list-fix names))
       (options (type-options-fix options))
       (supertype-alst (type-options->supertype options))
       (new-var (new-fresh-var names))
       ((mv fast-else &)
        (make-fast-judgements judge-else else new-var
                              supertype-alst nil 0))
       (ind-lst
        (map-judgements judge-then then new-var supertype-alst fast-else))
       ((mv judge-then-common &)
        (construct-judge-by-list judge-then then
                                 supertype-alst ind-lst ''t))
       (judge-else-common
        (construct-judge-by-find judge-else else supertype-alst ind-lst ''t))
       (judge `(if ,cond ,judge-then-common ,judge-else-common)))
    (merge-if-judgements (rearrange-if-judgements judge) then else supertype-alst)))

(defthm correctness-of-type-judgement-if-top
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judge-then)
                (pseudo-termp then)
                (pseudo-termp judge-else)
                (pseudo-termp else)
                (pseudo-termp cond)
                (alistp a)
                (ev-smtcp `(if ,cond ,judge-then ,judge-else) a))
           (ev-smtcp (type-judgement-if-top judge-then then judge-else else
                                            cond names options)
                     a))
  :hints (("Goal"
           :in-theory (e/d (type-judgement-if-top)
                           (CORRECTNESS-OF-PATH-TEST-LIST-COROLLARY
                            correctness-of-path-test-list
                            correctness-of-path-test
                            consp-of-pseudo-lambdap
                            symbol-listp
                            EV-SMTCP-OF-VARIABLE)))))

(define augment-path-cond ((cond pseudo-termp)
                           (judge-cond pseudo-termp)
                           (path-cond pseudo-termp)
                           (supertype-alst type-to-types-alist-p))
  :returns (mv (then-pc pseudo-termp)
               (else-pc pseudo-termp))
  (b* ((cond (pseudo-term-fix cond))
       (judge-cond (pseudo-term-fix judge-cond))
       (path-cond (pseudo-term-fix path-cond))
       ((mv okp1 var1 term1)
        (case-match cond
          (('equal lhs rhs) (mv (symbolp lhs) lhs rhs))
          (& (mv nil nil nil))))
       ((mv okp2 var2 term2)
        (case-match cond
          (('not ('equal lhs rhs)) (mv (symbolp lhs) lhs rhs))
          (& (mv nil nil nil))))
       ((unless (or okp1 okp2))
        (mv (conjoin `(,(simple-transformer cond) ,path-cond))
            (conjoin `(,(simple-transformer `(not ,cond)) ,path-cond))))
       ((if okp1)
        (mv (conjoin `(,(generate-judge-from-equality var1 term1 judge-cond
                                                      supertype-alst)
                       ,(simple-transformer cond) ,path-cond))
            (conjoin `(,(simple-transformer `(not ,cond)) ,path-cond)))))
    (mv (conjoin `(,(simple-transformer cond) ,path-cond))
        (conjoin `(,(generate-judge-from-equality var2 term2 judge-cond
                                                  supertype-alst)
                   ,(simple-transformer `(not ,cond)) ,path-cond)))))

(defthm correctness-of-augment-path-cond-1
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp cond)
                (pseudo-termp judge-cond)
                (pseudo-termp path-cond)
                (alistp a)
                (ev-smtcp judge-cond a))
           (b* (((mv then-pc &)
                 (augment-path-cond cond judge-cond path-cond supertype-alst)))
             (iff (ev-smtcp then-pc a)
                  (ev-smtcp `(if ,cond ,path-cond 'nil) a))))
  :hints (("Goal"
           :in-theory (e/d (augment-path-cond simple-transformer)
                           (pseudo-termp
                            correctness-of-path-test-list-corollary
                            correctness-of-path-test-list
                            correctness-of-path-test
                            symbol-listp
                            acl2::symbol-listp-when-not-consp
                            ev-smtcp-of-variable
                            consp-of-is-conjunct?
                            acl2::pseudo-termp-opener)))))

(defthm correctness-of-augment-path-cond-2
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp cond)
                (pseudo-termp judge-cond)
                (pseudo-termp path-cond)
                (alistp a)
                (ev-smtcp judge-cond a))
           (b* (((mv & else-pc)
                 (augment-path-cond cond judge-cond path-cond supertype-alst)))
             (iff (ev-smtcp else-pc a)
                  (ev-smtcp `(if (not ,cond) ,path-cond 'nil) a))))
  :hints (("Goal"
           :in-theory (e/d (augment-path-cond simple-transformer)
                           (pseudo-termp
                            correctness-of-path-test-list-corollary
                            correctness-of-path-test-list
                            correctness-of-path-test
                            symbol-listp
                            acl2::symbol-listp-when-not-consp
                            ev-smtcp-of-variable
                            consp-of-is-conjunct?
                            acl2::pseudo-termp-opener
                            consp-of-pseudo-lambdap
                            ev-smtcp-of-booleanp-call
                            alistp
                            implies-of-is-conjunct?
                            implies-of-type-predicate-of-term)))))

(defines type-judgements
  :flag-local nil
  :well-founded-relation l<
  :verify-guards nil

  (define type-judgement-if ((tterm typed-term-p)
                             (options type-options-p)
                             (names symbol-listp)
                             state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'ifp))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    :returns (new-tt good-typed-term-p)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (equal (typed-term->kind tterm) 'ifp)
                            (good-typed-term-p tterm)
                            (symbol-listp names))))
          (make-typed-term))
         ((type-options o) options)
         ((typed-term tt) tterm)
         ((typed-term tt-cond) (typed-term-if->cond tt))
         ((typed-term tt-then) (typed-term-if->then tt))
         ((typed-term tt-else) (typed-term-if->else tt))
         ((typed-term tt-top) (typed-term->top tt))
         (new-cond (type-judgement tt-cond options names state))
         (new-then (type-judgement tt-then options names state))
         (new-else (type-judgement tt-else options names state))
         (judge-then-top (type-judgement-top tt-then.judgements tt-then.term options))
         (judge-else-top (type-judgement-top tt-else.judgements tt-else.term options))
         (judge-if-top
          (type-judgement-if-top judge-then-top tt-then.term judge-else-top
                                 tt-else.term tt-cond.term names options))
         (judge-if-top-extended
          (extend-judgements judge-if-top tt-top.path-cond options state))
         (new-top (change-typed-term tt-top :judgements judge-if-top-extended)))
      (make-typed-if new-top new-cond new-then new-else)))

  (define type-judgement-fn ((tterm typed-term-p)
                             (options type-options-p)
                             (names symbol-listp)
                             state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'fncallp))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    :returns (new-tt good-typed-term-p)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (equal (typed-term->kind tterm) 'fncallp)
                            (good-typed-term-p tterm)
                            (symbol-listp names))))
          (make-typed-term))
         ((type-options to) options)
         ((typed-term tt) tterm)
         (tt-actuals (typed-term-fncall->actuals tt))
         ((typed-term ttt) (typed-term->top tt))
         ((cons fn actuals) tt.term)
         (new-actuals (type-judgement-list tt-actuals options names state))
         (new-tta.judgements (typed-term-list->judgements new-actuals))
         (actuals-judgements-top
          (type-judgement-top-list new-tta.judgements actuals options))
         (functions (type-options->functions options))
         (conspair (assoc-equal fn functions))
         ((unless conspair)
          (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-fn
                      "There exists no function description for function ~p0. ~
                       ~%" fn)
                  tt))
         (fn-description (cdr conspair))
         (return-judgement
          (returns-judgement fn actuals actuals-judgements-top fn-description
                             ttt.path-cond ''t state))
         ((if (equal return-judgement ''t))
          (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-fn
                      "Failed to find type judgements for return of function ~
                       call ~p0~%Current path-cond: ~p1~%Actuals-judgements: ~
                       ~p2~%"
                      tt.term ttt.path-cond actuals-judgements-top)
                  tt))
         (return-judgement-extended
          (extend-judgements return-judgement ttt.path-cond options state))
         (new-top (change-typed-term ttt :judgements return-judgement-extended))
         ((unless (make-typed-fncall-guard new-top new-actuals)) tt))
      (make-typed-fncall new-top new-actuals)))

  (define type-judgement ((tterm typed-term-p)
                          (options type-options-p)
                          (names symbol-listp)
                          state)
    :guard (good-typed-term-p tterm)
    :measure (list (acl2-count (typed-term->term tterm)) 1)
    :returns (new-tt good-typed-term-p)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (symbol-listp names)
                            (good-typed-term-p tterm))))
          (make-typed-term))
         ((if (equal (typed-term->kind tterm) 'variablep))
          (type-judgement-variable tterm options state))
         ((if (equal (typed-term->kind tterm) 'quotep))
          (type-judgement-quoted tterm options state))
         ((if (equal (typed-term->kind tterm) 'ifp))
          (type-judgement-if tterm options names state))
         ((unless (typed-term->kind tterm))
          (prog2$ (er hard? 'type-inference-bottomup=>type-judgement
                      "Found lambda term in goal.~%")
                  tterm)))
      (type-judgement-fn tterm options names state)))

  (define type-judgement-list ((tterm-lst typed-term-list-p)
                               (options type-options-p)
                               (names symbol-listp)
                               state)
    :returns (new-ttl good-typed-term-list-p)
    :guard (good-typed-term-list-p tterm-lst)
    :measure (list (acl2-count (typed-term-list->term-lst tterm-lst))
                   1)
    (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                            (type-options-p options)
                            (good-typed-term-list-p tterm-lst)
                            (symbol-listp names))))
          nil)
         ((unless (consp tterm-lst)) nil)
         ((cons tterm-hd tterm-tl) tterm-lst)
         (tt-car (type-judgement tterm-hd options names state))
         (tt-cdr (type-judgement-list tterm-tl options names state))
         ((unless (implies (consp tt-cdr)
                           (equal (typed-term->path-cond tt-car)
                                  (typed-term-list->path-cond tt-cdr))))
          tterm-lst))
      (cons tt-car tt-cdr)))
  ///
  (defthm typed-term-of-type-judgement-fn
    (typed-term-p (type-judgement-fn tterm options names state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (type-judgement-fn tterm options names state)))))))
  (defthm typed-term-of-type-judgement-if
    (typed-term-p (type-judgement-if tterm options names state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (type-judgement-if tterm options names state)))))))
  (defthm typed-term-of-type-judgement
    (typed-term-p (type-judgement tterm options names state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (type-judgement tterm options names state)))))))
  (defthm typed-term-list-of-type-judgement-list
    (typed-term-list-p
     (type-judgement-list tterm-lst options names state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-list-implies-typed-term-list)
             :use ((:instance good-typed-term-list-implies-typed-term-list
                              (tterm-lst
                               (type-judgement-list tterm-lst options names
                                                    state)))))))
  )

(defthm-type-judgements-flag
  (defthm type-judgement-if-maintains-path-cond
    (implies (and (type-options-p options)
                  (equal (typed-term->kind tterm) 'ifp)
                  (good-typed-term-p tterm)
                  (symbol-listp names))
             (equal (typed-term->path-cond
                     (type-judgement-if tterm options names state))
                    (typed-term->path-cond tterm)))
    :flag type-judgement-if
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp
                                    symbol-listp
                                    acl2::symbol-listp-when-not-consp
                                    consp-of-is-conjunct?
                                    acl2::pseudo-termp-cadr-from-pseudo-term-listp
                                    acl2::symbolp-of-car-when-symbol-listp
                                    pseudo-term-listp-of-symbol-listp
                                    acl2::pseudo-termp-opener))
                              :expand (type-judgement-if tterm options names state)))))
  (defthm type-judgement-fn-maintains-path-cond
    (implies (and (type-options-p options)
                  (equal (typed-term->kind tterm) 'fncallp)
                  (good-typed-term-p tterm)
                  (symbol-listp names))
             (equal (typed-term->path-cond
                     (type-judgement-fn tterm options names state))
                    (typed-term->path-cond tterm)))
    :flag type-judgement-fn
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp
                                    symbol-listp
                                    acl2::symbol-listp-when-not-consp
                                    consp-of-is-conjunct?
                                    acl2::pseudo-termp-cadr-from-pseudo-term-listp
                                    acl2::symbolp-of-car-when-symbol-listp
                                    pseudo-term-listp-of-symbol-listp
                                    acl2::pseudo-termp-opener))
                   :expand (type-judgement-fn tterm options names state)))))
  (defthm type-judgement-maintains-path-cond
    (implies (and (type-options-p options)
                  (good-typed-term-p tterm)
                  (symbol-listp names))
             (equal (typed-term->path-cond
                     (type-judgement tterm options names state))
                    (typed-term->path-cond tterm)))
    :flag type-judgement
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () ())
                   :expand (type-judgement tterm options names state)))))
  (defthm type-judgement-list-maintains-path-cond
    (implies (and (type-options-p options)
                  (good-typed-term-list-p tterm-lst)
                  (symbol-listp names))
             (equal (typed-term-list->path-cond
                     (type-judgement-list tterm-lst options names state))
                    (typed-term-list->path-cond tterm-lst)))
    :flag type-judgement-list
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (typed-term-list->path-cond)
                                   (pseudo-termp
                                    acl2::symbol-listp-when-not-consp
                                    consp-of-is-conjunct?
                                    acl2::pseudo-termp-cadr-from-pseudo-term-listp
                                    acl2::symbolp-of-car-when-symbol-listp
                                    pseudo-term-listp-of-symbol-listp
                                    acl2::pseudo-termp-opener
                                    pseudo-term-listp-of-symbol-listp))
                   :expand
                   ((type-judgement-list tterm-lst options names state)
                    (type-judgement-list nil options names state)
                    (type-judgement-list tterm-lst options names state)
                    (type-judgement-list nil options names state))))))
  :hints(("Goal"
          :in-theory (disable pseudo-termp
                              correctness-of-path-test-list
                              symbol-listp
                              correctness-of-path-test
                              acl2::symbol-listp-when-not-consp
                              consp-of-is-conjunct?
                              acl2::pseudo-termp-cadr-from-pseudo-term-listp
                              acl2::symbolp-of-car-when-symbol-listp
                              pseudo-term-listp-of-symbol-listp
                              acl2::pseudo-termp-opener))))

(defthm-type-judgements-flag
  (defthm type-judgement-if-maintains-term
    (implies (and (type-options-p options)
                  (equal (typed-term->kind tterm) 'ifp)
                  (good-typed-term-p tterm)
                  (symbol-listp names))
             (equal (typed-term->term
                     (type-judgement-if tterm options names state))
                    (typed-term->term tterm)))
    :flag type-judgement-if
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (make-typed-if) ())
                              :expand (type-judgement-if tterm options names state)))))
  (defthm type-judgement-fn-maintains-term
    (implies (and (type-options-p options)
                  (equal (typed-term->kind tterm) 'fncallp)
                  (good-typed-term-p tterm)
                  (symbol-listp names))
             (equal (typed-term->term
                     (type-judgement-fn tterm options names state))
                    (typed-term->term tterm)))
    :flag type-judgement-fn
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () ())
                   :expand (type-judgement-fn tterm options names state)))))
  (defthm type-judgement-maintains-term
    (implies (and (type-options-p options)
                  (good-typed-term-p tterm)
                  (symbol-listp names))
             (equal (typed-term->term
                     (type-judgement tterm options names state))
                    (typed-term->term tterm)))
    :flag type-judgement
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () ())
                   :expand (type-judgement tterm options names state)))))
  (defthm type-judgement-list-maintains-term-lst
    (implies (and (type-options-p options)
                  (good-typed-term-list-p tterm-lst)
                  (symbol-listp names))
             (equal (typed-term-list->term-lst
                     (type-judgement-list tterm-lst options names state))
                    (typed-term-list->term-lst tterm-lst)))
    :flag type-judgement-list
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (typed-term-list->term-lst) ())
                   :expand
                   ((type-judgement-list tterm-lst options names state)
                    (type-judgement-list nil options names state)
                    (type-judgement-list tterm-lst options names state)
                    (type-judgement-list nil options names state)))))))

(verify-guards type-judgement
  :hints (("Goal"
           :in-theory (enable make-typed-fncall-guard
                              typed-term-list->path-cond
                              typed-term-fncall->actuals
                              typed-term-list->term-lst))))

;; ------------------------------------------------
;; Correctness theorems for type-judgement
stop

(skip-proofs
 (defthm crock1
   (implies (and (ev-smtcp (correct-typed-term-list
                            (type-judgement-list
                             (typed-term-fncall->actuals tterm)
                             options names state))
                           a)
                 (ev-smtcp (typed-term->path-cond tterm) a))
            (ev-smtcp (type-judgement-top-list
                       (typed-term-list->judgements
                        (type-judgement-list (typed-term-fncall->actuals tterm)
                                             options names state))
                       (cdr (typed-term->term tterm))
                       options)
                      a)))
 )

(skip-proofs
(defthm crock2
  (implies (and (typed-term-p tterm)
                (type-options-p options))
           (THM-SPEC-LIST-P (CDR (ASSOC-EQUAL (CAR (TYPED-TERM->TERM TTERM))
                                              (TYPE-OPTIONS->FUNCTIONS
                                               OPTIONS))))))
)

(skip-proofs
(defthm crock3
  (IMPLIES (AND (ev-smtcp-meta-extract-global-facts)
                (GOOD-TYPED-FNCALL-P TTERM)
                (ALISTP A)
                (EV-SMTCP (TYPED-TERM->SMT-JUDGEMENTS TTERM)
                          A))
           (EV-SMTCP (TYPED-TERM->SMT-JUDGEMENTS (TYPED-TERM->TOP TTERM))
                     A)))
)

(defthm correctness-of-type-judgement-lemma1
   (implies (and (ev-smtcp-meta-extract-global-facts)
                 (good-typed-fncall-p tterm)
                 (type-options-p options)
                 (alistp a)
                 (ev-smtcp (correct-typed-term tterm) a)
                 (ev-smtcp (correct-typed-term-list
                            (type-judgement-list
                             (typed-term-fncall->actuals tterm)
                             options names state))
                           a))
            (ev-smtcp (correct-typed-term
                       (typed-term
                        (typed-term->term tterm)
                        (typed-term->path-cond tterm)
                        (extend-judgements
                         (returns-judgement
                          (car (typed-term->term tterm))
                          (cdr (typed-term->term tterm))
                          (type-judgement-top-list
                           (typed-term-list->judgements
                            (type-judgement-list (typed-term-fncall->actuals tterm)
                                                 options names state))
                           (cdr (typed-term->term tterm))
                           options)
                          (cdr (assoc-equal (car (typed-term->term tterm))
                                            (type-options->functions options)))
                          (typed-term->path-cond tterm)
                          ''t
                          state)
                         (typed-term->path-cond tterm)
                         options state)
                        (typed-term->smt-judgements (typed-term->top tterm))))
                      a))
   :hints (("goal"
            :in-theory (e/d (correct-typed-term)
                            (correctness-of-returns-judgement))
            :use ((:instance correctness-of-returns-judgement
                             (fn (car (typed-term->term tterm)))
                             (actuals (cdr (typed-term->term tterm)))
                             (actuals-judgements (type-judgement-top-list
                                                  (typed-term-list->judgements
                                                   (type-judgement-list (typed-term-fncall->actuals tterm)
                                                                        options names state))
                                                  (cdr (typed-term->term tterm))
                                                  options))
                             (respec-lst (cdr (assoc-equal (car (typed-term->term tterm))
                                                           (type-options->functions options))))
                             (path-cond (typed-term->path-cond tterm))
                             (acc ''t)
                             (state state)
                             (a a)))))
   )

(skip-proofs
(defthm crock4
  (implies (EV-SMTCP (TYPED-TERM->PATH-COND TTERM)
                     A)
           (EV-SMTCP
            (TYPED-TERM->PATH-COND (TYPE-JUDGEMENT (TYPED-TERM-IF->COND TTERM)
                                                   OPTIONS NAMES STATE))
            A)))
)

(skip-proofs
(defthm crock5
  (implies (and (EV-SMTCP (TYPED-TERM->PATH-COND TTERM)
                          A)
                (EV-SMTCP (CADR (TYPED-TERM->TERM TTERM))
                          A))
           (EV-SMTCP
            (TYPED-TERM->PATH-COND (TYPE-JUDGEMENT (TYPED-TERM-IF->then TTERM)
                                                   OPTIONS NAMES STATE))
            A)))
)

(skip-proofs
(defthm crock6
  (implies (and (EV-SMTCP (TYPED-TERM->PATH-COND TTERM)
                          A)
                (not (EV-SMTCP (CADR (TYPED-TERM->TERM TTERM))
                          A)))
           (EV-SMTCP
            (TYPED-TERM->PATH-COND (TYPE-JUDGEMENT (TYPED-TERM-IF->else TTERM)
                                                   OPTIONS NAMES STATE))
            A)))
)

(skip-proofs
 (defthm crock7
   (IMPLIES (AND (ev-smtcp-meta-extract-global-facts)
                 (GOOD-TYPED-if-P TTERM)
                 (ALISTP A)
                 (EV-SMTCP (TYPED-TERM->SMT-JUDGEMENTS TTERM)
                           A))
            (EV-SMTCP (TYPED-TERM->SMT-JUDGEMENTS (TYPED-TERM->TOP TTERM))
                      A)))
 )

(skip-proofs
 (defthm crock8
   (IMPLIES (AND (ev-smtcp-meta-extract-global-facts)
                 (GOOD-TYPED-if-P TTERM)
                 (ALISTP A)
                 (EV-SMTCP
                  (TYPED-TERM->SMT-JUDGEMENTS (TYPE-JUDGEMENT (TYPED-TERM-IF->THEN TTERM)
                                                              OPTIONS NAMES STATE))
                  A))
            (EV-SMTCP
             (TYPE-JUDGEMENT-TOP (TYPED-TERM->JUDGEMENTS (TYPED-TERM-IF->THEN TTERM))
                                 (CADDR (TYPED-TERM->TERM TTERM))
                                 OPTIONS)
             A)))
 )

(skip-proofs
 (defthm crock9
   (IMPLIES (AND (ev-smtcp-meta-extract-global-facts)
                 (GOOD-TYPED-if-P TTERM)
                 (ALISTP A)
                 (EV-SMTCP
                  (TYPED-TERM->JUDGEMENTS (TYPE-JUDGEMENT (TYPED-TERM-IF->ELSE TTERM)
                                                          OPTIONS NAMES STATE))
                  A))
            (EV-SMTCP
             (TYPE-JUDGEMENT-TOP (TYPED-TERM->JUDGEMENTS (TYPED-TERM-IF->ELSE TTERM))
                                 (CADDDR (TYPED-TERM->TERM TTERM))
                                 OPTIONS)
             A)))
 )

(defthm correctness-of-type-judgement-lemma2
   (implies (and (ev-smtcp-meta-extract-global-facts)
                 (good-typed-if-p tterm)
                 (alistp a)
                 (ev-smtcp (correct-typed-term tterm) a)
                 (ev-smtcp (correct-typed-term
                            (type-judgement
                             (typed-term-if->cond tterm)
                             options names state))
                           a)
                 (ev-smtcp (correct-typed-term
                            (type-judgement
                             (typed-term-if->then tterm)
                             options names state))
                           a)
                 (ev-smtcp (correct-typed-term
                            (type-judgement
                             (typed-term-if->else tterm)
                             options names state))
                           a))
            (ev-smtcp (correct-typed-term
                       (typed-term
                       (typed-term->term tterm)
                       (typed-term->path-cond tterm)
                       (extend-judgements
                        (type-judgement-if-top
                         (type-judgement-top
                          (typed-term->judgements (typed-term-if->then tterm))
                          (caddr (typed-term->term tterm))
                          options)
                         (caddr (typed-term->term tterm))
                         (type-judgement-top
                          (typed-term->judgements (typed-term-if->else tterm))
                          (cadddr (typed-term->term tterm))
                          options)
                         (cadddr (typed-term->term tterm))
                         (cadr (typed-term->term tterm))
                         names options)
                        (typed-term->path-cond tterm)
                        options state)
                       (typed-term->smt-judgements (typed-term->top tterm))))
                      a))
   :hints (("goal"
            :in-theory (e/d (correct-typed-term)
                            (CORRECTNESS-OF-PATH-TEST-LIST-COROLLARY
                             CORRECTNESS-OF-PATH-TEST-LIST
                             ACL2::PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP
                             SYMBOL-LISTP
                             CORRECTNESS-OF-PATH-TEST
                             ACL2::SYMBOL-LISTP-WHEN-NOT-CONSP
                             PSEUDO-TERM-LISTP-OF-SYMBOL-LISTP
                             CONSP-OF-IS-CONJUNCT?
                             correctness-of-type-judgement-if-top))
            :use ((:instance correctness-of-type-judgement-if-top
                             (judge-then (TYPE-JUDGEMENT-TOP (TYPED-TERM->JUDGEMENTS (TYPED-TERM-IF->THEN TTERM))
                                                             (CADDR (TYPED-TERM->TERM TTERM))
                                                             OPTIONS))
                             (then (CADDR (TYPED-TERM->TERM TTERM)))
                             (judge-else (TYPE-JUDGEMENT-TOP (TYPED-TERM->JUDGEMENTS (TYPED-TERM-IF->ELSE TTERM))
                                                             (CADDDR (TYPED-TERM->TERM TTERM))
                                                             OPTIONS))
                             (else (CADDDR (TYPED-TERM->TERM TTERM)))
                             (cond (CADR (TYPED-TERM->TERM TTERM)))
                             (names names)
                             (options options)
                             (a a))))))

(encapsulate ()
  (local (in-theory (e/d ()
                         (pseudo-termp
                          correctness-of-path-test-list
                          correctness-of-path-test-list-corollary
                          symbol-listp
                          correctness-of-path-test
                          acl2::symbol-listp-when-not-consp
                          consp-of-is-conjunct?
                          acl2::pseudo-termp-cadr-from-pseudo-term-listp
                          acl2::symbolp-of-car-when-symbol-listp
                          pseudo-term-listp-of-symbol-listp
                          acl2::pseudo-termp-opener
                          ev-smtcp-of-booleanp-call
                          type-judgement-t
                          pseudo-term-listp-of-cdr-of-pseudo-termp
                          acl2::pseudo-lambdap-of-car-when-pseudo-lambda-listp
                          default-cdr
                          default-car
                          implies-of-type-predicate-of-term
                          ev-smtcp-of-lambda))))

(defthm-type-judgements-flag
  (defthm correctness-of-type-judgement-if
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (typed-term-p tterm)
                  (equal (typed-term->kind tterm) 'ifp)
                  (good-typed-term-p tterm)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (type-judgement-if tterm options names state))
                       a))
    :flag type-judgement-if
    :hints ((and stable-under-simplificationp
                 '(:expand (type-judgement-if tterm options names state)))))
  (defthm correctness-of-type-judgement-fn
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (typed-term-p tterm)
                  (equal (typed-term->kind tterm) 'fncallp)
                  (good-typed-term-p tterm)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (type-judgement-fn tterm options names state))
                       a))
    :hints ((and stable-under-simplificationp
                 '(:expand (type-judgement-fn tterm options names state))))
    :flag type-judgement-fn)
  (defthm correctness-of-type-judgement
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (typed-term-p tterm)
                  (good-typed-term-p tterm)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (type-judgement tterm options names state))
                       a))
    :flag type-judgement
    :hints ((and stable-under-simplificationp
                 '(:expand (type-judgement tterm options names state)))))
  (defthm correctness-of-type-judgement-list
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (good-typed-term-list-p tterm-lst)
                  (alistp a)
                  (ev-smtcp (correct-typed-term-list tterm-lst) a))
             (ev-smtcp
              (correct-typed-term-list
               (type-judgement-list tterm-lst options names state))
              a))
    :hints ((and stable-under-simplificationp
                 '(:expand ((type-judgement-list tterm-lst options names state)
                            (type-judgement-list nil options names state)))))
    :flag type-judgement-list))
)

;; -------------------------------------------------------

(define type-judge-bottomup-cp ((cl pseudo-term-listp)
                                (smtlink-hint t)
                                state)
  (b* (((unless (pseudo-term-listp cl)) (value nil))
       ((unless (smtlink-hint-p smtlink-hint)) (value (list cl)))
       (goal (disjoin cl))
       ((type-options h) (construct-type-options smtlink-hint goal))
       (tterm (make-empty-typed-term goal))
       ((unless (good-typed-term-p tterm))
        (prog2$ (er hard? 'type-inference-bottomup=>type-judge-bottomup-cp
                    "Not a good-typed-term-p: ~q0" tterm)
                (value (list cl))))
       ((typed-term new-tt) (type-judgement tterm h h.names state))
       (new-cl `(implies (if ,new-tt.judgements ,new-tt.smt-judgements 'nil)
                         ,new-tt.term))
       (next-cp (cdr (assoc-equal 'type-judge-bottomup *SMT-architecture*)))
       ((if (null next-cp)) (value (list cl)))
       (the-hint
        `(:clause-processor (,next-cp clause ',smtlink-hint state)))
       (hinted-goal `((hint-please ',the-hint) ,new-cl)))
    (value (list hinted-goal))))

(defthm correctness-of-type-judge-bottomup-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (type-judge-bottomup-cp cl hints state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (type-judge-bottomup-cp
                            correct-typed-term
                            disjoin
                            make-empty-typed-term)
                           (correctness-of-type-judgement
                            type-judgement-maintains-path-cond
                            type-judgement-maintains-term
                            correctness-of-path-test-list-corollary
                            correctness-of-path-test-list
                            symbol-listp))
           :use ((:instance correctness-of-type-judgement
                            (options (construct-type-options hints (disjoin cl)))
                            (tterm (make-empty-typed-term (disjoin cl)))
                            (names (type-options->names
                                    (construct-type-options hints
                                                            (disjoin cl))))
                            (a a)
                            (state state))
                 (:instance type-judgement-maintains-path-cond
                            (options (construct-type-options hints (disjoin cl)))
                            (tterm (make-empty-typed-term (disjoin cl)))
                            (names (type-options->names
                                    (construct-type-options hints
                                                            (disjoin cl))))
                            (state state))
                 (:instance type-judgement-maintains-term
                            (options (construct-type-options hints (disjoin cl)))
                            (tterm (make-empty-typed-term (disjoin cl)))
                            (names (type-options->names
                                    (construct-type-options hints
                                                            (disjoin cl))))
                            (state state)))))
  :rule-classes :clause-processor)
