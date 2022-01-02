;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "ttmrg-change")

(set-state-ok t)
(set-induction-depth-limit 1)

; Mark is impatient
(local (in-theory (disable pseudo-termp pseudo-term-listp symbol-listp
  boolean-listp member-equal consp-of-pseudo-lambdap
  pseudo-lambdap-of-fn-call-of-pseudo-termp lambda-of-pseudo-lambdap
  pseudo-termp-when-pseudo-term-syntax-p ev-smtcp-of-type-hyp-call
  (:type-prescription pseudo-lambdap))))


(defsection move-this-stuff-to-../utils/pseudo-term
  (defines term-q
    :flag-local nil
    (define term-q ((term acl2::any-p))
      :returns (ok booleanp)
      :flag term
      (if (and (consp term)
	             (not (equal (car term) 'quote))
	             (true-listp term))
	        (args-q (cdr term))
	      t))

    (define args-q ((args acl2::any-p))
      :returns (ok booleanp)
      :flag args
      (if (consp args)
	        (and (term-q (car args))
	             (args-q (cdr args)))
	      (null args))))

  ;; Need to show that pseudo-termp implies term-q and pseudo-term-listp
  ;; implies args-q.  This helps because defthm-term-q-flag theorems tend to
  ;; have hypotheses involving pseudo-termp and pseudo-term-listp, and showing
  ;; these implications allows those hypotheses to discharge goals generated
  ;; from term-q and args-q.
  (defthm-term-q-flag
    (defthm pseudo-termp--implies--term-q
      (implies (pseudo-termp term) (term-q term))
      :hints('(:expand ((term-q term))))
      :flag term)

    (defthm pseudo-term-listp--implies--args-q
      (implies (pseudo-term-listp args) (args-q args))
      :hints('(:expand ((args-q args))))
      :flag args)))

;;-------------------------------------------------------
;; judgements of ground terms

(define fnsym-p ((x acl2::any-p))
  :returns (ok booleanp)
  (and (symbolp x)
       (not (booleanp x))
       (not (equal x 'quote))
       (not (equal x 'if)))
  ///
  (more-returns
    (ok :name not-nil-when-fnsym-p
        (implies ok (not (null x)))
	:rule-classes (:rewrite :forward-chaining))
    (ok :name symbolp-when-fnsym-p
        (implies ok (symbolp x))
	:rule-classes (:rewrite :forward-chaining))
    (ok :name pseudo-termp-when-fnsym-p
        (implies ok (pseudo-termp x))
	:rule-classes (:rewrite :forward-chaining)
	:hints(("Goal" :in-theory (enable pseudo-termp))))))

(define fnsym-fix ((x fnsym-p))
  :returns (y fnsym-p)
  (mbe :logic (if (fnsym-p x) x 'acl2::any-p)
       :exec x)
  ///
  (more-returns
    (y :name fnsym-fix-when-fnsym-p
       (implies (fnsym-p x) (equal y x)))))

(deffixtype fnsym
  :pred fnsym-p
  :fix  fnsym-fix
  :equiv fnsym-equiv
  :define t)

(defprod type-recognizer
  ((fn fnsym-p)
   (executable booleanp :default t)))

(deflist type-recognizer-list
  :elt-type type-recognizer
  :true-listp t)

(defprod type-inference-hint
  ((recognizers type-recognizer-list-p)))


(encapsulate nil
  (local (defrule lemma-*1/5
    (implies (consp x) (union-equal x y))))

  (defthm-term-q-flag ev-smtcp-of-ground-term
    (defthm ev-smtcp-of-ground-term
      (implies (and (pseudo-termp term) (null (acl2::simple-term-vars term))
		    (alistp a1) (alistp a2) (not (equal a1 a2)))
	       (equal (ev-smtcp term a1) (ev-smtcp term a2)))
      :flag term)

    (defthm ev-smtcp-of-ground-args
      (implies (and (pseudo-term-listp args) (null (acl2::simple-term-vars-lst args)) (alistp a1) (alistp a2))
	       (equal (ev-smtcp-lst args a1) (ev-smtcp-lst args a2)))
      :flag args)
    :hints(("Goal" :in-theory (enable pseudo-termp pseudo-term-listp
				      acl2::simple-term-vars acl2::simple-term-vars-lst
				      ev-smtcp-of-fncall-args)))))


(define judgements-of-ground-term-helper
    ((c pseudo-termp) (recognizers type-recognizer-list-p)
     (env symbol-alistp) (state state-p))
  :returns (j conj-p)
  (b* ((- (cw "checking (consp recognizers), recognizers = ~x0~%" recognizers))
       ((unless (consp recognizers)) ''t)
       (- (cw "extracting (car recognizers)~%"))
       ((cons (type-recognizer hd) tl) recognizers)
       (- (cw "checking (pseudo-termp c), c = ~x0~%" c))
       ((unless (mbt (pseudo-termp c))) ''t)
       (- (cw "making sure c is a quoted term~%"))
       ((unless (logic-fnsp c (w state))) ''t)
       ((unless (null (acl2::simple-term-vars c))) ''t)
       (pred (list hd.fn c))
       (- (cw "ready to (magic-ev ~x0 ~x1 state t nil)~%" pred env))
       ((mv magic-err magic-val)
	(if (and hd.executable
		 (acl2::logicp (car pred) (w state)))
	  (acl2::magic-ev pred env state t nil)
	  (mv t nil)))
       (- (cw "good-bye"))
       (j-tl (judgements-of-ground-term-helper c tl env state)))
    (if (and (not magic-err) magic-val)
      (conj-cons pred j-tl)
      j-tl))
  ///
  (local (in-theory (enable acl2::simple-term-vars acl2::simple-term-vars-lst)))
  (defrule judgements-of-ground-term-is-ground-term
    (not (acl2::simple-term-vars (judgements-of-ground-term-helper c recognizers env state)))
    :prep-lemmas(
      (defrule lemma-*1/1a
        (implies (and (pseudo-termp c)
		      (symbolp fn)
		      (not (acl2::simple-term-vars c)))
		 (not (acl2::simple-term-vars (list fn c)))))
      (defrule lemma-*1/1b
	(let ((fn (type-recognizer->fn (car recognizers)))
	      (j-cdr (judgements-of-ground-term-helper c (cdr recognizers) env state)))
	  (implies
	    (and
	      (pseudo-termp c)
	      (not (acl2::simple-term-vars c))
	      (not (acl2::simple-term-vars j-cdr)))
	    (not (acl2::simple-term-vars (conj-cons (list fn c) j-cdr)))))
	:in-theory (disable simple-term-vars-of-conj-cons)
	:use((:instance simple-term-vars-of-conj-cons (hd (list (type-recognizer->fn (car recognizers)) c))
						      (tl (judgements-of-ground-term-helper c (cdr recognizers) env state)))))))

  (defrule correctness-of-judgements-of-ground-term-helper
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (alistp env)
		  (alistp env2))
	     (ev-smtcp (judgements-of-ground-term-helper c recognizers env state) env2))
    :prep-lemmas (
      (defrule correctness-lemma-1
	  (implies (and (ev-smtcp-meta-extract-global-facts)
			(alistp env))
		   (ev-smtcp (judgements-of-ground-term-helper c recognizers env state) env))
	  :prep-lemmas (
	    (defrule lemma-*1/1
	      (implies (and (symbolp (type-recognizer->fn (car recognizers)))
			    (acl2::logicp (type-recognizer->fn (car recognizers)) (w state))
			    (pseudo-termp c)
			    (not (acl2::simple-term-vars c))
			    (logic-fnsp c (w state))
			    (alistp env)
			    (not (mv-nth 0 (acl2::magic-ev (list (type-recognizer->fn (car recognizers)) c) env state t nil)))
			    (mv-nth 1 (acl2::magic-ev (list (type-recognizer->fn (car recognizers)) c) env state t nil))
			    (ev-smtcp-meta-extract-global-facts))
		       (ev-smtcp (list (type-recognizer->fn (car recognizers)) c) env))
	      :do-not-induct t
	      :in-theory (disable acl2::magic-ev ev-smtcp-meta-extract-magic-ev)
	      :use((:instance ev-smtcp-meta-extract-magic-ev
			        (acl2::x (list (type-recognizer->fn (car recognizers)) c))
				(acl2::st state)
				(acl2::hard-errp t)
				(acl2::aokp nil)
				(acl2::alist env)))))
	  ; unless we disable w, lemma-*1/1 won't match "Subgoal *1/1".
	  ; Or, we could expand out w in the statement of lemma-*1/1, but that would be painful.
	  :in-theory (disable w)))
    :hints(("Goal"
      :in-theory (disable ev-smtcp-of-ground-term)
      :use((:instance ev-smtcp-of-ground-term
		      (term (judgements-of-ground-term-helper c recognizers env state))
		      (a1 env)
		      (a2 env2)))))))

; a simple example
(judgements-of-ground-term-helper '(unary-- '3)
  (list (make-type-recognizer :fn 'booleanp)
	(make-type-recognizer :fn 'integerp)
	(make-type-recognizer :fn 'natp)
	(make-type-recognizer :fn 'rationalp)
	(make-type-recognizer :fn 'true-listp))
 nil
 state)


(define judgements-of-const ((tterm ttmrg-syntax-p) (recognizers type-recognizer-list-p) (state state-p))
  :guard (and (consp (ttmrg->term tterm))
	      (equal (car (ttmrg->term tterm)) 'quote))
  :guard-debug t
  :returns (new-tt ttmrg-p)
  (b* (((ttmrg tterm) (ttmrg-fix tterm))
       (new-top-judge (judgements-of-ground-term-helper tterm.term recognizers nil state)))
     (strengthen-ttmrg->top-judge tterm new-top-judge))
  ///
  (more-returns
    (new-tt :name correctness-of-judgements-of-const
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (ttmrg-correct-p tterm))
	       (ttmrg-correct-p new-tt))
      :hints(("Goal"
       :use((:functional-instance
	      correctness-of-strengthen-ttmrg->top-judge
		(constrain-ttmrg->top-judge
		  (lambda (tterm state)
		    (judgements-of-ground-term-helper (ttmrg->term tterm) recognizers nil state))))))))
    (new-tt :name judgements-of-const--unchanged-fields
      (ttmrg-only-changed->judgements tterm new-tt))))

stop

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

(define type-judgement-quoted ((term pseudo-termp)
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
          (t (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-quoted
                         "Type inference for constant term ~p0 is not supported.~%"
                         term)
                     ''t))))
  ///
  (defthm correctness-of-type-judgement-quoted
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (alistp a))
             (ev-smtcp (type-judgement-quoted term options state) a))
    :hints (("Goal"
             :in-theory (e/d (pseudo-termp pseudo-term-listp)
                             (correctness-of-path-test-list-corollary
                              consp-of-is-conjunct?
                              acl2::symbol-listp-when-not-consp
                              correctness-of-path-test-list
                              ev-smtcp-of-variable))))))

;; ------------------------------------------------------------------
;;    Variable judgements

(define type-judgement-variable ((term pseudo-termp)
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
  (defthm correctness-of-type-judgement-variable
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (pseudo-termp path-cond)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (type-judgement-variable term path-cond options state) a))))

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

  (define type-judgement-if ((term pseudo-termp)
                             (path-cond pseudo-termp)
                             (options type-options-p)
                             (names symbol-listp)
                             state)
    :guard (and (consp term)
                (equal (car term) 'if))
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         (names (symbol-list-fix names))
         (options (type-options-fix options))
         ((type-options o) options)
         ((unless (mbt (and (consp term) (equal (car term) 'if)))) ''t)
         ((cons & actuals) term)
         ((unless (equal (len actuals) 3))
          (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-if
                      "Mangled if term: ~q0" term)
                  ''t))
         ((list cond then else) actuals)
         (judge-cond (type-judgement cond path-cond options names state))
         ((mv then-path-cond else-path-cond)
          (augment-path-cond cond judge-cond path-cond o.supertype))
         (judge-then
          (type-judgement then then-path-cond options names state))
         (judge-else
          (type-judgement else else-path-cond options names state))
         (judge-then-top (type-judgement-top judge-then then options))
         (judge-else-top (type-judgement-top judge-else else options))
         (judge-if-top
          (type-judgement-if-top judge-then-top then judge-else-top else
                                 cond names options))
         (judge-if-top-extended
          (extend-judgements judge-if-top path-cond options state)))
      `(if ,judge-if-top-extended
           (if ,judge-cond
               (if ,cond ,judge-then ,judge-else)
             'nil)
         'nil)))

  (define type-judgement-fn ((term pseudo-termp)
                             (path-cond pseudo-termp)
                             (options type-options-p)
                             (names symbol-listp)
                             state)
    :guard (and (consp term)
                (symbolp (car term))
                (not (equal (car term) 'if))
                (not (equal (car term) 'quote)))
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         (names (symbol-list-fix names))
         (options (type-options-fix options))
         ((unless (mbt (and (consp term)
                            (symbolp (car term))
                            (not (equal (car term) 'quote))
                            (not (equal (car term) 'if)))))
          ''t)
         ((cons fn actuals) term)
         (actuals-judgements
          (type-judgement-list actuals path-cond options names state))
         (actuals-judgements-top
          (type-judgement-top-list actuals-judgements actuals options))
         (functions (type-options->functions options))
         (conspair (assoc-equal fn functions))
         ((unless conspair)
          (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-fn
                      "There exists no function description for function ~p0. ~
                       ~%" fn)
                  ''t))
         (fn-description (cdr conspair))
         ;; return-judgement could be ''t which means it could be anything
         (return-judgement
          (returns-judgement fn actuals actuals-judgements-top fn-description
                             path-cond ''t state))
         ((if (equal return-judgement ''t))
          (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-fn
                      "Failed to find type judgements for return of function ~
                       call ~p0~%Current path-cond: ~p1~%Actuals-judgements: ~
                       ~p2~%"
                      term path-cond actuals-judgements-top)
                  ''t))
         (return-judgement-extended
          (extend-judgements return-judgement path-cond options state)))
      `(if ,return-judgement-extended
           ,actuals-judgements
         'nil)))

  (define type-judgement ((term pseudo-termp)
                          (path-cond pseudo-termp)
                          (options type-options-p)
                          (names symbol-listp)
                          state)
    :measure (list (acl2-count (pseudo-term-fix term)) 1)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         (names (symbol-list-fix names))
         (options (type-options-fix options))
         ((if (acl2::variablep term))
          (type-judgement-variable term path-cond options state))
         ((if (acl2::quotep term))
          (type-judgement-quoted term options state))
         ((cons fn &) term)
         ((if (pseudo-lambdap fn))
          ;; (type-judgement-lambda term path-cond options names state)
          (prog2$ (er hard? 'type-inference-bottomup=>type-judgement
                      "Found lambda in the goal.~%")
                  ''t))
         ((if (equal fn 'if))
          (type-judgement-if term path-cond options names state)))
      (type-judgement-fn term path-cond options names state)))

  (define type-judgement-list ((term-lst pseudo-term-listp)
                               (path-cond pseudo-termp)
                               (options type-options-p)
                               (names symbol-listp)
                               state)
    :measure (list (acl2-count (pseudo-term-list-fix term-lst)) 1)
    :returns (judgements-lst pseudo-termp)
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (path-cond (pseudo-term-fix path-cond))
         (names (symbol-list-fix names))
         ((unless (consp term-lst)) ''t)
         ((cons first rest) term-lst)
         (first-judge (type-judgement first path-cond options names state))
         (rest-judge (type-judgement-list rest path-cond options names state)))
      `(if ,first-judge
           ,rest-judge
         'nil)))
  ///
  (defthm correctness-of-type-judgement-list-nil
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp path-cond)
                  (symbol-listp names)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (type-judgement-list nil path-cond options names state) a))
    :hints (("Goal"
             :expand (type-judgement-list nil path-cond options names state))))
  )

(verify-guards type-judgement)

;; ------------------------------------------------
;; Correctness theorems for type-judgement

(encapsulate ()
(local (in-theory (disable pseudo-termp
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
                              ev-smtcp-of-lambda)))

(defthm-type-judgements-flag
  (defthm correctness-of-type-judgement-if
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (pseudo-termp path-cond)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (type-judgement-if term path-cond options names state) a))
    :flag type-judgement-if
    :hints ((and stable-under-simplificationp
                 '(:expand (type-judgement-if term path-cond options names
                                              state)))))
  (defthm correctness-of-type-judgement-fn
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (pseudo-termp path-cond)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (type-judgement-fn term path-cond options names state) a))
    :hints ((and stable-under-simplificationp
                 '(:expand (type-judgement-fn term path-cond options names
                                              state))))
    :flag type-judgement-fn)
  (defthm correctness-of-type-judgement
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (pseudo-termp path-cond)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (type-judgement term path-cond options names state) a))
    :flag type-judgement
    :hints ((and stable-under-simplificationp
                 '(:expand (type-judgement term path-cond options names
                                           state)))))
  (defthm correctness-of-type-judgement-list
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-term-listp term-lst)
                  (pseudo-termp path-cond)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (type-judgement-list term-lst path-cond options names state)
                       a))
    :hints ((and stable-under-simplificationp
                 '(:expand ((type-judgement-list term-lst path-cond options
                                                 names state)
                            (type-judgement-list nil path-cond options names
                                                 state)))))
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
       (judges (type-judgement goal ''t h h.names state))
       (new-cl `(implies ,judges ,goal))
       (next-cp (cdr (assoc-equal 'type-judge-bottomup *SMT-architecture*)))
       ((if (null next-cp)) (value (list cl)))
       (the-hint
        `(:clause-processor (,next-cp clause ',smtlink-hint state)))
       (hinted-goal `((hint-please ',the-hint) ,new-cl))
       (- (cw "type-judge-bottomup-cp: ~q0" hinted-goal)))
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
           :in-theory (enable type-judge-bottomup-cp)))
  :rule-classes :clause-processor)
