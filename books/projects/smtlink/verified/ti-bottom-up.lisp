;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "ttmrg-change")
(include-book "typed-term-fns")
(include-book "judgement-fns")
(include-book "returns-judgement")
(include-book "type-options")
(include-book "../utils/fresh-vars")
(include-book "make-test")

(set-state-ok t)
(set-induction-depth-limit 1)

; Mark is impatient
(local (in-theory (disable pseudo-termp pseudo-term-listp symbol-listp
  boolean-listp member-equal consp-of-pseudo-lambdap
  pseudo-lambdap-of-fn-call-of-pseudo-termp lambda-of-pseudo-lambdap
  pseudo-termp-when-pseudo-term-syntax-p ev-smtcp-of-type-hyp-call
  (:type-prescription pseudo-lambdap) member-equal)))

(deflist conj-list
  :elt-type conj
  :true-listp t)


(define update-path-cond-args-help
    ((ttargs ttmrg-list-p) (new-path-cond conj-p))
  :returns (new-args ttmrg-list-p)
  (if (consp ttargs)
    (cons (strengthen-ttmrg->path-cond (car ttargs) new-path-cond)
	  (update-path-cond-args-help (cdr ttargs) new-path-cond))
    nil)
  ///
  (more-returns
    (new-args :name ttmrg-args-simple-count-of-update-path-cond-args-help
      (equal (ttmrg-args-simple-count new-args)
	     (ttmrg-args-simple-count ttargs))
      :hints(("Goal"
	:in-theory (enable update-path-cond-args-help
			   ttmrg-args-simple-count))))))

(define update-path-cond-term-help ((tterm ttmrg-p))
  :returns (new-args ttmrg-list-p)
  (b* (((ttmrg tterm) tterm)
       ((unless (and (consp tterm.term)
		     (not (equal (car tterm.term) 'quote))))
	(ttmrg->args tterm))
       ((unless (and (equal (car tterm.term) 'if)
		     (consp (cddr (ttmrg->args tterm)))
		     (not (cdddr (ttmrg->args tterm)))))
	(update-path-cond-args-help tterm.args tterm.path-cond)))
    (list (strengthen-ttmrg->path-cond (car tterm.args) tterm.path-cond)
	  (strengthen-ttmrg->path-cond (cadr tterm.args)
	    (conj-cons2 (ttmrg->term (car tterm.args)) tterm.path-cond))
	  (strengthen-ttmrg->path-cond (caddr tterm.args)
	    (conj-cons2 `(not ,(ttmrg->term (car tterm.args)))
			tterm.path-cond))))
  ///
  (more-returns
    (new-args :name ttmrg-args-simple-count-of-update-path-cond-term-help
      (equal (ttmrg-args-simple-count new-args)
	     (ttmrg-args-simple-count (ttmrg->args tterm)))
      :hints(("Goal"
	:in-theory (enable update-path-cond-term-help
			   ttmrg-args-simple-count))))))

(defines update-path-cond
  (define update-path-cond-term ((tterm ttmrg-p))
    :flag term
    :returns (new-tt ttmrg-p)
    :measure (ttmrg-simple-count tterm)
    :verify-guards nil
    (let ((tterm2
	   (change-ttmrg->args
	     tterm
	     (update-path-cond-term-help tterm))))
      (change-ttmrg->args
	tterm2
	(update-path-cond-args (ttmrg->args tterm2)))))

  (define update-path-cond-args ((ttargs ttmrg-list-p))
    :flag args
    :returns (new-args ttmrg-list-p)
    :measure (ttmrg-args-simple-count ttargs)
    (if (consp ttargs)
      (cons (update-path-cond-term (car ttargs))
	    (update-path-cond-args (cdr ttargs)))
      nil))
  ///
  (verify-guards update-path-cond-term)

  (defrule ttmrg-args-only-changed->args-of-update-path-cond-args
    (ttmrg-args-only-changed->args
      (update-path-cond-args ttargs) ttargs)
    :in-theory (enable ttmrg-args-only-changed->args)
    :prep-lemmas (
      (defrule lemma-*1/3
	(equal (consp (update-path-cond-args ttargs))
	       (consp ttargs))
	:use((:instance update-path-cond-args)))
      (defrule change-ttmrg->args-ttmrg-args-only-changed->args
	(and (equal (ttmrg->term (change-ttmrg->args tterm new-ttargs))
		    (ttmrg->term tterm))
	     (equal (ttmrg->path-cond (change-ttmrg->args tterm new-ttargs))
		    (ttmrg->path-cond tterm)))
	:use((:instance change-ttmrg->args)))
      (defrule lemma-*1/2
	(implies (consp ttargs)
	  (and (equal (ttmrg->term (car (update-path-cond-args ttargs)))
		      (ttmrg->term (car ttargs)))
	       (equal (ttmrg->path-cond (car (update-path-cond-args ttargs)))
		      (ttmrg->path-cond (car ttargs)))))
	  :use((:instance update-path-cond-args)
	       (:instance update-path-cond-term (tterm (car ttargs)))))))

  (local (encapsulate nil
    (defrule ttmrg-args->stronger-path-cond-of-update-path-cond-term-help
      (implies (alistp env)
	(ttmrg-args->stronger-path-cond
	  (ttmrg->args tterm)
	  (update-path-cond-term-help tterm)
	  env))
      :in-theory (enable update-path-cond-term-help
			 ttmrg-args->stronger-path-cond)
      :prep-lemmas (
	(defrule lemma-args
	  (implies (and (alistp env) (pseudo-termp new-path-cond))
	    (ttmrg-args->stronger-path-cond
	      ttargs
	      (update-path-cond-args-help ttargs new-path-cond)
	      env))
	  :in-theory (enable ttmrg-args->stronger-path-cond
			     update-path-cond-args-help
			     strengthen-ttmrg->path-cond))))

    (defrule ttmrg-args-correct-path-of-update-path-cond-term-help
      (implies
	(and (ttmrg-correct-p tterm)
	     (alistp env)
	     (ev-smtcp (ttmrg->path-cond tterm) env)
	     (consp (ttmrg->term tterm))
	     (not (equal (car (ttmrg->term tterm)) 'quote)))
	(let ((new-ttargs (update-path-cond-term-help tterm)))
	  (if (equal (car (ttmrg->term tterm)) 'if)
	    (and (ev-smtcp (ttmrg->path-cond (car new-ttargs)) env)
		 (if (ev-smtcp (ttmrg->term (car new-ttargs)) env)
		   (ev-smtcp (ttmrg->path-cond (cadr new-ttargs)) env)
		   (ev-smtcp (ttmrg->path-cond (caddr new-ttargs)) env)))
	    (ttmrg-args-correct-path new-ttargs env))))
      :expand ((update-path-cond-term-help tterm)
	       (ttmrg-correct-p tterm))
      :use((:instance ttmrg-correct-sk-necc))
      :prep-lemmas (
	(defrule lemma-args
	  (implies (and (alistp env)
			(conj-p path-cond)
			(ttmrg-args-correct-path ttargs env)
			(ev-smtcp path-cond env))
		   (ttmrg-args-correct-path
		     (update-path-cond-args-help ttargs path-cond)
		     env))
	  :in-theory (enable update-path-cond-args-help
			     ttmrg-args-correct-path))))

    (defrule ttmrg-correct-p-of-update-path-cond-term-help
      (implies
	(and (ttmrg-correct-p tterm)
	     (ev-smtcp-meta-extract-global-facts))
	(ttmrg-correct-p
	  (change-ttmrg->args tterm
			      (update-path-cond-term-help tterm))))
      :use((:functional-instance
	      ttmrg-correct-p-of-change-ttmrg-args--strengthen-path-cond
	(constrain-ttmrg->args-path-cond
	  (lambda (tterm state) (update-path-cond-term-help tterm))))))

    (local (defrule lemma-0
	(equal (ttmrg->args (change-ttmrg->args tterm new-ttargs))
	       (ttmrg-list-fix new-ttargs))
	:expand (change-ttmrg->args tterm new-ttargs)))

    (defrule ttmrg-args-correct-p-of-update-path-cond-term-help
      (implies
	(and (ttmrg-correct-p tterm)
	     (ev-smtcp-meta-extract-global-facts))
	(ttmrg-args-correct-p (update-path-cond-term-help tterm)))
      :in-theory (disable ttmrg-args-correct-p-when-ttmrg-correct-p)
      :use ((:instance ttmrg-args-correct-p-when-ttmrg-correct-p
		       (tterm (change-ttmrg->args
				tterm
				(update-path-cond-term-help tterm))))))

    (defrule ttmrg->args-of-update-path-cond-term-help
      (implies
	(and (ttmrg-correct-p tterm)
	     (ev-smtcp-meta-extract-global-facts))
	(equal (ttmrg->args
		 (change-ttmrg->args tterm (update-path-cond-term-help tterm)))
	       (update-path-cond-term-help tterm))))

    (local (defrule lemma-correct-p-1
      (implies
	(and (ev-smtcp-meta-extract-global-facts)
	     (ttmrg-correct-p tterm)
	     (ttmrg-args-correct-p
	       (update-path-cond-args (ttmrg->args tterm))))
	(ttmrg-correct-p
	  (change-ttmrg->args
	    tterm
	    (update-path-cond-args (ttmrg->args tterm)))))
      :use((:functional-instance
	ttmrg-correct-p-of-constrain-ttmrg->args-args
	(constrain-ttmrg->args-args
	  (lambda (tterm state)
	     (update-path-cond-args (ttmrg->args tterm))))))))

    (defrule lemma-correct-p-2
      (implies
	(and (ev-smtcp-meta-extract-global-facts)
	     (ttmrg-correct-p tterm)
	     (ttmrg-args-correct-p
	       (update-path-cond-args (update-path-cond-term-help tterm))))
	(ttmrg-correct-p
	  (change-ttmrg->args
	    (change-ttmrg->args tterm
				(update-path-cond-term-help tterm))
	    (update-path-cond-args (update-path-cond-term-help tterm)))))
      :rule-classes ((:rewrite :match-free :all))
      :in-theory (disable lemma-correct-p-1)
      :use((:instance lemma-correct-p-1
			(tterm (change-ttmrg->args
				 tterm
				 (update-path-cond-term-help tterm))))))))

   (defthm-update-path-cond-flag
     (defthm ttmrg-correct-p-of-update-path-cond-term
       (implies (and (ev-smtcp-meta-extract-global-facts)
		     (ttmrg-correct-p tterm))
		(ttmrg-correct-p (update-path-cond-term tterm)))
       :flag term)
     (defthm ttmrg-args-correct-p-of-update-path-cond-args
       (implies (and (ev-smtcp-meta-extract-global-facts)
		     (ttmrg-args-correct-p ttargs))
		(ttmrg-args-correct-p (update-path-cond-args ttargs)))
       :flag args)
     :hints(("Goal"
       :in-theory (enable ttmrg-args-correct-p)))))


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
      (implies (and (pseudo-termp term)
		    (null (acl2::simple-term-vars term))
		    (alistp a1) (alistp a2) (not (equal a1 a2)))
	       (equal (ev-smtcp term a1) (ev-smtcp term a2)))
      :flag term)

    (defthm ev-smtcp-of-ground-args
      (implies (and (pseudo-term-listp args)
		    (null (acl2::simple-term-vars-lst args))
		    (alistp a1) (alistp a2))
	       (equal (ev-smtcp-lst args a1) (ev-smtcp-lst args a2)))
      :flag args)
    :hints(("Goal" :in-theory (enable pseudo-termp pseudo-term-listp
				      acl2::simple-term-vars acl2::simple-term-vars-lst
				      ev-smtcp-of-fncall-args)))))

(define judgements-of-ground-term-helper
    ((c pseudo-termp) (recognizers type-recognizer-list-p)
     (env symbol-alistp) (state state-p))
  :returns (j conj-p)
  (b* (((unless (consp recognizers)) ''t)
       ((cons (type-recognizer hd) tl) recognizers)
       ((unless (mbt (pseudo-termp c))) ''t)
       ((unless (logic-fnsp c (w state))) ''t)
       ((unless (null (acl2::simple-term-vars c))) ''t)
       (pred (list hd.fn c))
       ((mv magic-err magic-val)
	(if (and hd.executable
		 (acl2::logicp (car pred) (w state)))
	  (acl2::magic-ev pred env state t nil)
	  (mv t nil)))
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
	:use((:instance simple-term-vars-of-conj-cons
			  (hd (list (type-recognizer->fn (car recognizers)) c))
			  (tl (judgements-of-ground-term-helper
				c (cdr recognizers) env state)))))))

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

(make-test ; a simple example
  (equal (judgements-of-ground-term-helper
	   '(unary-- '3)
	   (list (make-type-recognizer :fn 'booleanp)
		 (make-type-recognizer :fn 'integerp)
		 (make-type-recognizer :fn 'natp)
		 (make-type-recognizer :fn 'rationalp)
		 (make-type-recognizer :fn 'true-listp))
	   nil
	   state)
	 '(if (integerp (unary-- '3))
	    (if (rationalp (unary-- '3))
	      't
	      'nil)
	    'nil))
  :output (:fail (:all . :warn)))


(define judgements-of-const ((tterm ttmrg-syntax-p)
			     (recognizers type-recognizer-list-p)
			     (state state-p))
  :guard (and (consp (ttmrg->term tterm))
	      (equal (car (ttmrg->term tterm)) 'quote))
  :guard-debug t
  :returns (new-tt ttmrg-p)
  (b* (((ttmrg tterm) (ttmrg-fix tterm))
       (new-top-judge
	 (judgements-of-ground-term-helper tterm.term recognizers nil state)))
     (strengthen-ttmrg->top-judgement tterm new-top-judge))
  ///
  (more-returns
    (new-tt :name correctness-of-judgements-of-const
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (ttmrg-correct-p tterm))
	       (ttmrg-correct-p new-tt))
      :hints(("Goal"
       :use((:functional-instance
	      correctness-of-strengthen-ttmrg->top-judgement
		(constrain-ttmrg->top-judgement
		  (lambda (tterm state)
		    (judgements-of-ground-term-helper
		      (ttmrg->term tterm) recognizers nil state))))))))
    (new-tt :name judgements-of-const--unchanged-fields
      (ttmrg-only-changed->top-judgement tterm new-tt))))


;; ------------------------------------------------------------------
;;    Judgements of variables

(define judgements-of-variable-helper
    ((tterm ttmrg-syntax-p) (options type-options-p) (state state-p))
  :returns (judge conj-p)
  (b* (((ttmrg tterm) (ttmrg-fix tterm))
       (options (type-options-fix options))
       (supertype (type-options->supertype options)))
    (term-to-conj
      (extend-judgements
	(look-up-path-cond tterm.term tterm.path-cond supertype)
	tterm.path-cond options state)))
  ///
  (more-returns judgements-of-variable-helper
    (judge :name correctness-of-judgements-of-variable-helper
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (alistp env)
		    (ev-smtcp (ttmrg->path-cond tterm) env))
	       (ev-smtcp judge env))
      :hints(("Goal"
	:in-theory (enable judgements-of-variable-helper))))))

(define judgements-of-variable
    ((tterm ttmrg-syntax-p) (options type-options-p) (state state-p))
  :returns (new-tt ttmrg-p)
  (strengthen-ttmrg->top-judgement tterm
    (judgements-of-variable-helper tterm options state))
  ///
  (more-returns
    (new-tt :name correctness-of-judgements-of-variable
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (ttmrg-correct-p tterm))
	       (ttmrg-correct-p new-tt))
      :hints(("Goal"
       :in-theory (enable judgements-of-variable)
       :use((:functional-instance
	      correctness-of-strengthen-ttmrg->top-judgement
		(constrain-ttmrg->top-judgement
		  (lambda (tterm state)
		    (judgements-of-variable-helper tterm options state))))))))
    (new-tt :name judgements-of-variable--unchanged-fields
      (ttmrg-only-changed->top-judgement tterm new-tt))))


(define judgements-of-if ((tterm ttmrg-syntax-p))
  :returns (new-tt ttmrg-p)
  :guard (and (consp (ttmrg->term tterm))
	      (equal (car (ttmrg->term tterm)) 'if))
  (b* (((ttmrg tterm) (ttmrg-fix tterm))
       ((unless (mbt (and (consp tterm.term) (equal (car tterm.term) 'if))))
	tterm)
       (thenj (ttmrg->top-judgement (cadr tterm.args)))
       (elsej (ttmrg->top-judgement (caddr tterm.args))))
    (strengthen-ttmrg->top-judgement tterm (conj-common thenj elsej)))
  ///
 (defrule correctness-of-judgements-of-if
   (let ((new-tt (judgements-of-if tterm)))
     (implies (and (ev-smtcp-meta-extract-global-facts)
		   (ttmrg-correct-p tterm))
	      (ttmrg-correct-p new-tt)))
   :expand (judgements-of-if tterm)
   :use((:functional-instance correctness-of-strengthen-ttmrg->top-judgement
	   (constrain-ttmrg->top-judgement
	    (lambda (tterm state)
	      (if (and (ttmrg-correct-p tterm)
		       (equal (car (ttmrg->term tterm)) 'if))
		(conj-common
		  (ttmrg->top-judgement (cadr (ttmrg->args tterm)))
		  (ttmrg->top-judgement (caddr (ttmrg->args tterm))))
		''t)))))
   :prep-lemmas (
     (defrule path-cond-implies-judgements
       (implies (and (ttmrg-correct-p tterm)
		     (alistp env)
		     (equal (car (ttmrg->term tterm)) 'if)
		     (ev-smtcp (ttmrg->path-cond tterm) env))
		(ev-smtcp (conj-common
			    (ttmrg->top-judgement (cadr (ttmrg->args tterm)))
			    (ttmrg->top-judgement (caddr (ttmrg->args tterm))))
			  env))
       :use((:instance ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk))
       :prep-lemmas (
	 (in-theory (enable ttmrg-correct-sk-thms))
	 (defrule lemma-then
	   (implies
	     (and (ttmrg-correct-p tterm)
		  (alistp env)
		  (equal (car (ttmrg->term tterm)) 'if))
	     (and
	       (implies
		 (ev-smtcp (ttmrg->path-cond (cadr (ttmrg->args tterm))) env)
		 (ev-smtcp (ttmrg->top-judgement (cadr (ttmrg->args tterm))) env))
	       (implies
		 (ev-smtcp (ttmrg->path-cond (caddr (ttmrg->args tterm))) env)
		 (ev-smtcp (ttmrg->top-judgement (caddr (ttmrg->args tterm))) env))))
	   :use((:instance member-when-ttmrg-args-correct-p
			     (ttargs (ttmrg->args tterm))
			     (ttarg (cadr (ttmrg->args tterm))))
		(:instance member-when-ttmrg-args-correct-p
			     (ttargs (ttmrg->args tterm))
			     (ttarg (caddr (ttmrg->args tterm))))
		(:instance ttmrg-syntax-p))))))))


(define judgements-of-fncall-help ((tterm ttmrg-syntax-p)
				   (options type-options-p)
				   (state state-p))
  :returns (new-judge conj-p)
  :guard (and (consp (ttmrg->term tterm))
	      (not (equal (car (ttmrg->term tterm)) 'quote))
	      (not (equal (car (ttmrg->term tterm)) 'if)))
  :guard-hints(("Goal" :use((:instance ttmrg-syntax-p))))
  (b* (((ttmrg tterm) (ttmrg-fix tterm))
       ((unless (mbt (and (consp tterm.term)
			  (not (equal (car tterm.term) 'quote))
			  (not (equal (car tterm.term) 'if)))))
	''t)
       ((cons fn actuals) tterm.term)
       (actuals-judgements-top (ttmrg->args-judgements tterm))
       (functions (type-options->functions options))
       (conspair (assoc-equal fn functions))
       ((unless conspair)
	(prog2$ (cw "no returns theorem found for ~x0~%" fn) ''t)))
    (term-to-conj
      (extend-judgements
	(returns-judgement
	  fn actuals actuals-judgements-top (cdr conspair)
	  tterm.path-cond ''t state)
	tterm.path-cond options state))))

(define judgements-of-fncall ((tterm ttmrg-syntax-p)
			      (options type-options-p)
			      (state state-p))
  :returns (new-tt ttmrg-p)
  :guard (and (consp (ttmrg->term tterm))
	      (not (equal (car (ttmrg->term tterm)) 'quote))
	      (not (equal (car (ttmrg->term tterm)) 'if)))
  :verify-guards nil
  (strengthen-ttmrg->top-judgement tterm
    (judgements-of-fncall-help tterm options state))
  ///
  (local (defrule correctness-of-judgements-of-fncall-help
    (let ((new-judge (judgements-of-fncall-help tterm options state)))
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (ttmrg-syntax-p tterm)
		    (alistp env)
		    (ev-smtcp (ttmrg->args-judgements tterm) env)
		    (ev-smtcp (ttmrg->path-cond tterm) env))
	       (ev-smtcp new-judge env)))
      :in-theory (disable alistp correctness-of-returns-judgement)
      :use((:instance judgements-of-fncall-help)
	   (:instance correctness-of-returns-judgement
		      (term (ttmrg->term tterm))
		      (a env)
		      (fn (car (ttmrg->term tterm)))
		      (actuals (cdr (ttmrg->term tterm)))
		      (actuals-judgements (ttmrg->args-judgements tterm))
		      (path-cond (ttmrg->path-cond tterm))
		      (respec-lst (cdr (assoc-equal (car (ttmrg->term tterm))
						    (type-options->functions options))))
		      (acc ''t)))

      :prep-lemmas (
	(defrule lemma-1
	  (implies (and (ttmrg-syntax-p tterm)
			(consp (ttmrg->term tterm)))
		   (symbolp (car (ttmrg->term tterm))))
	  :use((:instance ttmrg-syntax-p))))))

  (verify-guards judgements-of-fncall
    :hints(("Goal" :use((:instance ttmrg-syntax-p)))))

  (defrule correctness-of-judgements-of-fncall
    (let ((new-tt (judgements-of-fncall tterm options state)))
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (consp (ttmrg->term tterm))
		    (not (equal (car (ttmrg->term tterm)) 'quote))
		    (not (equal (car (ttmrg->term tterm)) 'if))
		    (ttmrg-correct-p tterm))
	       (ttmrg-correct-p new-tt)))
    :expand (judgements-of-fncall tterm options state)
    :use((:functional-instance correctness-of-strengthen-ttmrg->top-judgement
	    (constrain-ttmrg->top-judgement
	     (lambda (tterm state)
	       (if (and (ttmrg-correct-p tterm)
			(consp (ttmrg->term tterm))
			(not (equal (car (ttmrg->term tterm)) 'quote))
			(not (equal (car (ttmrg->term tterm)) 'if)))
		 (judgements-of-fncall-help tterm options state)
		 ''t)))))
    :prep-lemmas (
      (defrule lemma-1
	(implies (and (ttmrg-correct-p tterm)
		      (consp (ttmrg->term tterm))
		      (not (equal (car (ttmrg->term tterm)) 'quote))
		      (not (equal (car (ttmrg->term tterm)) 'if))
		      (alistp env)
		      (ev-smtcp (ttmrg->path-cond tterm) env))
		 (and (ttmrg-args-correct-p (ttmrg->args tterm))
		      (ttmrg-args-correct-path (ttmrg->args tterm) env)))
	:in-theory (e/d (ttmrg-correct-p ttmrg-correct-sk) (alistp))
	:use((:instance ttmrg-correct-sk-necc))
	:rule-classes ((:rewrite :match-free :all)))
      (defrule lemma-2
	(implies (and (alistp env)
		      (ttmrg-correct-p tterm)
		      (ev-smtcp (ttmrg->path-cond tterm) env))
		 (ev-smtcp (ttmrg->top-judgement tterm) env))
	:in-theory (e/d (ttmrg-correct-p ttmrg-correct-sk) (alistp))
	:use((:instance ttmrg-correct-sk-necc)))
      (defrule lemma-3
	(implies (and (alistp env)
		      (ttmrg-args-correct-p ttargs)
		      (ttmrg-args-correct-path ttargs env))
		 (ev-smtcp (ttmrg->args-judgements-help ttargs) env))
	:in-theory (enable ttmrg-args-correct-p ttmrg-args-correct-path ttmrg->args-judgements-help))
      (defrule lemma-4
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (alistp env)
		      (ttmrg-correct-p tterm)
		      (consp (ttmrg->term tterm))
		      (not (equal (car (ttmrg->term tterm)) 'quote))
		      (not (equal (car (ttmrg->term tterm)) 'if))
		      (ev-smtcp (ttmrg->path-cond tterm) env))
		 (ev-smtcp (judgements-of-fncall-help tterm options state)
			   env))
	:in-theory (disable alistp correctness-of-judgements-of-fncall-help)
	:use((:instance correctness-of-judgements-of-fncall-help)
	     (:instance ttmrg->args-judgements))))))

(acl2::rule
  (implies (alistp env)
	   (equal (ev-smtcp ''t env) 't))
  :do-not-induct t)



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
