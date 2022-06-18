;; Copyright (C) 2015, University of British Columbia)
;; Originally written by Yan Peng (December 30th 2019)
;; Edited by Mark Greenstreet
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
;(include-book "clause-processors/just-expand" :dir :system)
;(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "conj")

(set-induction-depth-limit 1)
(local (in-theory (disable pseudo-termp ;; Mark is impatient
    pseudo-term-listp integer-listp rational-listp default-cdr
    consp-of-pseudo-lambdap
    lambda-of-pseudo-lambdap
    pseudo-lambdap-of-fn-call-of-pseudo-termp
    ACL2::PSEUDO-LAMBDAP-OF-CAR-WHEN-PSEUDO-LAMBDA-LISTP
    ACL2::PSEUDO-LAMBDAP-WHEN-MEMBER-EQUAL-OF-PSEUDO-LAMBDA-LISTP
    CONSP-OF-CDR-OF-PSEUDO-LAMBDAP
    acl2::integerp-of-car-when-integer-listp
    acl2::rationalp-of-car-when-rational-listp
    acl2::integer-listp-of-cdr-when-integer-listp
    acl2::rational-listp-of-cdr-when-rational-listp
    ACL2::SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP
    ACL2::SYMBOL-LISTP-WHEN-NOT-CONSP
    ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP)))

(defsection ttmrg-basics
  (set-well-founded-relation l<)

  (fty::deftypes ttmrg
    (defprod ttmrg
      :measure (list (acl2-count x) 1)
      ((term pseudo-termp :default ''nil)
       (path-cond conj-p :default ''t)
       (args ttmrg-list-p :default nil)
       (top-judgement conj-p :default ''t)))

    (deflist ttmrg-list
      :elt-type ttmrg-p
      :true-listp t
      :measure (list (acl2-count x) 0)))

  (acl2::defrule ttmrg->args-smaller-than-tterm
    (implies (ttmrg-p tterm)
	     (< (acl2-count (ttmrg->args tterm))
		(acl2-count tterm)))
    :rule-classes (:rewrite :linear)
    :expand ((ttmrg->args tterm)
	     (ttmrg-p tterm)))

  (define ttmrg->args-judgements-help ((ttargs ttmrg-list-p))
    :returns (judgements conj-conj-p)
    (if (consp ttargs)
      (conj-cons (ttmrg->top-judgement (car ttargs))
		 (ttmrg->args-judgements-help (cdr ttargs)))
      ''t))

  (define ttmrg->args-judgements ((tterm ttmrg-p))
    :returns (j conj-conj-p)
    (ttmrg->args-judgements-help (ttmrg->args tterm)))

  (define ttmrg->judgements ((tterm ttmrg-p))
    :returns (j conj-conj-p)
    (conj-cons (ttmrg->top-judgement tterm)
	       (ttmrg->args-judgements tterm)))

  (define ttmrg-list->terms ((args ttmrg-list-p))
    :returns (terms pseudo-term-listp)
    (b* (((unless (consp args)) nil)
	 ((cons hd tl) args))
       (cons (ttmrg->term hd)
	     (ttmrg-list->terms tl))))

  ; ttmrg-list->judgements only used in triv.lisp.
  ; after refactoring to make judgements a derived field,
  ; check to see if we can delete ttmrg-list->judgements
  (define ttmrg-list->judgements ((args ttmrg-list-p))
    :returns (judgements conj-conj-p)
    (b* (((unless (consp args)) ''t)
	 ((cons hd tl) args))
       (conj-cons (ttmrg->judgements hd)
		  (ttmrg-list->judgements tl)))))

(defines ttmrg-syntax
  :well-founded-relation l<
  :flag-local nil
  (define ttmrg-syntax-p ((tterm acl2::any-p))
    :returns (ok booleanp)
    :measure (list (acl2-count tterm) 1)
    :hints(("Goal" :in-theory (disable acl2-count)))
    :flag term
    :short "recognizer for &ldquo;syntactically correct&rdquo; @(see ttmrg) structures"
    :long "<p>@('(ttmrg-syntax-p tterm)') requires:
      <ul><li>@('(ttmrg-p tterm)')</li>
	  <li>If @('(atom (ttmrg->term tterm))')
	    or @('(equal (car (ttmrg->term tterm)) 'quote)'),
	    then @('(ttmrg->args tterm)') must be @('nil').
	    The other fields, @('path-cond') and @('judgements'), are unconstrained.
	  </li>
	  <li>If @('(car (ttmrg->term tterm))') is a symbol other than @(''nil')
	    or @(''t'), then the term is a function call.  In this case
	    @'((ttmrg->judgements tterm)') must satisfy @('conj-conj-p') and
	    @('((conj-len (ttmrg->judgments tterm)))') must be the same as
	    @('((len (ttmrg->term tterm)))').  In other words, the first
	    element of judgements is for the term, and the rest of
	    judgements are the judgements for the arguments to the function.
	    Each of these judgements is a @(see conj-p).
	    Likewise, @('(equal (len (ttmrg->args tterm) (len (cdr (ttrmg->term tterm)))))')
	    must hold.
	    <p>
	    Is the test that the function symbol is not a boolean helpful?
	    Or, does it just create extra work when proving that
	    ttmrg-syntax-p holds for some term?
	    </d>
	  </li>
	  <li>If @('(car (ttmrg->term tterm))') is the symbol @(''if'),
	    then the @('args') field must have length three,  i.e.
	    @('(and (consp (cdddr term)) (not (cddddr term)))') where
	    @('term) is @('(ttrmg->ter tterm)').
	  </li>
	  <li>A @(see ttmrg) that satisfies @('ttmrg-syntax-p')
	    cannot be a lambda expression.  All lambdas in the goal should have
	    been flattened in the expand-clause-processor. This simplifies the
	    implementation of the remaining Smtlink clause-processors.
	  </li>
      </ul>
      If we know that a @('ttmrg) object satisfies @('ttmrg-syntax-p), then
      we avoid needing many tests about the shape of the term.
    </p>"
    (b* (((unless (ttmrg-p tterm)) nil)
	 ((ttmrg tterm) tterm)
	 (term tterm.term)
	 ((if (atom term)) (null tterm.args))
	 (fn (car term))
	 ((if (equal fn 'quote))
	   (and (not tterm.args)
		(consp (cdr term))
		(not (cddr term))))
	 (args tterm.args)
	 ((unless
	   (if (equal fn 'if)
	       (and (consp (cddr args))
		    (not (cdddr args)))
	       (and (symbolp fn)
		    (not (booleanp fn)))))
	  nil)
	 ((unless (match-len tterm.args (cdr term))) nil))
       (ttmrg-args-syntax-p tterm.args)))

  (define ttmrg-args-syntax-p ((ttargs acl2::any-p))
    :returns (ok booleanp)
    :measure (list (acl2-count ttargs) 0)
    :flag args
    (if (consp ttargs)
      (and (ttmrg-syntax-p (car ttargs))
	   (ttmrg-args-syntax-p (cdr ttargs)))
      (not ttargs)))
  ///
  (more-returns ttmrg-syntax-p
    (ok :name ttmrg-p-when-ttmrg-syntax-p
	(implies ok (ttmrg-p tterm))
	:rule-classes (:rewrite :forward-chaining))
    (ok :name ttmrg-syntax-p-of-if
	(implies (and ok (equal (car (ttmrg->term tterm)) 'if))
		 (and (consp (ttmrg->args tterm))
		      (consp (cdr (ttmrg->args tterm)))
		      (consp (cddr (ttmrg->args tterm)))
		      (not (cdddr (ttmrg->args tterm)))))))

  (more-returns ttmrg-args-syntax-p
    (ok :name ttmrg-list-p-when-ttmrg-args-syntax-p
	(implies ok (ttmrg-list-p ttargs))
	:hints(("Goal"
          :in-theory (enable ttmrg-args-syntax-p ttmrg-list-p)
	  :induct (len ttargs)))
	:rule-classes (:rewrite :forward-chaining))
    (ok :name ttmrg-args-syntax-p-of-cdr
	(implies ok (ttmrg-args-syntax-p (cdr ttargs))))))

(defsection ttmrg-correct
  (define ttmrg-args-correct-values ((ttargs ttmrg-list-p)
				     (args pseudo-term-listp)
				     (env alistp))
    :returns (ok booleanp)
    (if (and (consp ttargs) (consp args))
      (and (implies (ev-smtcp (ttmrg->path-cond (car ttargs)) env)
			      (equal (ev-smtcp (ttmrg->term (car ttargs)) env)
				     (ev-smtcp (car args) env)))
	   (ttmrg-args-correct-values (cdr ttargs) (cdr args) env))
      (not (or ttargs args))))

  ; (ttmrg-args-correct-path args env): test that the path-cond for each
  ;  element of args hold in env.
  ;  Use: args is the argument list for some function call (other than
  ;  'quote or 'if).  Our caller should check that the path-cond of this
  ;  function-call holds.  Then, (ttmrg-args-correct-path args env)
  ;  establishes that the path-cond for the function-call implies the
  ;  path-cond for each element of args.
  (define ttmrg-args-correct-path ((ttargs ttmrg-list-p) (env alistp))
    :returns (ok booleanp)
    (or (atom ttargs)
      (and (ev-smtcp (ttmrg->path-cond (car ttargs)) env)
	   (ttmrg-args-correct-path (cdr ttargs) env))))

  (acl2::define-sk ttmrg-correct-sk ((tterm acl2::any-p))
    :guard-hints(("Goal" :in-theory (enable ttmrg-syntax-p)))
    :returns (ok booleanp)
    (forall env
      (b* (((unless (ttmrg-syntax-p tterm)) nil)
	   ((unless (alistp env)) t)
	   ((ttmrg tterm) tterm)
	   ; All typed-terms must satisfy path-cond implies judgements
	   ((unless (ev-smtcp tterm.path-cond env)) t)
	   ((unless (ev-smtcp tterm.top-judgement env)) nil)
	   ((if (or (atom tterm.term) (equal (car tterm.term) 'quote))) t))
	(and ; tterm is a function call 
	  (ttmrg-args-correct-values tterm.args (cdr tterm.term) env)
	  (if (equal (car tterm.term) 'if)
	    (b* (((list (ttmrg condx) (ttmrg thenx) (ttmrg elsex))
		  tterm.args))
	      (and (ev-smtcp condx.path-cond env)
		   (if (ev-smtcp condx.term env)
		     (ev-smtcp thenx.path-cond env)
		     (ev-smtcp elsex.path-cond env))))
	    (ttmrg-args-correct-path tterm.args env))))))
  
  (defrule syntax-p-when-ttmrg-correct-sk
    (implies (ttmrg-correct-sk tterm)
	     (ttmrg-syntax-p tterm))
    :rule-classes (:rewrite :forward-chaining)
    :in-theory (enable ttmrg-correct-sk))

  (defines ttmrg-correct
    :well-founded-relation l<
    :flag-local nil
    (define ttmrg-correct-p ((tterm acl2::any-p))
      :measure (list (acl2-count tterm) 1)
      :returns (ok booleanp)
      :flag term
      (b* (((unless (ttmrg-correct-sk tterm)) nil)
	   (term (ttmrg->term tterm))
	   ((unless (consp term)) t)
	   ((cons fn &) term)
	   ((if (equal fn 'quote)) t))
	 (ttmrg-args-correct-p (ttmrg->args tterm))))

    (define ttmrg-args-correct-p ((ttargs ttmrg-list-p))
      :measure (list (acl2-count ttargs) 0)
      :returns (ok booleanp)
      :flag args
      (b* (((unless (consp ttargs)) (null ttargs))
	   ((cons hd tl) ttargs))
	  (and (ttmrg-correct-p hd)
	       (ttmrg-args-correct-p tl))))
    ///
    (more-returns ttmrg-correct-p
      (ok :name ttmrg-syntax-p-when-ttmrg-correct-p
	  (implies ok (ttmrg-syntax-p tterm))
	  :rule-classes (:rewrite :forward-chaining)
	  :hints(("Goal" :expand ((ttmrg-correct-p tterm)))))
      (ok :name ttmrg-p-when-ttmrg-correct-p
        (implies ok (ttmrg-p tterm))
	:rule-classes (:rewrite :forward-chaining))
      (ok :name ttmrg-args-correct-p-when-ttmrg-correct-p
	(implies ok (ttmrg-args-correct-p (ttmrg->args tterm)))
	:rule-classes ((:rewrite) (:forward-chaining) (:type-prescription))
	:hints(("Goal"
	  :use((:instance ttmrg-syntax-p))
	  :expand (ttmrg-correct-p tterm)))))
    (more-returns ttmrg-args-correct-p
      (ok :name ttmrg-args-syntax-p-when-ttmrg-args-correct-p
	(implies ok (ttmrg-args-syntax-p ttargs))
	:rule-classes (:rewrite :forward-chaining)
	:hints(("Goal"
	  :induct (len ttargs)
	  :in-theory (enable ttmrg-args-syntax-p))))
      (ok :name ttmrg-list-p-when-ttmrg-args-correct-p
	(implies ok (ttmrg-list-p ttargs))
	:rule-classes (:rewrite :forward-chaining)
	:hints(("Goal"
	  :induct (len ttargs)
	  :in-theory (enable ttmrg-list-p))))
      (ok :name ttmrg-args-correct-p-of-cdr
	(implies ok (ttmrg-args-correct-p (cdr ttargs))))
      (ok :name member-when-ttmrg-args-correct-p
	(implies (and ok (member-equal ttarg ttargs))
		 (ttmrg-correct-p ttarg))
	:hints(("Goal" :in-theory (enable member-equal)))))

    (deflabel start-ttmrg-correct-sk-thms)
    (defrule ttmrg-correct-sk-when-ttmrg-correct-p
      (implies (ttmrg-correct-p tterm)
	       (ttmrg-correct-sk tterm))
      :expand (ttmrg-correct-p tterm))

    (defrule ttmrg->top-judgement-when-ttmrg-correct-sk
      (implies (and (ttmrg-correct-sk tterm)
		    (alistp env)
		    (ev-smtcp (ttmrg->path-cond tterm) env))
	       (ev-smtcp (ttmrg->top-judgement tterm) env))
      :use ((:instance ttmrg-correct-sk-necc))
      :rule-classes ((:rewrite :match-free :all)))

    (defrule ttmrg-args-correct-values-when-ttmrg-correct-sk
      (implies (and (ttmrg-correct-sk tterm)
		    (alistp env)
		    (ev-smtcp (ttmrg->path-cond tterm) env)
		    (consp (ttmrg->term tterm))
		    (not (equal (car (ttmrg->term tterm)) 'quote)))
	       (ttmrg-args-correct-values (ttmrg->args tterm)
					  (cdr (ttmrg->term tterm)) env))
      :use((:instance ttmrg-correct-sk-necc)))

    (defrule ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk
      (implies (and (ttmrg-correct-sk tterm)
		    (alistp env)
		    (ev-smtcp (ttmrg->path-cond tterm) env)
		    (consp (ttmrg->term tterm))
		    (equal (car (ttmrg->term tterm)) 'if))
	       (and (ev-smtcp (ttmrg->path-cond (car (ttmrg->args tterm))) env)
		    (if (ev-smtcp (ttmrg->term (car (ttmrg->args tterm))) env)
		      (ev-smtcp (ttmrg->path-cond (cadr (ttmrg->args tterm))) env)
		      (ev-smtcp (ttmrg->path-cond (caddr (ttmrg->args tterm))) env))))
      :use((:instance ttmrg-correct-sk-necc)))

    (defrule ttmrg-args-correct-path-when-ttmrg-correct-sk
      (implies (and (ttmrg-correct-sk tterm)
		    (alistp env)
		    (ev-smtcp (ttmrg->path-cond tterm) env)
		    (consp (ttmrg->term tterm))
		    (not (equal (car (ttmrg->term tterm)) 'quote))
		    (not (equal (car (ttmrg->term tterm)) 'if)))
	       (ttmrg-args-correct-path (ttmrg->args tterm) env))
      :use((:instance ttmrg-correct-sk-necc)))
    (deftheory ttmrg-correct-sk-thms
      (set-difference-theories
	(current-theory :here)
	(current-theory 'start-ttmrg-correct-sk-thms)))
    (in-theory (disable ttmrg-correct-sk-thms
			member-when-ttmrg-args-correct-p))))


; Type inference can update various fields of the ttmrg values while
; preserving the function call structure.  ttmrg-simple-count is a measure
; function that is based on the function call structure of a ttmrg and
; ignores the other fields.
(defines ttmrg-simple-count
  :flag-local nil
  (define ttmrg-simple-count ((tterm ttmrg-p))
    :returns (m natp)
    :flag term
    :measure (ttmrg-count tterm)
    (1+ (ttmrg-args-simple-count (ttmrg->args tterm))))

  (define ttmrg-args-simple-count ((ttargs ttmrg-list-p))
    :returns (m natp)
    :flag args
    :measure (ttmrg-list-count ttargs)
    (if (consp ttargs)
      (+ 1 (ttmrg-simple-count (car ttargs))
	 (ttmrg-args-simple-count (cdr ttargs)))
      0))
  ///
  (more-returns ttmrg-simple-count
    (m :name ttmrg-args-simple-count-of-ttmrg->args-<-ttmrg-simple-count-of-term
      (< (ttmrg-args-simple-count (ttmrg->args tterm)) m)))

  (more-returns ttmrg-args-simple-count
    (m :name ttmrg-simple-count-of-car-<-ttmrg-args-simple-count
      (implies (consp ttargs)
	       (< (ttmrg-simple-count (car ttargs)) m))
      :hints(("Goal"
	:expand ((ttmrg-args-simple-count ttargs)))))
    (m :name ttmrg-simple-count-of-cdr-<-ttmrg-args-simple-count
      (implies (consp ttargs)
	       (< (ttmrg-args-simple-count (cdr ttargs)) m))
      :hints(("Goal"
	:expand ((ttmrg-args-simple-count ttargs))))))

  (defthm-ttmrg-simple-count-flag
    (defthm ttmrg-simple-count-of-ttmrg-fix
      (equal (ttmrg-simple-count (ttmrg-fix tterm))
	     (ttmrg-simple-count tterm))
      :flag term)
    (defthm ttmrg-args-simple-count-of-ttmrg-list-fix
      (equal (ttmrg-args-simple-count (ttmrg-list-fix ttargs))
	     (ttmrg-args-simple-count ttargs))
      :flag args)
    :hints(("Goal"
      :in-theory (enable ttmrg-fix ttmrg-list-fix
			 ttmrg-simple-count ttmrg-args-simple-count)))))


; pseudo-term-syntax-p recognizes pseudo-terms that satisfy the constraints
;   we have for ttmrg-syntax-p: no lambada; 't, 'nil, cannot be used as
;   function names; the 'quote function must have exactly one argument;
;   and the 'if function must have exactly three arguments.
(defines pseudo-term-syntax
  :flag-local nil ; pseudo-term-syntax-p and pseudo-term-list-syntax-p
                  ; provide a more efficient induction schema than
		  ; pseudo-termp and pseudo-term-listp
  (define pseudo-term-syntax-p ((term acl2::any-p))
    :returns (ok booleanp)
    :flag term
    (b* (((unless (consp term)) (symbolp term))
	 ((cons fn args) term)
	 ((if (equal fn 'quote))
	  (and (consp args) (null (cdr args))))
	 ((unless (symbolp fn)) nil)
	 ((if (booleanp fn)) nil)
	 ((if (and (equal fn 'if)
		   (not (and (consp args) (consp (cdr args))
			     (consp (cddr args)) (null (cdddr args))))))
	  nil))
       (pseudo-term-list-syntax-p args)))

  (define pseudo-term-list-syntax-p ((args acl2::any-p))
    :returns (ok booleanp)
    :flag args
    (b* (((unless (consp args)) (null args))
	 ((cons hd tl) args))
       (and (pseudo-term-syntax-p hd)
	    (pseudo-term-list-syntax-p tl))))

  ///
  (defthm-pseudo-term-syntax-flag
    (defthm pseudo-termp-when-pseudo-term-syntax-p
      (implies (pseudo-term-syntax-p term) (pseudo-termp term))
      :rule-classes (:rewrite :forward-chaining)
      :flag term)
    (defthm pseudo-term-listp-when-pseudo-term-list-syntax-p
      (implies (pseudo-term-list-syntax-p args) (pseudo-term-listp args))
      :rule-classes (:rewrite :forward-chaining)
      :flag args)
    :hints(("Goal" :in-theory (enable pseudo-termp pseudo-term-listp)))))

(defines pseudo-term-syntax-fix
  :verify-guards nil
  :returns-hints(("Goal" :in-theory (enable pseudo-term-syntax-p pseudo-term-list-syntax-p)))
  (define pseudo-term-syntax-fix ((term pseudo-term-syntax-p))
    :returns (term-fix pseudo-term-syntax-p)
    :flag term
    (mbe :exec term
	 :logic (b* (((unless (consp term))
		      (and (symbolp term) term))
		     ((cons fn args) term)
		     ((if (equal fn 'quote))
		      (and (consp args) (null (cdr args)) term))
		     (fn-fix
		      (cond ((and (consp fn) (equal (car fn) 'lambda))
				'unexpected-lambda-expression)
			    ((not (symbolp fn)) 'garbled-term)
			    ((booleanp fn)
			     (if fn 'invalid-use-of-t-as-function
				    'invalid-use-of-nil-as-function))
			    ((and (equal fn 'if)
				  (or (not (consp (cddr args)))
				      (cdddr args)))
			     'bad-if)
			    (t fn)))
		     (args-fix (pseudo-term-list-syntax-fix args)))
		  (cons fn-fix args-fix))))

  (define pseudo-term-list-syntax-fix ((args pseudo-term-list-syntax-p))
    :returns (args-fix pseudo-term-list-syntax-p)
    :flag args
    (mbe :exec args
	 :logic
	   (if (consp args)
	     (cons (pseudo-term-syntax-fix (car args))
		   (pseudo-term-list-syntax-fix (cdr args)))
	     nil)))
  ///

  (defthm-pseudo-term-syntax-fix-flag
    (defthm pseudo-term-syntax-fix-when-pseudo-term-syntax-p
      (implies (pseudo-term-syntax-p term)
	       (equal (pseudo-term-syntax-fix term) term))
      :flag term)
    (defthm pseudo-term-list-syntax-fix-when-pseudo-term-list-syntax-p
      (implies (pseudo-term-list-syntax-p args)
	       (equal (pseudo-term-list-syntax-fix args) args))
      :flag args)
    :hints(("Goal" :in-theory (enable pseudo-term-syntax-p
				      pseudo-term-list-syntax-p))))

  (verify-guards pseudo-term-syntax-fix
    :hints(("Goal" :in-theory (enable pseudo-term-syntax-p
				      pseudo-term-list-syntax-p))))

  (defthm-pseudo-term-syntax-fix-flag
    (defthm acl2-count-of-pseudo-term-syntax-fix
      (<= (acl2-count (pseudo-term-syntax-fix term))
	  (acl2-count term))
      :flag term)
    (defthm acl2-count-of-pseudo-term-list-syntax-fix
      (<= (acl2-count (pseudo-term-list-syntax-fix args))
	  (acl2-count args))
      :flag args)))
