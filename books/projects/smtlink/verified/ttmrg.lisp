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
       (judgements conj-p :default ''t)))

    (deflist ttmrg-list
      :elt-type ttmrg-p
      :true-listp t
      :measure (list (acl2-count x) 0)))


  (acl2::defrule term->args-smaller-than-term
    (implies (ttmrg-p tterm)
	     (< (acl2-count (ttmrg->args tterm))
		(acl2-count tterm)))
    :expand ((ttmrg->args tterm)
	     (ttmrg-p tterm)))

  (define ttmrg->top-judgement ((tterm ttmrg-p))
    :returns (j pseudo-termp)
    (b* (((ttmrg tterm) (ttmrg-fix tterm))
	 (term tterm.term)
	 ((unless (and (consp term) (not (equal (car term) 'quote))))
	  tterm.judgements)
	 ((unless (conj-consp tterm.judgements)) ''t))
       (conj-car tterm.judgements)))

  (define ttmrg->args-judgement ((tterm ttmrg-p))
    :returns (j conj-p)
    (b* (((ttmrg tterm) (ttmrg-fix tterm))
	 (term tterm.term)
	 ((unless (and (consp term) (not (equal (car term) 'quote)))) ''t)
	 ((unless (conj-consp tterm.judgements)) ''t))
       (conj-cdr tterm.judgements)))

  (define ttmrg-list->terms ((args ttmrg-list-p))
    :returns (terms pseudo-term-listp)
    (b* (((unless (consp args)) nil)
	 ((cons hd tl) args))
       (cons (ttmrg->term hd)
	     (ttmrg-list->terms tl))))

  (define ttmrg-list->judgements ((args ttmrg-list-p))
    :returns (judgements conj-p)
    (b* (((unless (consp args)) ''t)
	 ((cons hd tl) args))
       (conj-cons (ttmrg->judgements hd)
		  (ttmrg-list->judgements tl)))))

(defsection ttmrg-syntax
  (define args-path-cond-match-parent ((path-cond conj-p) (args ttmrg-list-p))
    :returns (ok booleanp)
    (if (consp args)
      (and (equal (ttmrg->path-cond (car args)) path-cond)
	   (args-path-cond-match-parent path-cond (cdr args)))
      t))

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
	    </li>
	    <li>If @('(car (ttmrg->term tterm))') is the symbol @(''if'),
	      then the @('args') field must have length three, and
	      the @('path-cond') field for @('(car args)') must be the same as
	      the @('path-cond') for this @('ttmrg').
	      We don't constrain the @('path-cond')for the other two elements
	      of @('args') -- that's a semantic constraint addressed by
	      @(see ttmrg-correct).
	    </li>
	    <li>If @('(car (ttmrg->term tterm))') is a symbol other than
	      <tt>'if</tt>, <tt>'t</tt> or <tt>'nil</tt> then the each element
	      of the @('args') field must have the same @('path-cond') as this
	      @('ttmrg').
	    </li>
	    <li>A @(see ttmrg) that satisfies @('ttmrg-syntax-p')
	      cannot be a lambda expression.  All lambdas in the goal should have
	      been flattened in the expand-clause-processor. This simplifies the
	      implementation of the remaining Smtlink clause-processors.
	    </li>
        </ul>
      </p>"
      (b* (((unless (ttmrg-p tterm)) nil)
	   ((ttmrg tterm) tterm)
	   (term tterm.term)
	   ((if (atom term)) (null tterm.args))
	   (fn (car term))
	   ((if (equal fn 'quote)) (null tterm.args))
	   (args tterm.args)
	   (path-cond tterm.path-cond)
	   ((unless (conj-consp tterm.judgements)) nil)
	   ((unless (conj-conj-p tterm.judgements)) nil)
	   ((unless
	     (if (equal fn 'if)
		 (and (consp (cddr args))
		      (not (cdddr args))
		      (equal (ttmrg->path-cond (car args)) path-cond))
		 (and (symbolp fn)
		      (not (booleanp fn))
		      (args-path-cond-match-parent path-cond args))))
	    nil))
	 (ttmrg-args-syntax-p
	   (cdr term)
	   tterm.args
	   (conj-cdr tterm.judgements))))

    (define ttmrg-args-syntax-p ((args pseudo-term-listp)
				 (typed-args ttmrg-list-p)
				 (jargs conj-conj-p))
      :returns (ok booleanp)
      :measure (list (acl2-count typed-args) 0)
      :flag args
      (if (consp args)
	(and (consp typed-args)
	     (conj-consp jargs)
	     (equal (ttmrg->term (car typed-args))
		    (car args))
	     (ttmrg-syntax-p (car typed-args))
	     (ttmrg-args-syntax-p
	       (cdr args)
	       (cdr typed-args)
	       (conj-cdr jargs)))
	(and (not args)
	     (not typed-args)
	     (equal jargs ''t))))
    ///

    (more-returns ttmrg-syntax-p
      (ok :name ttmrg-p-when-ttmrg-syntax-p
	  (implies ok (ttmrg-p tterm))
	  :rule-classes (:rewrite :forward-chaining))
      (ok :name conj-conj-p-of-ttmrg-p->judgements
	  (implies (and ok
			(consp (ttmrg->term tterm))
			(not (equal (car (ttmrg->term tterm)) 'quote)))
		   (conj-conj-p (ttmrg->judgements tterm))))
      (ok :name conj-p-of-ttmrg->top-judgement-when-ttmrg-syntax-p
	(implies ok (conj-p (ttmrg->top-judgement tterm)))
	:hints(("Goal" :in-theory (enable ttmrg->top-judgement))))
      (ok :name conj-conj-p-of-ttmrg->args-judgement-when-ttmrg-syntax-p
	(implies ok (conj-conj-p (ttmrg->args-judgement tterm)))
	:hints(("Goal"
	  :in-theory (enable ttmrg->args-judgement)
	  :expand ((ttmrg-syntax-p tterm))))))

    (defrule conj-car/cdr-of-ttmrg->top-args-judgement-when-ttmrg-syntax-p
      (implies (and (ttmrg-syntax-p tterm)
		    (consp (ttmrg->term tterm))
		    (not (equal (car (ttmrg->term tterm)) 'quote)))
	       (equal (conj-cons (ttmrg->top-judgement tterm)
				 (ttmrg->args-judgement tterm))
		      (ttmrg->judgements tterm)))
      :in-theory (disable conj-cons-car-cdr foo-lemma)
      :use((:instance conj-cons-car-cdr (x (TTMRG->JUDGEMENTS TTERM)))
	   (:instance foo-lemma (args (cdr (ttmrg->term tterm)))
				(typed-args (ttmrg->args tterm))
				(jargs (conj-cdr (ttmrg->judgements tterm)))))
      :expand ((ttmrg-syntax-p tterm)
	       (ttmrg->top-judgement tterm)
	       (ttmrg->args-judgement tterm)
	       (foo-p (cdr (ttmrg->term tterm))
				    (ttmrg->args tterm)
				    (conj-cdr (ttmrg->judgements tterm))))
      :prep-lemmas(
	; foo-p gives us the induction schema we need to prove foo-lemma:
	;   ttmrg-args-syntax-p establishes that the conj structure of
	;   tterm.judgements matches the cons structure of args and typed-args.
	(define foo-p ((args pseudo-term-listp) (typed-args ttmrg-list-p) (jargs conj-p))
	  :returns (ok booleanp)
	  (if (and (consp args) (consp typed-args) (conj-consp jargs))
	    (foo-p (cdr args) (cdr typed-args) (conj-cdr jargs))
	    (and (equal args nil) (equal typed-args nil)(equal jargs ''t)))
	  ///
	  (more-returns
	    (ok :name foo-lemma
	      (implies (ttmrg-args-syntax-p args typed-args jargs) ok)))))))

  (define ttmrg-list-syntax-p ((ttlst acl2::any-p))
    :returns (ok booleanp)
    (if (consp ttlst)
      (and (ttmrg-syntax-p (car ttlst))
	   (ttmrg-list-syntax-p (cdr ttlst)))
      (not ttlst))
    ///
    (more-returns
      (ok :name ttmrg-list-p-when-ttmrg-list-syntax-p
	  (implies ok (ttmrg-list-p ttlst))
	  :hints(("Goal" :in-theory (enable ttmrg-list-p)))
	  :rule-classes (:rewrite :forward-chaining))
      (ok :name ttmrg-list-syntax-p-of-cdr
	  (implies ok (ttmrg-list-syntax-p (cdr ttlst)))
	  :hints(("Goal" :in-theory (enable ttmrg-list-syntax-p))))))

  (defthm-ttmrg-syntax-flag
    (defthm ttmrg-syntax-p-implies-ttmrg-list-p
      (implies (ttmrg-syntax-p tterm) (ttmrg-list-syntax-p (ttmrg->args tterm)))
      :flag term)
    (defthm ttmrg-args-syntax-p-implies-ttmrg-list-p
      (implies (ttmrg-args-syntax-p args typed-args jargs)
	       (ttmrg-list-syntax-p typed-args))
      :flag args
      :skip t)
      :hints(("Goal" :in-theory (enable ttmrg-syntax-p ttmrg-args-syntax-p ttmrg-list-syntax-p)))))


(defsection ttmrg-correct
  (acl2::define-sk ttmrg-correct-sk ((tterm ttmrg-syntax-p))
    :guard-hints(("Goal" :in-theory (enable ttmrg-syntax-p)))
    :returns (ok booleanp)
    (forall a
      (implies (alistp a)
        (b* (((unless (mbt (ttmrg-syntax-p tterm))) nil)
	     ((ttmrg tterm) tterm)
	     (term tterm.term)
	     ((unless
	       (implies
		 (and (consp term) (equal (car term) 'if))
		 (b* ((path-cond tterm.path-cond)
		      ((list condx thenx elsex) tterm.args))
		   (and (implies (and (ev-smtcp path-cond a)
				      (ev-smtcp (ttmrg->term condx) a))
				 (ev-smtcp (ttmrg->path-cond thenx) a))
			(implies (and (ev-smtcp path-cond a)
				      (not (ev-smtcp (ttmrg->term condx) a)))
				 (ev-smtcp (ttmrg->path-cond elsex) a))))))
	      nil))
	  (implies (ev-smtcp (ttmrg->path-cond tterm) a)
		   (ev-smtcp (ttmrg->judgements tterm) a))))))

  (defines ttmrg-correct
    :well-founded-relation l<
    :flag-local nil
    (define ttmrg-correct-p ((tterm acl2::any-p))
      :measure (list (acl2-count tterm) 1)
      :returns (ok booleanp)
      :flag term
      (b* (((unless (ttmrg-syntax-p tterm)) nil)
	   ((unless (ttmrg-correct-sk tterm)) nil)
	   (term (ttmrg->term tterm))
	   ((unless (consp term)) t)
	   ((cons fn &) term)
	   ((if (equal fn 'quote)) t))
	 (ttmrg-args-correct-p (ttmrg->args tterm))))

    (define ttmrg-args-correct-p ((typed-args acl2::any-p))
      :measure (list (acl2-count typed-args) 0)
      :returns (ok booleanp)
      :flag args
      (b* (((unless typed-args) t)
	   ((unless (ttmrg-list-syntax-p typed-args)) nil)
	   ((cons hd tl) typed-args))
	  (and (ttmrg-correct-p hd)
	       (ttmrg-args-correct-p tl))))
    ///
    (more-returns ttmrg-correct-p
      (ok :name ttmrg-syntax-p-when-ttmrg-correct-p
	  (implies ok (ttmrg-syntax-p tterm))
	  :rule-classes (:rewrite :forward-chaining))
      (ok :name ttmrg-p-when-ttmrg-correct-p
        (implies ok (ttmrg-p tterm))
	:rule-classes (:rewrite :forward-chaining)))))

; pseudo-term-syntax-p recognizes pseudo-terms that satisfy the constraints
;   we have for ttmrg-syntax-p: no lambada; 't, 'nil, cannot be used as
;   function names; the 'quote function must have exactly one argument;
;   and the 'if function must have exactly three arguments.
(defines pseudo-term-syntax
  :flag-local nil ; pseudo-term-syntax-p and pesudo-term-list-syntax-p
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
