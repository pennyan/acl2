;; Copyright (C) 2021, University of British Columbia
;; Written by Mark Greenstreet (December 15th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

; ttmrg-change.lisp
;   Functions that preserve ttmrg-correct-p when updating one or more
;   fields of a ttmrg-p term.

(include-book "ttmrg")

(set-state-ok t)
(set-induction-depth-limit 1)

(local (in-theory (disable ; mark is impatient
  consp-of-pseudo-lambdap pseudo-termp pseudo-lambdap-of-fn-call-of-pseudo-termp
  acl2::pseudo-lambdap-of-car-when-pseudo-termp symbol-listp alistp member-equal)))


(local (encapsulate nil
  ; A few properties of ttmrg-syntax-p.  I'm guessing they won't be    ;
  ; needed in other books.  So, I'm making them local to avoid         ;
  ; cluttering the logical world.;

  (local (in-theory (enable ttmrg-syntax-p)))
  (defrule ttmrg-syntax-p-of-change-term-other-than-fncall
    (implies (and (ttmrg-syntax-p tterm)
		  (pseudo-termp new-term)
		  (or (not (consp (ttmrg->term tterm)))
		      (equal (car (ttmrg->term tterm)) 'quote))
		  (or (not (consp new-term))
		      (equal (car new-term) 'quote)))
	     (ttmrg-syntax-p (change-ttmrg tterm :term new-term)))
    :in-theory (enable pseudo-termp))

  (defrule ttmrg-syntax-p-of-change-args
    (implies (and (ttmrg-syntax-p tterm)
		  (ttmrg-args-syntax-p new-args)
		  (match-len new-args (ttmrg->args tterm)))
	     (ttmrg-syntax-p (change-ttmrg tterm :args new-args)))
    :in-theory (enable match-len))

  (defrule ttmrg-syntax-p-of-change-top-judgement
    (implies (and (ttmrg-syntax-p tterm)
		  (conj-p new-top-judge))
	     (ttmrg-syntax-p (change-ttmrg tterm :top-judgement new-top-judge))))

  (defrule ttmrg-syntax-p-of-change-path-cond
    (implies (and (ttmrg-syntax-p tterm)
		  (conj-p new-path-cond))
	     (ttmrg-syntax-p (change-ttmrg tterm :path-cond new-path-cond))))
  (local (in-theory (disable ttmrg-syntax-p)))))

(local (in-theory (enable ttmrg-correct-sk-thms)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                                      ;
;  Functions for updating the top judgement of a ttmrg-p:              ;
;    constrain-ttmrg->top-judge:  constraints for a safe update        ;
;    change-ttmrg->top-judgement:                                      ;
;      Update top-judgement using constrain-ttmrg->top-judge.          ;
;      We prove that change-ttmrg->top-judgement preserves             ;
;      ttmrg-correct-p.                                                ;
;    ttmrg-only->changed-judgements:                                   ;
;      macro that generates the predicate that says all fields other   ;
;        than the judgements field are unchanged.                      ;
;                                                                      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate (((constrain-ttmrg->top-judgement * state) => *))
  (local (define constrain-ttmrg->top-judgement
	     ((tterm ttmrg-p) (state state-p))
	   :enabled t
	   :ignore-ok t
	   :irrelevant-formals-ok t
	   ''t))

  (defrule conj-p-of-constrain-ttmrg->top-judgement
    (conj-p (constrain-ttmrg->top-judgement tterm state)))

  (defrule correctness-of-constrain-ttmrg->top-judgement
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (alistp env)
		  (ev-smtcp (ttmrg->path-cond tterm) env))
	     (ev-smtcp (constrain-ttmrg->top-judgement tterm state) env))))

(define change-ttmrg->top-judgement ((tterm ttmrg-p) (new-top-judge conj-p))
  :returns (new-tt ttmrg-p)
  (change-ttmrg (ttmrg-fix tterm) :top-judgement (conj-fix new-top-judge))
  ///
  (defmacro ttmrg-only-changed->top-judgement (old-tt new-tt)
    `(and (equal (ttmrg->term ,new-tt)
		 (ttmrg->term ,old-tt))
	  (equal (ttmrg->args ,new-tt)
		 (ttmrg->args ,old-tt))
	  (equal (ttmrg->path-cond ,new-tt)
		 (ttmrg->path-cond ,old-tt))))
  (more-returns
    (new-tt :name change-ttmrg->top-judgement--unchanged-fields
      (ttmrg-only-changed->top-judgement tterm new-tt)))

  (defrule ttmrg-syntax-p-of-change-ttmrg->top-judgement
    (implies (ttmrg-syntax-p tterm)
	     (ttmrg-syntax-p (change-ttmrg->top-judgement tterm new-top-judge)))
    :in-theory (disable ttmrg-syntax-p-of-change-top-judgement)
    :use((:instance ttmrg-syntax-p-of-change-top-judgement
		      (new-top-judge (conj-fix new-top-judge)))))

  (defrule correctness-of-change-ttmrg->top-judgement
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (ttmrg-correct-p tterm))
	     (ttmrg-correct-p
	       (change-ttmrg->top-judgement
		 tterm
		 (constrain-ttmrg->top-judgement tterm state))))
    :in-theory (e/d (ttmrg-correct-sk)
		    (change-ttmrg->top-judgement))
    :expand ((ttmrg-correct-p (change-ttmrg->top-judgement
				tterm
				(constrain-ttmrg->top-judgement tterm state))))
    :prep-lemmas(
      (defrule top-judgement-of-change-ttmrg->top-judgement
	(equal (ttmrg->top-judgement
		 (change-ttmrg->top-judgement
		   tterm
		   (constrain-ttmrg->top-judgement tterm state)))
	       (constrain-ttmrg->top-judgement tterm state))))))


(define strengthen-ttmrg->top-judgement ((tterm ttmrg-syntax-p) (new-top-judge conj-p))
  :returns (new-tt ttmrg-p)
  (change-ttmrg->top-judgement tterm
			       (conj-cons2 new-top-judge
					   (ttmrg->top-judgement tterm)))
  ///
  (more-returns
    (new-tt :name ttmrg-syntax-p-of-strengthen-ttmrg->top-judgement
      (implies (ttmrg-syntax-p tterm)
	       (ttmrg-syntax-p new-tt)))
    (new-tt :name strengthen-ttmrg->top-judge--unchanged-fields
      (ttmrg-only-changed->top-judgement tterm new-tt)))

  (defrule correctness-of-strengthen-ttmrg->top-judgement
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (ttmrg-correct-p tterm))
	     (ttmrg-correct-p
	       (strengthen-ttmrg->top-judgement
		 tterm
		 (constrain-ttmrg->top-judgement tterm state))))
    :in-theory (enable strengthen-ttmrg->top-judgement)
    :use((:functional-instance correctness-of-change-ttmrg->top-judgement
	    (constrain-ttmrg->top-judgement
	      (lambda (tterm state)
		(conj-cons2 (constrain-ttmrg->top-judgement tterm state)
			    (if (ttmrg-correct-p tterm)
			      (ttmrg->top-judgement tterm)
			      ''t))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                                      ;
;  Functions for updating the path-cond of a ttmrg-p:                  ;
;                                                                      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define strengthen-ttmrg->path-cond ((tterm ttmrg-p) (new-path-cond conj-p))
  :returns (new-tt ttmrg-p)
  (change-ttmrg tterm :path-cond
		(conj-cons2 new-path-cond (ttmrg->path-cond tterm)))
  ///
  (defmacro ttmrg-only-changed->path-cond (old-tt new-tt)
    `(and (equal (ttmrg->term ,new-tt)
		 (ttmrg->term ,old-tt))
	  (equal (ttmrg->args ,new-tt)
		 (ttmrg->args ,old-tt))
	  (equal (ttmrg->top-judgement ,new-tt)
		 (ttmrg->top-judgement ,old-tt))))
  (more-returns strengthen-ttmrg->path-cond
    (new-tt :name strengthen-ttmrg->path-cond--unchanged-fields
      (implies (ttmrg-p tterm)
	       (ttmrg-only-changed->path-cond tterm new-tt)))
    (new-tt :name strengthen-ttmrg->path-cond-does-what-its-name-says
      (implies (and (alistp env)
		    (ev-smtcp (ttmrg->path-cond new-tt) env))
	       (ev-smtcp (ttmrg->path-cond tterm) env))
      :rule-classes ((:rewrite :match-free :all))
      :hints(("Goal" :in-theory (enable conj-cons2))))
    (new-tt :name ev-smtcp-of-strengthen-ttmrg->path-cond
      (implies
	(and (alistp env)
	     (conj-p new-path-cond)
	     (ev-smtcp (ttmrg->path-cond tterm) env)
	     (ev-smtcp new-path-cond env))
	(ev-smtcp (ttmrg->path-cond new-tt) env))
      :hints(("Goal" :in-theory (enable conj-cons2))))
    (new-tt :name ttmrg-simple-count-of-strengthen-ttmrg->path-cond
	(equal (ttmrg-simple-count new-tt)
	       (ttmrg-simple-count tterm))
	:hints(("Goal"
	  :in-theory (enable strengthen-ttmrg->path-cond
			     ttmrg-simple-count)))))
  
  (local (in-theory (disable strengthen-ttmrg->path-cond)))
  (local (defrule syntax-p-of-strengthen-ttmrg->path-cond
    (implies (ttmrg-syntax-p tterm)
	     (ttmrg-syntax-p (strengthen-ttmrg->path-cond tterm new-path-cond)))
    :expand (
      (ttmrg-syntax-p tterm)
      (ttmrg-syntax-p (strengthen-ttmrg->path-cond tterm new-path-cond)))))

  (defrule correctness-of-strengthen-ttmrg->path-cond
    (implies (and (ttmrg-correct-p tterm)
		  (pseudo-termp new-path-cond))
	     (ttmrg-correct-p
	       (strengthen-ttmrg->path-cond
		 tterm
		 new-path-cond)))
    :in-theory (enable ttmrg-correct-sk)
    :expand ((ttmrg-correct-p (strengthen-ttmrg->path-cond
			        tterm
			        new-path-cond)))))


; updating the path-cond of a ttmrg-p is "easy".
; we now want to show conditions that ensure the update of the path-conds
; of the arguments to a function call preserve ttmrg-correct-p.
(define ttmrg-args->stronger-path-cond
	  ((old-ttargs ttmrg-list-p) (new-ttargs ttmrg-list-p) (env alistp))
  :returns (ok booleanp)
  (b* (((unless (and (consp old-ttargs) (consp new-ttargs)))
	(not (or (consp old-ttargs) (consp new-ttargs))))
       ((cons (ttmrg old-hd) old-tl) old-ttargs)
       ((cons (ttmrg new-hd) new-tl) new-ttargs)
       ((unless (ttmrg-only-changed->path-cond old-hd new-hd)) nil)
       ((unless (implies (ev-smtcp new-hd.path-cond env)
			 (ev-smtcp old-hd.path-cond env)))
	nil))
    (ttmrg-args->stronger-path-cond old-tl new-tl env)))

(defrule reflexivity-of-ttmrg-args->stronger-path-cond
  (ttmrg-args->stronger-path-cond args args env)
  :in-theory (enable ttmrg-args->stronger-path-cond))

(encapsulate (((constrain-ttmrg->args-path-cond * state) => *))
  (local (define constrain-ttmrg->args-path-cond
	     ((tterm ttmrg-p) (state state-p))
	   :enabled t
	   :ignore-ok t
	   :irrelevant-formals-ok t
	   (ttmrg-list-fix (ttmrg->args tterm))))

  (defrule ttmrg-list-p-of-constrain-ttmrg->args-path-cond
    (ttmrg-list-p (constrain-ttmrg->args-path-cond tterm state))
    :rule-classes (:rewrite :type-prescription))

  (defrule ttmrg-args->stronger-path-cond-of-constrain-ttmrg->args-path-cond
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (alistp env))
	     (ttmrg-args->stronger-path-cond
	       (ttmrg->args tterm)
	       (constrain-ttmrg->args-path-cond tterm state)
	       env))
    :in-theory (enable ttmrg-args->stronger-path-cond))

  (defrule ttmrg-args-correct-path-of-constrain-ttmrg->args-path-cond
    (implies
      (and (ev-smtcp-meta-extract-global-facts)
	   (ttmrg-correct-p tterm)
	   (alistp env)
	   (ev-smtcp (ttmrg->path-cond tterm) env)
	   (consp (ttmrg->term tterm))
	   (not (equal (car (ttmrg->term tterm)) 'quote)))
      (let ((new-ttargs (constrain-ttmrg->args-path-cond tterm state)))
	(if (equal (car (ttmrg->term tterm)) 'if)
	  (and (ev-smtcp (ttmrg->path-cond (car new-ttargs)) env)
	       (if (ev-smtcp (ttmrg->term (car new-ttargs)) env)
		 (ev-smtcp (ttmrg->path-cond (cadr new-ttargs)) env)
		 (ev-smtcp (ttmrg->path-cond (caddr new-ttargs)) env)))
	  (ttmrg-args-correct-path new-ttargs env))))
    :in-theory (disable ttmrg-args-correct-path-when-ttmrg-correct-sk)
    :use((:instance ttmrg-args-correct-path-when-ttmrg-correct-sk)
         (:instance ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk))))

(define change-ttmrg->args ((tterm ttmrg-p) (new-ttargs ttmrg-list-p))
  :returns (new-tt ttmrg-p)
  (change-ttmrg tterm :args new-ttargs)
  ///
  (defmacro ttmrg-only-changed->args (old-tt new-tt)
    `(and (equal (ttmrg->term ,new-tt)
		 (ttmrg->term ,old-tt))
	  (equal (ttmrg->top-judgement ,new-tt)
		 (ttmrg->top-judgement ,old-tt))
	  (equal (ttmrg->path-cond ,new-tt)
		 (ttmrg->path-cond ,old-tt))))
  (more-returns
    (new-tt :name change-ttmrg->args--unchanged-fields
      (implies (ttmrg-p tterm)
	       (ttmrg-only-changed->args tterm new-tt)))
    (new-tt :name ttmrg-syntax-p-of-change-ttmrg->args
      (implies (and (ttmrg-syntax-p tterm)
		    (ttmrg-args-syntax-p new-ttargs)
		    (match-len (double-rewrite new-ttargs)
			       (ttmrg->args (double-rewrite tterm))))
	       (ttmrg-syntax-p new-tt))
	  :hints(("Goal"
	    :in-theory (enable change-ttmrg->args ttmrg-syntax-p))))
    (new-tt :name ttmrg-args-simple-count-of-change-ttmrg->args
      (equal (ttmrg-args-simple-count (ttmrg->args new-tt))
	     (ttmrg-args-simple-count new-ttargs))
      :hints(("Goal"
	:in-theory (enable change-ttmrg->args ttmrg-args-simple-count))))))

(local (defrule match-len-of-constrain-ttmrg->args-path-cond
  (implies (ev-smtcp-meta-extract-global-facts)
	   (match-len (ttmrg->args tterm)
		      (constrain-ttmrg->args-path-cond tterm state)))
  :use((:instance match-len-when-ttmrg-args->stronger-path-cond
		    (old-ttargs (ttmrg->args tterm))
		    (new-ttargs (constrain-ttmrg->args-path-cond tterm state))
		    (env nil)))
  :prep-lemmas (
    (acl2::defruled match-len-when-ttmrg-args->stronger-path-cond
      (implies (ttmrg-args->stronger-path-cond old-ttargs new-ttargs env)
	       (match-len old-ttargs new-ttargs))
      :in-theory (enable ttmrg-args->stronger-path-cond match-len)))))

(defrule ttmrg-args-correct-p-of-constrain-ttmrg->args-path-cond
  (implies (and (ev-smtcp-meta-extract-global-facts)
		(ttmrg-correct-p tterm))
	   (ttmrg-args-correct-p
	     (constrain-ttmrg->args-path-cond tterm state)))
  :use((:instance ttmrg-args-correct-p-when-args-stronger-path
		    (old-ttargs (ttmrg->args tterm))
		    (new-ttargs (constrain-ttmrg->args-path-cond tterm state))))
  :prep-lemmas (
    (acl2::define-sk args-stronger-path
	((old-ttargs ttmrg-list-p) (new-ttargs ttmrg-list-p))
      :returns (ok booleanp)
      (forall (env)
	(implies (alistp env)
		 (ttmrg-args->stronger-path-cond old-ttargs new-ttargs env)))
      ///
      (defrule args-stronger-path-of-constrain-ttmrg->args-path-cond
	(implies (ev-smtcp-meta-extract-global-facts)
		 (args-stronger-path
		   (ttmrg->args tterm)
		   (constrain-ttmrg->args-path-cond tterm state))))

      (acl2::defrule ttmrg-only-changed->path-cond-when-args-stronger-path
	(implies (args-stronger-path old-ttargs new-ttargs)
		 (ttmrg-only-changed->path-cond (car old-ttargs)
						(car new-ttargs)))
	:rule-classes ((:rewrite :match-free :all))
	:use((:instance ttmrg-args->stronger-path-cond (env nil)))))

    (acl2::defruled correctness-of-new-car
      (implies (and (consp old-ttargs)
		    (ttmrg-args-correct-p old-ttargs)
		    (ttmrg-list-p new-ttargs)
		    (match-len new-ttargs old-ttargs)
		    (args-stronger-path old-ttargs new-ttargs))
	       (ttmrg-correct-p (car new-ttargs)))
      :expand (ttmrg-correct-p (car new-ttargs))
      :use((:instance ttmrg-args-correct-p (ttargs old-ttargs)))
      :prep-lemmas (
	(acl2::define-sk term-stronger-path ((old-tt ttmrg-p) (new-tt ttmrg-p))
	  :returns (ok booleanp)
	  (forall (env)
	    (implies (and (alistp env)
			  (ev-smtcp (ttmrg->path-cond new-tt) env))
		     (ev-smtcp (ttmrg->path-cond old-tt) env)))
	  ///
	  (acl2::defrule term-stronger-path-when-args-stronger-path
	    (implies (args-stronger-path old-ttargs new-ttargs)
		     (term-stronger-path (car old-ttargs) (car new-ttargs)))
	    :use((:instance args-stronger-path-necc
			      (old-ttargs old-ttargs)
			      (new-ttargs new-ttargs)
			      (env (term-stronger-path-witness (car old-ttargs)
							       (car new-ttargs))))
		 (:instance ttmrg-args->stronger-path-cond
			      (env (term-stronger-path-witness
				     (car old-ttargs) (car new-ttargs)))))))

	(defrule lemma-correct-sk
	  (implies
	    (and (ttmrg-correct-p tterm)
		 (ttmrg-p new-tt)
		 (ttmrg-only-changed->path-cond tterm new-tt)
		 (term-stronger-path tterm new-tt))
	    (ttmrg-correct-sk new-tt))
	  :in-theory (disable ttmrg-args-correct-values-when-ttmrg-correct-sk
			      ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk
			      ttmrg->top-judgement-when-ttmrg-correct-sk)
	  :expand (ttmrg-correct-sk new-tt)
	  :use((:instance ttmrg-syntax-p)
	       (:instance ttmrg-syntax-p (tterm new-tt))
	       (:instance ttmrg->top-judgement-when-ttmrg-correct-sk
			    (env (ttmrg-correct-sk-witness new-tt)))
	       (:instance ttmrg-args-correct-values-when-ttmrg-correct-sk
			    (env (ttmrg-correct-sk-witness new-tt)))
	       (:instance ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk
			    (env (ttmrg-correct-sk-witness new-tt)))
	       (:instance term-stronger-path-necc (old-tt tterm)
			    (env (ttmrg-correct-sk-witness new-tt)))))))

    (defrule args-stronger-path-of-cdr
      (implies (args-stronger-path old-ttargs new-ttargs)
	       (args-stronger-path (cdr old-ttargs) (cdr new-ttargs)))
      :use((:instance args-stronger-path-necc
			(env (args-stronger-path-witness (cdr old-ttargs) (cdr new-ttargs))))
	   (:instance args-stronger-path (old-ttargs (cdr old-ttargs)) (new-ttargs (cdr new-ttargs)))
	   (:instance ttmrg-args->stronger-path-cond
			(env (args-stronger-path-witness (cdr old-ttargs) (cdr new-ttargs))))))

    (acl2::defruled ttmrg-args-correct-p-when-args-stronger-path
      (implies (and (args-stronger-path old-ttargs new-ttargs)
		    (ttmrg-args-correct-p old-ttargs)
		    (ttmrg-list-p new-ttargs)
		    (match-len new-ttargs old-ttargs))
	       (ttmrg-args-correct-p new-ttargs))
      :in-theory (enable ttmrg-args->stronger-path-cond match-len)
      :prep-lemmas (
	(defrule lemma-*1/1
	  (implies (and (consp old-ttargs)
			(ttmrg-args-correct-p old-ttargs)
			(ttmrg-list-p new-ttargs)
			(match-len new-ttargs old-ttargs)
			(args-stronger-path old-ttargs new-ttargs)
			(implies (and (ttmrg-args-correct-p (cdr old-ttargs))
				      (ttmrg-list-p (cdr new-ttargs))
				      (match-len (cdr new-ttargs)
						 (cdr old-ttargs))
				      (args-stronger-path (cdr old-ttargs)
							  (cdr new-ttargs)))
				 (ttmrg-args-correct-p (cdr new-ttargs))))
		   (ttmrg-args-correct-p new-ttargs))
	  :expand (ttmrg-args-correct-p new-ttargs)
	  :use((:instance correctness-of-new-car)
	       (:instance match-len (l1 new-ttargs) (l2 old-ttargs))))))))

(defrule ttmrg-correct-p-of-change-ttmrg-args--strengthen-path-cond
  (implies (and (ev-smtcp-meta-extract-global-facts)
		(ttmrg-correct-p tterm))
	   (ttmrg-correct-p
	     (change-ttmrg->args tterm
	       (constrain-ttmrg->args-path-cond tterm state))))
  :in-theory (e/d (ttmrg-correct-sk)
		  (change-ttmrg->args
		   ttmrg-args-correct-path-of-constrain-ttmrg->args-path-cond))
  :expand ((ttmrg-correct-p (change-ttmrg->args
			      tterm
			      (constrain-ttmrg->args-path-cond tterm state))))
  :use((:instance ttmrg-args-correct-path-of-constrain-ttmrg->args-path-cond
		    (env (ttmrg-correct-sk-witness
			  (change-ttmrg->args tterm
			    (constrain-ttmrg->args-path-cond tterm state))))))
  :prep-lemmas (
    (defrule ttmrg->args-of-change-ttmrg->args
      (equal (ttmrg->args (change-ttmrg->args tterm new-ttargs))
	     (ttmrg-list-fix new-ttargs))
      :in-theory (enable change-ttmrg->args))

    (defrule lemma-values
      (implies
	(and (ev-smtcp-meta-extract-global-facts)
	     (ttmrg-correct-p tterm)
	     (alistp env)
	     (consp (ttmrg->term tterm))
	     (not (equal (car (ttmrg->term tterm)) 'quote))
	     (ev-smtcp (ttmrg->path-cond tterm) env))
	(let ((new-ttargs (constrain-ttmrg->args-path-cond tterm state)))
	  (ttmrg-args-correct-values new-ttargs (cdr (ttmrg->term tterm)) env)))
      :in-theory (disable ttmrg-args-correct-values-when-ttmrg-correct-sk)
      :use((:instance lemma-1
			(args (cdr (ttmrg->term tterm)))
			(old-ttargs (ttmrg->args tterm))
			(new-ttargs (constrain-ttmrg->args-path-cond tterm state)))
	   (:instance ttmrg-args-correct-values-when-ttmrg-correct-sk))
      :prep-lemmas (
	(acl2::defruled lemma-1
	  (implies
	    (and (pseudo-term-listp args)
		 (ttmrg-args-correct-p old-ttargs)
		 (ttmrg-args-correct-p new-ttargs)
		 (alistp env)
		 (ttmrg-args-correct-values old-ttargs args env)
		 (ttmrg-args->stronger-path-cond old-ttargs new-ttargs env))
	    (ttmrg-args-correct-values new-ttargs args env))
	  :in-theory (enable ttmrg-args-correct-values
			     ttmrg-args-correct-p
			     ttmrg-args->stronger-path-cond))))))


(define ttmrg-args-only-changed->args ((ttargs1 ttmrg-list-p) (ttargs2 ttmrg-list-p))
  :returns (ok booleanp)
  (b* (((unless (and (consp ttargs1) (consp ttargs2)))
	(not (or (consp ttargs1) (consp ttargs2))))
       ((cons (ttmrg tterm1) tl1) ttargs1)
       ((cons (ttmrg tterm2) tl2) ttargs2)
       ((unless (and (equal tterm1.term tterm2.term)
		     (equal tterm1.path-cond tterm2.path-cond)))
	nil))
    (ttmrg-args-only-changed->args tl1 tl2))
  ///
  (more-returns
    (ok :name match-len-when-ttmrg-args-only-changed->args
      (implies ok (match-len ttargs1 ttargs2))
      :hints(("Goal" :in-theory (enable match-len)))))
  ; we might not have needed to have gone all out and shown that
  ; ttmrg-args-only-change->args is an equivalence relation, but we do
  ; need reflexivity, so why not take care of the rest while we're at it.
  (defrule reflexivity-of-ttmrg-args-only-changed->args
    (ttmrg-args-only-changed->args x x))
  (defrule commutativity-of-ttmrg-args-only-changed->args
    (equal (ttmrg-args-only-changed->args y x)
	   (ttmrg-args-only-changed->args x y)))
  (defrule transativity-of-ttmrg-args-only-changed->args
    (implies (and (ttmrg-args-only-changed->args x y)
		  (ttmrg-args-only-changed->args y z))
	     (ttmrg-args-only-changed->args x z)))
  (local (in-theory (disable ttmrg-args-only-changed->args)))
  (defequiv ttmrg-args-only-changed->args))

(encapsulate (((constrain-ttmrg->args-args * state) => *))
  (local (define constrain-ttmrg->args-args
	     ((tterm ttmrg-p) (state state-p))
	   :enabled t
	   :ignore-ok t
	   :irrelevant-formals-ok t
	   (ttmrg-list-fix (ttmrg->args tterm))))

  (defrule ttmrg-list-p-of-constrain-ttmrg->args-args
    (ttmrg-list-p (constrain-ttmrg->args-args tterm state))
    :rule-classes (:rewrite :type-prescription))

  (defrule ttmrg-args-only-changed->args-of-constrain-ttmrg->args-args
    (implies (ev-smtcp-meta-extract-global-facts)
	     (ttmrg-args-only-changed->args
	       (constrain-ttmrg->args-args tterm state)
	       (ttmrg->args tterm)))
    :in-theory (enable ttmrg-args-only-changed->args)))

(defrule ttmrg-correct-p-of-constrain-ttmrg->args-args
  (implies (and (ev-smtcp-meta-extract-global-facts)
		(ttmrg-correct-p tterm)
		(ttmrg-args-correct-p
		  (constrain-ttmrg->args-args tterm state)))
	   (ttmrg-correct-p
	     (change-ttmrg->args
	       tterm
	       (constrain-ttmrg->args-args tterm state))))
  :expand (change-ttmrg->args tterm new-ttargs)
  :in-theory (disable lemma-sk)
  :use((:instance ttmrg-correct-p
		  (tterm (change-ttmrg->args
			   tterm
			   (constrain-ttmrg->args-args tterm state))))
       (:instance lemma-sk
		  (env (ttmrg-correct-sk-witness
			 (change-ttmrg->args
			   tterm
			   (constrain-ttmrg->args-args tterm state))))
		  (new-ttargs (constrain-ttmrg->args-args tterm state))))
  :prep-lemmas (
    (defrule lemma-1
      (equal (ttmrg->args (change-ttmrg->args tterm new-ttargs))
	     (ttmrg-list-fix new-ttargs))
      :expand (change-ttmrg->args tterm new-ttargs))
    (acl2::defruled lemma-sk
      (implies (and (ttmrg-correct-p tterm)
		    (ttmrg-args-correct-p new-ttargs)
		    (ttmrg-args-only-changed->args
		      new-ttargs (ttmrg->args tterm))
		    (equal env (ttmrg-correct-sk-witness
			     (change-ttmrg->args tterm new-ttargs))))
	       (ttmrg-correct-sk (change-ttmrg->args tterm new-ttargs)))
      :in-theory (disable ttmrg-args-correct-values-when-ttmrg-correct-sk
			  ttmrg-args-correct-path-when-ttmrg-correct-sk
			  ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk)
      :use((:instance change-ttmrg->args)
	   (:instance ttmrg-correct-sk
		      (tterm (change-ttmrg->args tterm new-ttargs)))
	   (:instance ttmrg-args-correct-values-when-ttmrg-correct-sk)
	   (:instance ttmrg-args-correct-path-when-ttmrg-correct-sk)
	   (:instance ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk))
      :prep-lemmas (
	(defrule lemma-values
	  (implies
	    (and (alistp env)
		 (ttmrg-args-correct-values old-ttargs args env)
		 (ttmrg-args-only-changed->args new-ttargs old-ttargs)
		 (ttmrg-args-correct-p new-ttargs))
	    (ttmrg-args-correct-values new-ttargs args env))
	  :rule-classes ((:rewrite :match-free :all))
	  :in-theory (enable ttmrg-args-correct-values
			     ttmrg-args-only-changed->args))

	(defrule lemma-path
	  (implies
	    (and (alistp env)
		 (ttmrg-args-correct-path old-ttargs env)
		 (ttmrg-args-only-changed->args new-ttargs old-ttargs)
		 (ttmrg-args-correct-p new-ttargs))
	    (ttmrg-args-correct-path new-ttargs env))
	  :in-theory (enable ttmrg-args-correct-path
			     ttmrg-args-only-changed->args))

	(acl2::defrule lemma-if
	  (implies
	    (ttmrg-args-only-changed->args new-ttargs (ttmrg->args tterm))
	    (and (equal (ttmrg->path-cond (car new-ttargs))
			(ttmrg->path-cond (car (ttmrg->args tterm))))
		 (equal (ttmrg->term (car new-ttargs))
			(ttmrg->term (car (ttmrg->args tterm))))
		 (equal (ttmrg->path-cond (cadr new-ttargs))
			(ttmrg->path-cond (cadr (ttmrg->args tterm))))
		 (equal (ttmrg->path-cond (caddr new-ttargs))
			(ttmrg->path-cond (caddr (ttmrg->args tterm))))))
	  :in-theory (enable ttmrg-args-only-changed->args))))))

; Update the term and/or top-judgement fields of the elements of an argument
; list.  ; Perhaps this could be combined with the code above for updating
; path-conditions.  Would functional instantiation of the theorems here 
; be harder if we merged the constraints?
;(encapsulate (((constrain-ttmrg->args-term/judge * state) => *))
;  (local (define constrain-ttmrg->args-term/judge
;	     ((tterm ttmrg-p) (state state-p))
;	   :enabled t
;	   :ignore-ok t
;	   :irrelevant-formals-ok t
;	   (ttmrg->args tterm)))
;
;  (defrule ttmrg-list-p-of-constrain-ttmrg->args-term/judge
;    (ttmrg-list-p (constrain-ttmrg->args-term/judge tterm state)))
;
;  (defrule match-len-of-constrain-ttmrg->args-term/judge
;    (match-len (constrain-ttmrg->args-term/judge tterm state)
;	       (ttmrg->args tterm)))
;
;  (define constrain-ttmrg->args-term/judge--unchanged-p
;            ((old-args ttmrg-list-p) (new-args ttmrg-list-p)
;				     (env alistp))
;    :returns (ok booleanp)
;    (b* (((unless (and (consp old-args) (consp new-args)))
;          (not (or (consp old-args) (consp new-args))))
;	 ((cons (ttmrg old-hd) old-tl) old-args)
;	 ((cons (ttmrg new-hd) new-tl) new-args)
;	 ((unless (equal new-hd.path-cond old-hd.path-cond)) nil)
;	 ((unless
;	    (implies
;	      (ev-smtcp old-hd.path-cond env)
;	      (equal (ev-smtcp new-hd.term env)
;		     (ev-smtcp old-hd.term env))))
;	  nil))
;      (constrain-ttmrg->args-term/judge--unchanged-p old-tl new-tl env))
;    ///
;    (defrule reflexivity-of-constrain-ttmrg->args-term/judge--unchanged-p
;      (constrain-ttmrg->args-term/judge--unchanged-p args args env)))
;
;  (defrule constrain-ttmrg->args-term/judge--unchanged
;    (implies
;      (and (ev-smtcp-meta-extract-global-facts)
;	   (ttmrg-correct-p tterm)
;	   (alistp env))
;      (constrain-ttmrg->args-term/judge--unchanged-p
;	(ttmrg->args tterm)
;	(constrain-ttmrg->args-term/judge tterm state)
;	env)))
;
;  (defrule ttmrg-args-correct-p-of-constrain-ttmrg->args-term/judge
;    (implies
;      (and (ev-smtcp-meta-extract-global-facts)
;	   (ttmrg-correct-p tterm))
;      (ttmrg-args-correct-p (constrain-ttmrg->args-term/judge tterm state)))))
;
;(define ttmrg-args->arglist ((ttargs ttmrg-list-p))
;  :returns (args pseudo-term-listp)
;  (if (consp ttargs)
;    (cons (ttmrg->term (car ttargs))
;	  (ttmrg-args->arglist (cdr ttargs)))
;    nil))
;
;(local (defrule match-len-of-ttmrg-args->arglist
;  (match-len (ttmrg-args->arglist ttargs) ttargs)
;  :in-theory (enable ttmrg-args->arglist match-len)))
;
;(define change-ttmrg->args-term/judge
;    ((tterm ttmrg-syntax-p) (new-args ttmrg-list-p))
;  :returns (new-tt ttmrg-p)
;  :guard-hints(("Goal" :expand((ttmrg-syntax-p tterm))))
;  (b* (((ttmrg tterm) (ttmrg-fix tterm))
;       ((unless (consp tterm.term)) tterm)
;       (fn (car tterm.term))
;       ((unless (not (equal fn 'quote))) tterm)
;       (new-term (cons fn (ttmrg-args->arglist new-args))))
;    (change-ttmrg tterm :term new-term :args new-args)))
;
;(defrule correctness-of-change-ttmrg->args-term/judge
;  (implies (and (ev-smtcp-meta-extract-global-facts)
;		(ttmrg-correct-p tterm))
;	   (ttmrg-correct-p
;	     (change-ttmrg->args tterm
;	       (constrain-ttmrg->args-term/judge tterm state))))
;
;  :in-theory (e/d (ttmrg-correct-sk)
;		  (change-ttmrg->args))
;  :expand ((ttmrg-correct-p (change-ttmrg->args
;			      tterm
;			      (constrain-ttmrg->args-term/judge tterm state))))
;  :prep-lemmas (
;    (defrule lemma-values
;      (implies (and (ev-smtcp-meta-extract-global-facts)
;		    (ttmrg-correct-p tterm)
;		    (alistp env)
;		    (ev-smtcp (ttmrg->path-cond tterm) env)
;		    (consp (ttmrg->term tterm))
;		    (not (equal (car (ttmrg->term tterm)) 'quote)))
;	       (ttmrg-args-correct-values
;		 (constrain-ttmrg->args-term/judge tterm state)
;		 (cdr (ttmrg->term tterm))
;		 env))
;      :in-theory (disable ttmrg-args-correct-values-when-ttmrg-correct-sk)
;      :use((:instance lemma-1 (args (cdr (ttmrg->term tterm)))
;		                     (old-ttargs (ttmrg->args tterm))
;				     (new-ttargs (constrain-ttmrg->args-term/judge tterm state)))
;	   (:instance ttmrg-args-correct-values-when-ttmrg-correct-sk))
;      :prep-lemmas (
;	(acl2::defruled lemma-1
;	  (implies (and (pseudo-term-listp args)
;			(ttmrg-list-p old-ttargs)
;			(ttmrg-list-p new-ttargs)
;			(alistp env)
;			(ttmrg-args-correct-values old-ttargs args env)
;			(constrain-ttmrg->args-term/judge--unchanged-p
;			  old-ttargs new-ttargs env))
;		   (ttmrg-args-correct-values new-ttargs args env))
;	  :in-theory (enable ttmrg-args-correct-values
;			     constrain-ttmrg->args-term/judge--unchanged-p))))
;
;    (defrule lemma-if
;      (implies
;	(and (ev-smtcp-meta-extract-global-facts)
;	     (ttmrg-correct-p tterm)
;	     (alistp env)
;	     (ev-smtcp (ttmrg->path-cond tterm) env)
;	     (consp (ttmrg->term tterm))
;	     (equal (car (ttmrg->term tterm)) 'if))
;	(let ((new-ttargs (constrain-ttmrg->args-term/judge tterm state)))
;	  (and (ev-smtcp (ttmrg->path-cond (car new-ttargs)) env)
;	       (if (ev-smtcp (ttmrg->term (car new-ttargs)) env)
;		 (ev-smtcp (ttmrg->path-cond (cadr new-ttargs)) env)
;		 (ev-smtcp (ttmrg->path-cond (caddr new-ttargs)) env)))))
;      :in-theory (disable ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk)
;      :use((:instance lemma-1 (new-ttargs (constrain-ttmrg->args-term/judge tterm state)))
;	   (:instance ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk))
;      :prep-lemmas (
;	(defrule lemma-1
;          (implies
;	    (and (ev-smtcp-meta-extract-global-facts)
;		 (ttmrg-correct-sk tterm)
;		 (ttmrg-list-p new-ttargs)
;		 (alistp env)
;		 (ev-smtcp (ttmrg->path-cond tterm) env)
;		 (consp (ttmrg->term tterm))
;		 (equal (car (ttmrg->term tterm)) 'if)
;		 (constrain-ttmrg->args-term/judge--unchanged-p
;		   (ttmrg->args tterm) new-ttargs env))
;	    (let ((old-ttargs (ttmrg->args tterm)))
;	      (and (equal (ev-smtcp (ttmrg->term (car new-ttargs)) env)
;			  (ev-smtcp (ttmrg->term (car old-ttargs)) env))
;		   (equal (ttmrg->path-cond (car new-ttargs))
;			  (ttmrg->path-cond (car old-ttargs)))
;		   (equal (ttmrg->path-cond (cadr new-ttargs))
;			  (ttmrg->path-cond (cadr old-ttargs)))
;		   (equal (ttmrg->path-cond (caddr new-ttargs))
;			  (ttmrg->path-cond (caddr old-ttargs))))))
;	  :in-theory (disable ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk)
;	  :use((:instance constrain-ttmrg->args-term/judge--unchanged-p
;			    (old-args (ttmrg->args tterm)) (new-args new-ttargs))
;	       (:instance constrain-ttmrg->args-term/judge--unchanged-p
;			    (old-args (cdr (ttmrg->args tterm))) (new-args (cdr new-ttargs)))
;	       (:instance constrain-ttmrg->args-term/judge--unchanged-p
;			    (old-args (cddr (ttmrg->args tterm))) (new-args (cddr new-ttargs)))
;	       (:instance ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk)))))
;
;    (defrule lemma-path
;      (implies
;	(and (ev-smtcp-meta-extract-global-facts)
;	     (ttmrg-correct-p tterm)
;	     (alistp env)
;	     (ev-smtcp (ttmrg->path-cond tterm) env)
;	     (consp (ttmrg->term tterm))
;	     (not (equal (car (ttmrg->term tterm)) 'quote))
;	     (not (equal (car (ttmrg->term tterm)) 'if)))
;	(let ((new-ttargs (constrain-ttmrg->args-term/judge tterm state)))
;	  (ttmrg-args-correct-path new-ttargs env)))
;      :in-theory (disable lemma-1 ttmrg-args-correct-path-when-ttmrg-correct-sk)
;      :use((:instance lemma-1
;		      (old-ttargs (ttmrg->args tterm))
;		      (new-ttargs (constrain-ttmrg->args-term/judge tterm state)))
;           (:instance ttmrg-args-correct-path-when-ttmrg-correct-sk))
;      :prep-lemmas (
;	(defrule lemma-1
;	  (implies
;	    (and (ttmrg-args-correct-path old-ttargs env)
;		 (constrain-ttmrg->args-term/judge--unchanged-p
;		   old-ttargs new-ttargs env))
;	    (ttmrg-args-correct-path new-ttargs env))
;	  :in-theory (enable ttmrg-args-correct-path
;			     constrain-ttmrg->args-term/judge--unchanged-p))))))
