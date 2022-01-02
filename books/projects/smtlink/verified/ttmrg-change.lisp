;; Copyright (C) 2021, University of British Columbia
;; Written by Mark Greenstreet (December 15th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

; ttmrg-change.lisp
;   Functions that preserver ttmrg-correct-p when updating one or more
;   fields of a ttmrg-p term.

(include-book "ttmrg")

(set-state-ok t)
(set-induction-depth-limit 1)

;  Properties of ttmrg-correct-sk                                      ;
;    When one of the functions in this books updates one or a few      ;
;    fields, we include a theorem that says the other fields are       ;
;    unchanged.  Then, the proof that the new ttmrg-p term satisifies  ;
;    the requirements of ttmrg-correct-sk needs to know that the old   ;
;    satisfied these requirements as well.  A brute force approach     ;
;    would be to enable ttmrg-correct-sk so that both the old and new  ;
;    terms get expanded.  Doing so generates a plethora of subgoals;   ;
;    the proofs are hard to debug; and they would presumably be slow   ;
;    if they succeeded.                                                ;
;      To avoid the problems described above, the following theorems   ;
;    prove that if a term satisifies ttmrg-correct-sk, then the        ;
;    various properties below hold.  In this case, the rewriter        ;
;    finds the relevant theorem(s) about the old term when they are    ;
;    needed, and we avoid the case-explosion.                          ;
;                                                                      ;
;    "plus ça change, plus c'est la même chose"                        ;

(local (encapsulate nil
  ; I'm hoping that the functions in this book for updating ttmrg-p    ;
  ; terms will be all that we need in the rest of Smtlink.  Thus, I'm  ;
  ; making all of these theorems local to avoid cluttering the logical ;
  ; world with runes that won't be used elsewhere.                     ;

  (defrule ttmrg->judgements-when-ttmrg-correct-sk
    (implies (and (ttmrg-correct-sk tterm)
		  (alistp env)
		  (ev-smtcp (ttmrg->path-cond tterm) env))
	     (ev-smtcp (ttmrg->judgements tterm) env))
    :use ((:instance ttmrg-correct-sk-necc)))

  (defrule ttmrg-args-correct-values-when-ttmrg-correct-sk
    (implies (and (ttmrg-correct-sk tterm)
		  (alistp env)
		  (ev-smtcp (ttmrg->path-cond tterm) env)
		  (consp (ttmrg->term tterm)) (not (equal (car (ttmrg->term tterm)) 'quote)))
	     (ttmrg-args-correct-values (ttmrg->args tterm) (cdr (ttmrg->term tterm)) env))
    :use((:instance ttmrg-correct-sk-necc)))

  (defrule ev-smtcp-of-ttmrg->args-judgement-when-ttmrg-correct-sk
    (implies (and (ttmrg-correct-sk tterm)
		  (alistp env)
		  (ev-smtcp (ttmrg->path-cond tterm) env)
		  (consp (ttmrg->term tterm)) (not (equal (car (ttmrg->term tterm)) 'quote)))
	     (ev-smtcp (ttmrg->args-judgement tterm) env))
    :in-theory (e/d (ttmrg->args-judgement) (ev-smtcp-of-conj-cons))
    :use((:instance ttmrg-correct-sk-necc)
	 (:instance ev-smtcp-of-conj-cons (hd (conj-car (ttmrg->judgements tterm)))
					  (tl (conj-cdr (ttmrg->judgements tterm))))))

  (defrule ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk
    (implies (and (ttmrg-correct-sk tterm)
		  (alistp env)
		  (ev-smtcp (ttmrg->path-cond tterm) env)
		  (consp (ttmrg->term tterm)) (equal (car (ttmrg->term tterm)) 'if))
	     (and (ev-smtcp (ttmrg->path-cond (car (ttmrg->args tterm))) env)
		  (implies (ev-smtcp (ttmrg->term (car (ttmrg->args tterm))) env)
			   (ev-smtcp (ttmrg->path-cond (cadr (ttmrg->args tterm))) env))
		  (implies (not (ev-smtcp (ttmrg->term (car (ttmrg->args tterm))) env))
			   (ev-smtcp (ttmrg->path-cond (caddr (ttmrg->args tterm))) env))))
    :use((:instance ttmrg-correct-sk-necc)))

  (defrule ttmrg-args-correct-path-when-ttmrg-correct-sk
    (implies (and (ttmrg-correct-sk tterm)
		  (alistp env)
		  (ev-smtcp (ttmrg->path-cond tterm) env)
		  (consp (ttmrg->term tterm)) (not (equal (car (ttmrg->term tterm)) 'quote))
		  (not (equal (car (ttmrg->term tterm)) 'if)))
	     (ttmrg-args-correct-path (ttmrg->args tterm) (ttmrg->path-cond tterm) env))
    :use((:instance ttmrg-correct-sk-necc)))

  (defrule ttmrg-args-correct-judge-when-ttmrg-correct-sk
    (implies (and (ttmrg-correct-sk tterm)
		  (alistp env)
		  (ev-smtcp (ttmrg->path-cond tterm) env)
		  (consp (ttmrg->term tterm))
		  (not (equal (car (ttmrg->term tterm)) 'quote)))
	     (ttmrg-args-correct-judge (ttmrg->args tterm) (ttmrg->args-judgement tterm) env))
    :in-theory (e/d (ttmrg->args-judgement) (ev-smtcp-of-conj-cons))
    :use((:instance ttmrg-correct-sk-necc)
	 (:instance ev-smtcp-of-conj-cons (hd (conj-car (ttmrg->judgements tterm)))
				      (tl (conj-cdr (ttmrg->judgements tterm)))))
    :prep-lemmas (
      (defrule conj-cdr-of-conj-atom
	(implies (not (conj-consp x))
		 (equal (conj-cdr x) ''t))
	:expand ((conj-consp x) (conj-cdr x)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                                      ;
;  Functions for updating the top judgement of a ttmrg-p:              ;
;    constrain-ttmrg->top-judge:  constraints for a safe update        ;
;    change-ttmrg->top-judge:                                          ;
;      Update top-judgement using constrain-ttmrg->top-judge.          ;
;      We prove that change-ttmrg->top-judge preserves ttmrg-correct-p.;
;    ttmrg-only->changed-judgements:                                   ;
;      macro that generates the predicate that says all fields other   ;
;        than the judgements field are unchanged.                      ;
;                                                                      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate (((constrain-ttmrg->top-judge * state) => *))
  (local (define constrain-ttmrg->top-judge
	     ((tterm ttmrg-p) (state state-p))
	   :enabled t
	   :ignore-ok t
	   :irrelevant-formals-ok t
	   ''t))

  (defrule conj-p-of-constrain-ttmrg->top-judge
    (conj-p (constrain-ttmrg->top-judge tterm state)))

  (defrule correctness-of-constrain-ttmrg->top-judge
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (alistp env)
		  (ev-smtcp (ttmrg->path-cond tterm) env))
	     (ev-smtcp (constrain-ttmrg->top-judge tterm state) env))))

(defmacro ttmrg-only-changed->judgements (old-tt new-tt)
  `(and (equal (ttmrg->term ,new-tt)
	       (ttmrg->term ,old-tt))
        (equal (ttmrg->args ,new-tt)
	       (ttmrg->args ,old-tt))
        (equal (ttmrg->path-cond ,new-tt)
	       (ttmrg->path-cond ,old-tt))))

(define change-ttmrg->top-judge ((tterm ttmrg-p) (new-top-judge conj-p))
  :returns (new-tt ttmrg-p)
  (b* (((ttmrg tterm) (ttmrg-fix tterm))
       (term tterm.term)
       (new-j (if (and (consp term) (not (equal (car term) 'quote)))
		(conj-cons (conj-fix new-top-judge)
			   (ttmrg->args-judgement tterm))
		new-top-judge)))
    (change-ttmrg tterm :judgements new-j))
  ///
  (more-returns change-ttmrg->top-judge
    (new-tt :name syntax-p-of-change-ttmrg->top-judge
      (implies (and (ttmrg-syntax-p tterm)
		    (conj-p new-top-judge))
	       (ttmrg-syntax-p new-tt))
      :hints(("Goal" :in-theory (enable ttmrg-syntax-p ttmrg->args-judgement))))

    (new-tt :name change-ttmrg->top-judge--unchanged-fields
      (ttmrg-only-changed->judgements tterm new-tt)))

  (defrule correctness-of-change-ttmrg->top-judge
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (ttmrg-correct-p tterm))
	     (ttmrg-correct-p
	       (change-ttmrg->top-judge
		 tterm
		 (constrain-ttmrg->top-judge tterm state))))
    :in-theory (disable change-ttmrg->top-judge)
    :expand ((ttmrg-correct-p tterm)
	     (ttmrg-correct-p (change-ttmrg->top-judge
			       tterm
			       (constrain-ttmrg->top-judge tterm state))))
    :prep-lemmas (
      (defrule judgements-of-change-ttmrg->top-judge
	(implies (ttmrg-syntax-p tterm)
		 (equal (ttmrg->judgements
			  (change-ttmrg->top-judge
			    tterm
			    (constrain-ttmrg->top-judge tterm state)))
			(let ((term (ttmrg->term tterm))
			      (new-j (constrain-ttmrg->top-judge tterm state)))
			  (if (and (consp term) (not (equal (car term) 'quote)))
			    (conj-cons new-j (ttmrg->args-judgement tterm))
			    new-j))))
	:in-theory (enable ttmrg->args-judgement))
      (defrule ttmrg-correct-sk-of-change-ttmrg->top-judge
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (ttmrg-correct-sk tterm))
		 (ttmrg-correct-sk
		   (change-ttmrg->top-judge
		     tterm
		     (constrain-ttmrg->top-judge tterm state))))
	:in-theory (disable change-ttmrg->top-judge)
	:expand ((ttmrg-correct-sk (change-ttmrg->top-judge
				    tterm
				    (constrain-ttmrg->top-judge tterm state))))))))

(define strengthen-ttmrg->top-judge ((tterm ttmrg-syntax-p) (new-top-judge conj-p))
  :returns (new-tt ttmrg-p)
  (b* (((ttmrg tterm) (ttmrg-fix tterm))
       ((if (equal new-top-judge ''t)) tterm)
       (old-top-judge (ttmrg->top-judgement tterm))
       (j2 (if (equal old-top-judge ''t)
	     new-top-judge
	     (conj-cons new-top-judge old-top-judge))))
     (change-ttmrg->top-judge tterm j2))
  ///
  (more-returns strengthen-ttmrg->top-judge
    (new-tt :name ttmrg-syntax-p-of-strengthen-ttmrg->top-judge
      (implies (and (ttmrg-syntax-p tterm) (conj-p new-top-judge))
	       (ttmrg-syntax-p new-tt))
      :hints(("Goal"
        :in-theory (enable strengthen-ttmrg->top-judge ttmrg-syntax-p))))
    (new-tt :name strengthen-ttmrg->top-judge--unchanged-fields
      (ttmrg-only-changed->judgements tterm new-tt)
      :hints(("Goal" :expand ((strengthen-ttmrg->top-judge tterm new-top-judge))))))

  (defrule correctness-of-strengthen-ttmrg->top-judge
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (ttmrg-correct-p tterm))
	     (ttmrg-correct-p
	       (strengthen-ttmrg->top-judge
		 tterm
		 (constrain-ttmrg->top-judge tterm state))))
    :use((:functional-instance correctness-of-change-ttmrg->top-judge
	    (constrain-ttmrg->top-judge
	      (lambda (tterm state)
		(conj-cons (constrain-ttmrg->top-judge tterm state)
			   (if (ttmrg-correct-p tterm)
			     (ttmrg->top-judgement tterm)
			     ''t))))))
    :prep-lemmas (
      (defrule lemma-1
        (implies (and (alistp env)
		      (ev-smtcp (ttmrg->judgements tterm) env))
		 (ev-smtcp (ttmrg->top-judgement tterm) env))
	:in-theory (e/d (ttmrg->top-judgement) (ev-smtcp-of-conj-cons))
	:use((:instance ev-smtcp-of-conj-cons (hd (conj-car (ttmrg->judgements tterm)))
					      (tl (conj-cdr (ttmrg->judgements tterm))))))
      (defrule lemma-2
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (ttmrg-correct-p tterm)
		      (ev-smtcp (ttmrg->path-cond tterm) env)
		      (alistp env))
		 (ev-smtcp (ttmrg->top-judgement tterm) env))
	:do-not-induct t
	:expand ((ttmrg-correct-p tterm))))))
