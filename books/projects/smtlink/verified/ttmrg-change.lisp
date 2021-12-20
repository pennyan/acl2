;; Copyright (C) 2021, University of British Columbia
;; Written by Mark Greenstreet (December 15th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "ttmrg")

(set-state-ok t)
(set-induction-depth-limit 1)

(encapsulate (((constrain-ttmrg->top-judge * state) => *))
  (local (define constrain-ttmrg->top-judge
	     ((tterm ttmrg-p) (state state-p))
	   :enabled t
	   :ignore-ok t
	   :irrelevant-formals-ok t
	   ''t))

  (defrule conj-p-of-constrain-ttmrg->top-judge
    (conj-p (constrain-ttmrg->top-judge path-cond state)))

  (defrule correctness-of-constrain-ttmrg->top-judge
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (alistp env)
		  (ev-smtcp (ttmrg->path-cond tterm) env))
	     (ev-smtcp (constrain-ttmrg->top-judge tterm state) env))))

(defmacro ttmrg-only-changed->top-judgements (old-tt new-tt)
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
      (ttmrg-only-changed->top-judgements tterm new-tt)))

  (local (in-theory (disable change-ttmrg->top-judge)))
  (defrule correctness-of-change-ttmrg->top-judge
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (ttmrg-correct-p tterm))
	     (ttmrg-correct-p
	       (change-ttmrg->top-judge
		 tterm
		 (constrain-ttmrg->top-judge tterm state))))
    :expand ((ttmrg-correct-p tterm)
	     (ttmrg-correct-p (change-ttmrg->top-judge
			       tterm
			       (constrain-ttmrg->top-judge tterm state))))
    :prep-lemmas (
      (defrule correct-sk-of-change-ttmrg->top-judge
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (ttmrg-syntax-p tterm)
		      (ttmrg-correct-sk tterm))
		 (ttmrg-correct-sk (change-ttmrg->top-judge
				    tterm
				    (constrain-ttmrg->top-judge tterm state))))
	:expand ((ttmrg-correct-sk (change-ttmrg->top-judge tterm (constrain-ttmrg->top-judge tterm state))))
	:prep-lemmas (
	  (defrule ttmrg-correct-and-path-cond-implies-judgements
	    (implies (and (ttmrg-correct-sk tterm)
			  (alistp env)
			  (ev-smtcp (ttmrg->path-cond tterm) env))
		     (ev-smtcp (ttmrg->judgements tterm) env))
	    :in-theory (disable ttmrg-correct-sk-necc)
	    :use((:instance ttmrg-correct-sk-necc (a env))))

	  (defrule constrain-mrg->top-judge-maintains-judgements
	    (implies (and (ev-smtcp-meta-extract-global-facts)
			  (ttmrg-syntax-p tterm)
			  (alistp env)
			  (ev-smtcp (ttmrg->path-cond tterm) env)
			  (ev-smtcp (ttmrg->judgements tterm) env))
		     (ev-smtcp (ttmrg->judgements
				 (change-ttmrg->top-judge
				   tterm
				   (constrain-ttmrg->top-judge tterm state)))
			       env))
	    :do-not-induct t
	    :in-theory (e/d (ttmrg->args-judgement)
			    (eval-of-conj-cons car-is-if-when-conj-consp))
	    :use((:instance eval-of-conj-cons (hd (conj-car (ttmrg->judgements tterm)))
					      (tl (conj-cdr (ttmrg->judgements tterm))))
	         (:instance eval-of-conj-cons (hd (constrain-ttmrg->top-judge tterm state))
					      (tl (conj-cdr (ttmrg->judgements tterm))))
	         (:instance eval-of-conj-cons (hd (constrain-ttmrg->top-judge tterm state))
					      (tl ''t)))
	    :expand ((change-ttmrg->top-judge tterm (constrain-ttmrg->top-judge tterm state))))

	  (defrule ttmrg-correct-sk-implies-good-if
	    (implies (and (ttmrg-correct-sk tterm)
			  (alistp env)
			  (consp (ttmrg->term tterm))
			  (equal (car (ttmrg->term tterm)) 'if))
		     (and (implies (and (ev-smtcp (ttmrg->path-cond tterm) env)
					(ev-smtcp (ttmrg->term (car (ttmrg->args tterm))) env))
				   (ev-smtcp (ttmrg->path-cond (cadr (ttmrg->args tterm))) env))
			  (implies (and (ev-smtcp (ttmrg->path-cond tterm) env)
					(not (ev-smtcp (ttmrg->term (car (ttmrg->args tterm))) env)))
				   (ev-smtcp (ttmrg->path-cond (caddr (ttmrg->args tterm))) env))))
	    :in-theory (disable ttmrg-correct-sk-necc)
	    :use((:instance ttmrg-correct-sk-necc (a env)))))))))

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
      (ttmrg-only-changed->top-judgements tterm new-tt)
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
	:in-theory (e/d (ttmrg->top-judgement) (eval-of-conj-cons))
	:use((:instance eval-of-conj-cons (hd (conj-car (ttmrg->judgements tterm)))
					  (tl (conj-cdr (ttmrg->judgements tterm))))))
      (defrule lemma-2
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (ttmrg-correct-p tterm)
		      (ev-smtcp (ttmrg->path-cond tterm) env)
		      (alistp env))
		 (ev-smtcp (ttmrg->top-judgement tterm) env))
	:in-theory (e/d (ttmrg-correct-p) (ttmrg-correct-sk-necc))
	:use((:instance ttmrg-correct-sk-necc (a env)))))))
