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

(local (in-theory (disable ; mark is impatient
  CONSP-OF-PSEUDO-LAMBDAP PSEUDO-TERMP PSEUDO-LAMBDAP-OF-FN-CALL-OF-PSEUDO-TERMP
  ACL2::PSEUDO-LAMBDAP-OF-CAR-WHEN-PSEUDO-TERMP SYMBOL-LISTP)))


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
		  (consp (ttmrg->term tterm))
		  (not (equal (car (ttmrg->term tterm)) 'quote)))
	     (ttmrg-args-correct-values (ttmrg->args tterm) (cdr (ttmrg->term tterm)) env))
    :use((:instance ttmrg-correct-sk-necc)))

  (defrule ev-smtcp-of-ttmrg->args-judgement-when-ttmrg-correct-sk
    (implies (and (ttmrg-correct-sk tterm)
		  (alistp env)
		  (ev-smtcp (ttmrg->path-cond tterm) env)
		  (consp (ttmrg->term tterm))
		  (not (equal (car (ttmrg->term tterm)) 'quote)))
	     (ev-smtcp (ttmrg->args-judgement tterm) env))
    :in-theory (e/d (ttmrg->args-judgement) (ev-smtcp-of-conj-cons))
    :use((:instance ttmrg-correct-sk-necc)
	 (:instance ev-smtcp-of-conj-cons (hd (conj-car (ttmrg->judgements tterm)))
					  (tl (conj-cdr (ttmrg->judgements tterm))))))

  (defrule ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk
    (implies (and (ttmrg-correct-sk tterm)
		  (alistp env)
		  (ev-smtcp (ttmrg->path-cond tterm) env)
		  (consp (ttmrg->term tterm))
		  (equal (car (ttmrg->term tterm)) 'if))
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
		  (consp (ttmrg->term tterm))
		  (not (equal (car (ttmrg->term tterm)) 'quote))
		  (not (equal (car (ttmrg->term tterm)) 'if)))
	     (ttmrg-args-correct-path (ttmrg->args tterm) env))
    :use((:instance ttmrg-correct-sk-necc)))

  (defrule ttmrg-args-correct-judge-when-ttmrg-correct-sk
    (implies (and (ttmrg-correct-sk tterm)
		  (alistp env)
		  (ev-smtcp (ttmrg->path-cond tterm) env)
		  (consp (ttmrg->term tterm))
		  (not (equal (car (ttmrg->term tterm)) 'quote)))
	     (ttmrg-args-correct-judge (ttmrg->args tterm) (conj-cdr (ttmrg->judgements tterm)) env))
    :use((:instance ttmrg-correct-sk-necc)))))


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
  (more-returns
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
			    (conj-cons new-j (conj-cdr (ttmrg->judgements tterm)))
			    new-j))))
	:in-theory (enable change-ttmrg->top-judge ttmrg->args-judgement)
	:use((:instance conj-atom (x (ttmrg->judgements tterm)))))
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
  (more-returns
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
	:expand ((ttmrg-correct-p tterm))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                                      ;
;  Functions for updating the path-cond of a ttmrg-p:                  ;
;                                                                      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro ttmrg-only-changed->path-cond (old-tt new-tt)
  `(and (equal (ttmrg->term ,new-tt)
	       (ttmrg->term ,old-tt))
        (equal (ttmrg->args ,new-tt)
	       (ttmrg->args ,old-tt))
        (equal (ttmrg->judgements ,new-tt)
	       (ttmrg->judgements ,old-tt))))

(define strengthen-ttmrg->path-cond ((tterm ttmrg-p) (new-path-cond conj-p))
  :returns (new-tt ttmrg-p)
  (b* (((ttmrg tterm) (ttmrg-fix tterm))
       (new-path-cond (conj-fix new-path-cond))
       ((if (equal new-path-cond ''t)) tterm)
       (pc2 (if (equal tterm.path-cond ''t)
	      new-path-cond
	      (conj-cons new-path-cond tterm.path-cond))))
    (change-ttmrg tterm :path-cond pc2))
  ///
  (more-returns
    (new-tt :name strengthen-ttmrg->path-cond--unchanged-fields
      (implies (ttmrg-p tterm)
	       (ttmrg-only-changed->path-cond tterm new-tt)))
    (new-tt :name strengthen-ttmrg->path-cond-strengthens-path-cond
      (implies (and (ttmrg-p tterm) (alistp env)
		    (ev-smtcp (ttmrg->path-cond new-tt) env))
	       (ev-smtcp (ttmrg->path-cond tterm) env))
      :hints(("Goal":in-theory (enable strengthen-ttmrg->path-cond)))))
  
  (local (in-theory (disable strengthen-ttmrg->path-cond)))
  (defrule syntax-p-of-strengthen-ttmrg->path-cond
    (implies (ttmrg-syntax-p tterm)
	     (ttmrg-syntax-p (strengthen-ttmrg->path-cond tterm new-path-cond)))
    :expand (
      (ttmrg-syntax-p tterm)
      (ttmrg-syntax-p (strengthen-ttmrg->path-cond tterm new-path-cond))))

  (defrule correctness-of-strengthen-ttmrg->path-cond
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (ttmrg-correct-p tterm))
	     (ttmrg-correct-p
	       (strengthen-ttmrg->path-cond
		 tterm
		 new-path-cond)))
    :expand ((ttmrg-correct-p tterm)
	     (ttmrg-correct-p (strengthen-ttmrg->path-cond
			       tterm
			       new-path-cond)))
    :prep-lemmas (
      (defrule ttmrg-correct-sk-of-strengthen-ttmrg->path-cond
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (ttmrg-correct-sk tterm))
		 (ttmrg-correct-sk
		   (strengthen-ttmrg->path-cond
		     tterm
		     new-path-cond)))
	:expand ((ttmrg-correct-sk (strengthen-ttmrg->path-cond
				    tterm
				    new-path-cond)))
	:in-theory (disable ttmrg-args-correct-path-when-ttmrg-correct-sk)
	:use((:instance ttmrg-args-correct-path-when-ttmrg-correct-sk
			  (env (ttmrg-correct-sk-witness
				 (strengthen-ttmrg->path-cond
				   tterm
                                   new-path-cond)))))))))

	   

; updating the path-cond of a ttmrg-p is "easy".
; we now want to show conditions that ensure the update of the path-conds
; of the arguments to a function call preserve ttmrg-correct-p.

(define list-conj-match-len ((lst true-listp) (conj conj-p))
  :returns (ok booleanp)
  (if (and (consp lst) (conj-consp conj))
    (list-conj-match-len (cdr lst) (conj-cdr conj))
    (and (not (consp lst)) (not (conj-consp conj)))))

(encapsulate (((constrain-ttmrg->args-path * state) => *))
  (local (define helper ((args ttmrg-list-p))
    :returns (new-pcs conj-conj-p)
    (if (consp args)
      (conj-cons ''t (helper (cdr args)))
      ''t)
    ///
    (more-returns
      (new-pcs :name ev-smtcp-of-helper
        (implies (alistp env)
		 (equal (ev-smtcp new-pcs env) t)))
      (new-pcs :name match-len-of-helper
        (list-conj-match-len args new-pcs)
	:hints(("Goal" :in-theory (enable list-conj-match-len)))))))

  (local (define constrain-ttmrg->args-path
	     ((tterm ttmrg-p) (state state-p))
	   :enabled t
	   :ignore-ok t
	   :irrelevant-formals-ok t
	   (helper (ttmrg->args tterm))))

  (defrule conj-conj-p-of-constrain-ttmrg->args-path
    (conj-conj-p (constrain-ttmrg->args-path tterm state)))

  (defrule match-len-of-constrain-ttmrg->args-path
    (list-conj-match-len (ttmrg->args tterm)
			 (constrain-ttmrg->args-path tterm state)))

  (defrule correctness-of-constrain-ttmrg->args-path
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (ttmrg-correct-sk tterm)
		  (alistp env)
		  (ev-smtcp (ttmrg->path-cond tterm) env))
	     (let ((fn (car (ttmrg->term tterm)))
		   (new-pcs (constrain-ttmrg->args-path tterm state)))
	       (if (equal fn 'if)
		 (and (ev-smtcp (conj-car new-pcs) env)
		      (if (ev-smtcp (ttmrg->term (car (ttmrg->args tterm))) env)
			(ev-smtcp (conj-car (conj-cdr new-pcs)) env)
			(ev-smtcp (conj-car (conj-cdr (conj-cdr new-pcs))) env)))
		 (ev-smtcp new-pcs env))))
    :expand ((helper (ttmrg->args tterm))
             (helper (cdr (ttmrg->args tterm)))
             (helper (cdr (cdr (ttmrg->args tterm)))))))

(define ttmrg-args-only-changed-path-cond-fn ((args0 ttmrg-list-p) (args1 ttmrg-list-p))
  :returns (ok booleanp)
  (b* (((unless (mbt (and (ttmrg-list-p args0) (ttmrg-list-p args1))))
	nil)
       ((unless (and (consp args0) (consp args1)))
	(not (or (consp args0) (consp args1))))
       ((cons (ttmrg hd0) tl0) args0)
       ((cons (ttmrg hd1) tl1) args1)
       ((unless (and (equal hd0.term hd1.term)
		     (equal hd0.args hd1.args)
		     (equal hd0.judgements hd1.judgements)))
	nil))
    (ttmrg-args-only-changed-path-cond-fn tl0 tl1))
  ///
  (defmacro ttmrg-args-only-changed->path-cond (old-tt new-tt)
    `(and (equal (ttmrg->term ,new-tt)
		 (ttmrg->term ,old-tt))
	  (ttmrg-args-only-changed-path-cond-fn (ttmrg->args ,new-tt)
						(ttmrg->args ,old-tt))
	  (equal (ttmrg->path-cond ,new-tt)
		 (ttmrg->path-cond ,old-tt))
	  (equal (ttmrg->judgements ,new-tt)
		 (ttmrg->judgements ,old-tt)))))

(defrule ttmrg-list-p-when-ttmrg-args-correct-p ; move to ttmrg.lisp
  (implies (ttmrg-args-correct-p args)
	   (ttmrg-list-p args))
  :in-theory (enable ttmrg-args-correct-p ttmrg-list-p induct-foo)
  :induct (induct-foo args)
  :prep-lemmas (
    (define induct-foo ((args))
      (if (consp args)
	(and (ttmrg-correct-p (car args))
	     (induct-foo (cdr args)))
	(equal args nil)))))

(define ttmrg-args-path-cond-stronger-p
    ((ttargs0 ttmrg-list-p) (ttargs1 ttmrg-list-p) (env alistp))
  :returns (ok booleanp)
  (b* (((unless (and (consp ttargs0) (consp ttargs1)))
	(not (or ttargs0 ttargs1)))
       ((cons hd0 tl0) ttargs0)
       ((cons hd1 tl1) ttargs1)
       ((unless (implies (ev-smtcp (ttmrg->path-cond hd1) env)
			 (ev-smtcp (ttmrg->path-cond hd0) env)))
	nil))
    (ttmrg-args-path-cond-stronger-p tl0 tl1 env))
  ///
  (defrule reflexivity-of-ttmrg-args-path-cond-stronger-p
    (implies (true-listp ttargs)
	     (ttmrg-args-path-cond-stronger-p ttargs ttargs env))
    :in-theory (enable ttmrg-args-path-cond-stronger-p)))

(defrule ttmrg-list-p-when-ttmrg-args-syntax-p ; move to ttmrg.lisp
  (implies (ttmrg-args-syntax-p ttargs args jargs)
	   (ttmrg-list-p ttargs))
  :in-theory (enable ttmrg-args-syntax-p ttmrg-list-p induct-foo)
  :induct (induct-foo ttargs args jargs)
  :prep-lemmas (
    (define induct-foo
        ((ttargs ttmrg-list-p) (args pseudo-term-listp) (jargs conj-conj-p))
      (if (consp args)
	(and (ttmrg-syntax-p (car ttargs))
	     (induct-foo (cdr ttargs) (cdr args) (conj-cdr jargs)))
	(equal args nil)))))

(define strengthen-ttmrg-args->path-cond-helper
    ((args ttmrg-list-p) (new-pcs conj-conj-p))
  :returns (new-args ttmrg-list-p)
  (b* (((unless (consp args)) nil)
       ((unless (conj-consp new-pcs))
	(ttmrg-list-fix args))
       ((cons hd tl) args)
       ((conj-cons pc-hd pc-tl) new-pcs)
       (new-hd (strengthen-ttmrg->path-cond hd pc-hd)))
    (cons new-hd (strengthen-ttmrg-args->path-cond-helper tl pc-tl))))

(local (encapsulate nil
  (more-returns strengthen-ttmrg-args->path-cond-helper
    (new-args :name ttmrg-list-syntax-p-of-strengthen-ttmrg-args->path-cond-helper
      (implies (ttmrg-list-syntax-p args)
	       (ttmrg-list-syntax-p new-args))
      :hints(("Goal" :in-theory (enable strengthen-ttmrg-args->path-cond-helper
					ttmrg-list-syntax-p))))
    (new-args :name ttmrg-args-correct-p-of-strengthen-ttmrg-args->path-cond-helper
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (ttmrg-args-correct-p args))
	       (ttmrg-args-correct-p new-args))
      :hints(("Goal" :in-theory (enable strengthen-ttmrg-args->path-cond-helper
					ttmrg-args-correct-p))))
    (new-args :name len-of-strengthen-ttmrg-args->path-cond-helper
      (equal (len new-args) (len args))
      :hints(("Goal" :in-theory (enable strengthen-ttmrg-args->path-cond-helper)))))

  (defrule ttmrg-args-syntax-p-of-strengthen-ttmrg-args->path-cond-helper
    (let ((new-args (strengthen-ttmrg-args->path-cond-helper args new-pcs)))
      (implies (ttmrg-args-syntax-p args a j)
	       (ttmrg-args-syntax-p new-args a j)))
    :hints(("Goal" :in-theory (enable strengthen-ttmrg-args->path-cond-helper
				      ttmrg-args-syntax-p
				      induct-foo)))
    :induct (induct-foo args new-pcs a j)
    :prep-lemmas (
      (define induct-foo
	  ((ttargs ttmrg-list-p) (new-pcs conj-conj-p)
	   (args pseudo-term-listp) (jargs conj-conj-p))
	(if (consp args)
	  (and (ttmrg-syntax-p (car ttargs))
	       (induct-foo (cdr ttargs) (conj-cdr new-pcs) (cdr args) (conj-cdr jargs)))
	  (not args)))))

  (defrule strengthen-ttmrg-args->path-cond-helper--unchanged-fields
    (implies
      (ttmrg-list-p args)
      (ttmrg-args-only-changed-path-cond-fn
       (strengthen-ttmrg-args->path-cond-helper args new-pcs)
       args))
    :in-theory (enable ttmrg-args-only-changed-path-cond-fn
		       strengthen-ttmrg-args->path-cond-helper)
    :prep-lemmas (
      (defrule lemma-*1/3
	(implies
	  (ttmrg-list-p args)
	  (ttmrg-args-only-changed-path-cond-fn args args))
	:in-theory (enable ttmrg-args-only-changed-path-cond-fn))))

  (defrule strengthen-ttmrg-args->path-cond-helper-strengthens-path-cond
    (implies (and (ttmrg-list-p ttargs) (alistp env))
	     (ttmrg-args-path-cond-stronger-p
	       ttargs
	       (strengthen-ttmrg-args->path-cond-helper ttargs new-pcs)
	       env))
    :in-theory (enable ttmrg-args-path-cond-stronger-p
		       strengthen-ttmrg-args->path-cond-helper))

  (defrule ttmrg-args-correct-values-of-strengthen-ttmrg-args->path-cond-helper
    (implies (and (ttmrg-args-syntax-p ttargs args jargs)
		  (alistp env)
		  (ttmrg-args-correct-values ttargs args env))
	     (ttmrg-args-correct-values
	       (strengthen-ttmrg-args->path-cond-helper ttargs new-pcs)
	       args env))
    :in-theory (enable strengthen-ttmrg-args->path-cond-helper
		       ttmrg-args-correct-values
		       ttmrg-args-syntax-p
		       induct-foo)
    :induct (induct-foo ttargs args jargs new-pcs)
    :prep-lemmas (
      (define induct-foo
	  ((ttargs ttmrg-list-p) (args pseudo-term-listp) (jargs conj-p) (new-pcs conj-conj-p))
	:returns (ok booleanp)
	(if (and (consp ttargs) (consp args) (conj-consp jargs) (conj-consp new-pcs))
	  (induct-foo (cdr ttargs) (cdr args) (conj-cdr jargs) (conj-cdr new-pcs))
	  (not (or ttargs args (not (equal jargs ''t))
		   (not (equal new-pcs ''t))))))))

  (defrule ttmrg-args-correct-judge-of-strengthen-ttmrg-args->path-cond-helper
    (implies
      (and (ttmrg-list-p ttargs)
	   (alistp env)
	   (ttmrg-args-correct-judge ttargs jargs env))
      (ttmrg-args-correct-judge
	(strengthen-ttmrg-args->path-cond-helper ttargs new-pcs)
	jargs env))
    :in-theory (enable strengthen-ttmrg-args->path-cond-helper
		       ttmrg-args-correct-judge))

  (defrule ttmrg-args-correct-path-of-strengthen-ttmrg-args->path-cond-helper
    (implies
      (and (ttmrg-list-p ttargs)
	   (alistp env)
	   (ttmrg-args-correct-path ttargs env)
	   (ev-smtcp new-pcs env))
      (ttmrg-args-correct-path
	(strengthen-ttmrg-args->path-cond-helper ttargs new-pcs) env))
    :in-theory (enable strengthen-ttmrg-args->path-cond-helper
		       strengthen-ttmrg->path-cond
		       ttmrg-args-correct-path
		       conj-fix)
    :expand ((conj-cons (conj-car new-pcs) (ttmrg->path-cond (car ttargs)))))))


(define strengthen-ttmrg-args->path-cond
    ((tterm ttmrg-p) (new-pcs conj-conj-p))
  :returns (new-tt ttmrg-p)
  (b* (((ttmrg tterm) (ttmrg-fix tterm))
       (new-args (strengthen-ttmrg-args->path-cond-helper
		   tterm.args new-pcs)))
    (change-ttmrg tterm :args new-args))
  ///
  (more-returns
    (new-tt :name strengthen-ttmrg-args->path-cond--unchanged-fields
       (ttmrg-args-only-changed->path-cond tterm new-tt)))

  (defrule syntax-p-of-strengthen-ttmrg-args->path-cond
    (implies (ttmrg-syntax-p tterm)
	     (ttmrg-syntax-p (strengthen-ttmrg-args->path-cond tterm new-pcs)))
    :in-theory (enable ttmrg-syntax-p
		       strengthen-ttmrg-args->path-cond-helper
		       strengthen-ttmrg-args->path-cond)
    :prep-lemmas (
      (acl2::defruled crock-0
	(implies (and (true-listp x) (equal (len x) 0)) (null x)))
      (defrule crock-3
	(implies (and (true-listp x) (equal (len x) 3))
		 (and (consp (cddr x)) (not (cdddr x))))
	:use((:instance crock-0 (x (cdddr x)))))
      (defrule crock-if
	(implies (and (ttmrg-syntax-p x) (equal (car (ttmrg->term x)) 'if))
		 (equal (len (ttmrg->args x)) 3))
	:expand (ttmrg-syntax-p x)))))

(local (encapsulate nil ; many lemmas for proving that
      ; strengthen-ttmrg-args->path-cond preserves ttmrg-correct-p.
      ; The most tedious part of this is handling if-expressions where each
      ; argument of the if has a different constraint for its path condition.
      ; Lemmas iffy-1 through iffy-4 seem like they should be pre-lemmas for
      ; lemma-path-cond-ifargs, but they (I observed iffy-3 and iffy-4) get
      ; used in proofs for subsequent lemmas.  So, I export them all from
      ; this encapsulation.
  (defrule lemma-correct-values
    (implies
     (and (ttmrg-correct-sk tterm)
	  (alistp env)
	  (ev-smtcp (ttmrg->path-cond tterm) env)
	  (consp (ttmrg->term tterm))
	  (not (equal (car (ttmrg->term tterm)) 'quote)))
     (ttmrg-args-correct-values
      (ttmrg->args (strengthen-ttmrg-args->path-cond
			tterm
			(constrain-ttmrg->args-path tterm state)))
      (cdr (ttmrg->term tterm))
      env))
    :in-theory (enable strengthen-ttmrg-args->path-cond)
    :use((:instance lemma-1))
    :prep-lemmas (
      (acl2::defruled lemma-1
	(implies (and (ttmrg-correct-sk tterm)
		      (alistp env)
		      (ev-smtcp (ttmrg->path-cond tterm) env)
		      (consp (ttmrg->term tterm))
		      (not (equal (car (ttmrg->term tterm)) 'quote)))
		 (and (ttmrg-args-syntax-p (ttmrg->args tterm)
					   (cdr (ttmrg->term tterm))
					   (conj-cdr (ttmrg->judgements tterm)))
		      (ttmrg-args-correct-values (ttmrg->args tterm)
						 (cdr (ttmrg->term tterm))
						 env)))
	:prep-lemmas (
	  (defrule lemma-0
	    (implies (and (ttmrg-syntax-p tterm)
			  (consp (ttmrg->term tterm))
			  (not (equal (car (ttmrg->term tterm)) 'quote)))
		     (ttmrg-args-syntax-p (ttmrg->args tterm)
					  (cdr (ttmrg->term tterm))
					  (conj-cdr (ttmrg->judgements tterm))))
	    :in-theory (enable ttmrg-syntax-p))))))

  (defrule iffy-1
    (implies
      (and (ttmrg-correct-sk tterm)
	   (equal (car (ttmrg->term tterm)) 'if))
      (equal
	(ttmrg->args (strengthen-ttmrg-args->path-cond tterm new-pcs))
	(b* (((list ttcond ttthen ttelse) (ttmrg->args tterm))
	     ((conj-list pccond pcthen pcelse) new-pcs))
	  (list (strengthen-ttmrg->path-cond ttcond pccond)
		(strengthen-ttmrg->path-cond ttthen pcthen)
		(strengthen-ttmrg->path-cond ttelse pcelse)))))
    :in-theory (enable strengthen-ttmrg-args->path-cond)
    :use((:instance iffy-syntax)
	 (:instance iffy-recursion (ttargs (ttmrg->args tterm))))
    :prep-lemmas (
      (acl2::defruled iffy-syntax
	(implies (and (ttmrg-correct-sk tterm)
		      (equal (car (ttmrg->term tterm)) 'if))
		 (let ((ttargs (ttmrg->args tterm)))
		   (and (consp (cddr ttargs)) (not (cdddr ttargs)))))
	:use((:instance ttmrg-syntax-p)))

      (acl2::defruled iffy-recursion
	(implies (and (ttmrg-list-p ttargs)
		      (consp (cddr ttargs))
		      (not (cdddr ttargs)))
		 (equal
		   (strengthen-ttmrg-args->path-cond-helper ttargs new-pcs)
		   (b* (((list ttcond ttthen ttelse) ttargs)
			((conj-list pccond pcthen pcelse) new-pcs))
		     (list (strengthen-ttmrg->path-cond ttcond pccond)
			   (strengthen-ttmrg->path-cond ttthen pcthen)
			   (strengthen-ttmrg->path-cond ttelse pcelse)))))
	:expand ((strengthen-ttmrg-args->path-cond-helper ttargs new-pcs)
		 (strengthen-ttmrg-args->path-cond-helper (cdr ttargs) (conj-cdr new-pcs))
		 (strengthen-ttmrg-args->path-cond-helper (cddr ttargs) (conj-cdr (conj-cdr new-pcs)))
		 (strengthen-ttmrg-args->path-cond-helper nil (conj-cdr (conj-cdr (conj-cdr new-pcs)))))
	:prep-lemmas (
	  (defrule conj-car/cdr-when-not-conj-consp
	    (implies (not (conj-consp x))
		     (and (equal (conj-car x) ''t)
			  (equal (conj-cdr x) ''t)))
	    :in-theory (enable conj-car conj-cdr))

	  (defrule strengthen-ttmrg->path-cond-of-t
	    (implies (ttmrg-p tterm)
		     (equal (strengthen-ttmrg->path-cond tterm ''t) tterm))
	    :in-theory (enable strengthen-ttmrg->path-cond))))))

  (defrule iffy-2
    (implies (and (ttmrg-p tterm)
		  (conj-p new-pc)
		  (alistp env))
	     (implies (and (ev-smtcp (ttmrg->path-cond tterm) env)
			   (ev-smtcp new-pc env))
		      (ev-smtcp (ttmrg->path-cond
				  (strengthen-ttmrg->path-cond tterm new-pc)) env)))
    :in-theory (enable strengthen-ttmrg->path-cond))

  (defrule iffy-3
    (implies
      (and
	(ttmrg-syntax-p tterm)
	(consp (ttmrg->term tterm))
	(equal (car (ttmrg->term tterm)) 'if))
      (and (ttmrg-p (car (ttmrg->args tterm)))
	   (ttmrg-p (cadr (ttmrg->args tterm)))
	   (ttmrg-p (caddr (ttmrg->args tterm)))))
   :in-theory (enable ttmrg-syntax-p))

  (defrule iffy-4
    (implies
      (and
	(ttmrg-correct-sk tterm)
	(alistp env)
	(conj-conj-p new-pcs)
	(consp (ttmrg->term tterm))
	(equal (car (ttmrg->term tterm)) 'if)
	(ev-smtcp (ttmrg->path-cond (car (ttmrg->args tterm)))
		  env)
	(ev-smtcp (conj-car new-pcs) env))
      (b* ((cond-pc (ev-smtcp (ttmrg->path-cond
				(strengthen-ttmrg->path-cond
				  (car (ttmrg->args tterm))
				  (conj-car new-pcs)))
			      env))
	   (cond-val (ev-smtcp (ttmrg->term (car (ttmrg->args tterm))) env))
	   (x-arg (if cond-val
		       (cadr (ttmrg->args tterm))
		       (caddr (ttmrg->args tterm))))
	   (x-pc (conj-car (conj-cdr (if cond-val new-pcs (conj-cdr new-pcs))))))
	(and cond-pc
	     (implies (and (ev-smtcp (ttmrg->path-cond x-arg) env)
			   (ev-smtcp x-pc env))
		      (ev-smtcp (ttmrg->path-cond
				  (strengthen-ttmrg->path-cond x-arg x-pc))
				env))))))

  (defrule lemma-path-cond-ifargs
    (implies
      (and (ev-smtcp-meta-extract-global-facts)
	   (ttmrg-correct-sk tterm)
	   (alistp env)
	   (ev-smtcp (ttmrg->path-cond tterm) env)
	   (consp (ttmrg->term tterm))
	   (equal (car (ttmrg->term tterm)) 'if))
      (let* ((args (ttmrg->args tterm))
	     (new-args
	      (ttmrg->args
		(strengthen-ttmrg-args->path-cond
		  tterm (constrain-ttmrg->args-path tterm state))))
	     (cond-val (ev-smtcp (ttmrg->term (car args)) env)))
	(and (ev-smtcp (ttmrg->path-cond (car new-args)) env)
	     (if cond-val
	       (ev-smtcp (ttmrg->path-cond (cadr new-args)) env)
	       (ev-smtcp (ttmrg->path-cond (caddr new-args)) env)))))
    :in-theory (disable correctness-of-constrain-ttmrg->args-path
			ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk)
    :use((:instance correctness-of-constrain-ttmrg->args-path)
	 (:instance ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk)))

  (defrule lemma-correct-judgements
    (implies
     (and
       (ev-smtcp-meta-extract-global-facts)
       (ttmrg-correct-sk tterm)
       (alistp env)
       (ev-smtcp (ttmrg->path-cond tterm) env)
       (consp (ttmrg->term tterm))
       (not (equal (car (ttmrg->term tterm)) 'quote)))
     (ttmrg-args-correct-judge
       (ttmrg->args (strengthen-ttmrg-args->path-cond
			 tterm new-pcs))
       (conj-cdr (ttmrg->judgements tterm))
       env))
    :expand ((strengthen-ttmrg-args->path-cond tterm new-pcs))
    :in-theory (disable ttmrg-args-correct-judge-of-strengthen-ttmrg-args->path-cond-helper
			ttmrg-args-correct-judge-when-ttmrg-correct-sk)
    :use((:instance ttmrg-args-correct-judge-of-strengthen-ttmrg-args->path-cond-helper
		    (ttargs (ttmrg->args tterm))
		    (jargs (conj-cdr (ttmrg->judgements tterm))))
	 (:instance ttmrg-args-correct-judge-when-ttmrg-correct-sk)))

  (defrule lemma-correct-path
    (implies
     (and (ev-smtcp-meta-extract-global-facts)
	  (not (equal (car (ttmrg->term tterm)) 'if))
	  (ttmrg-correct-sk tterm)
	  (alistp env)
	  (ev-smtcp (ttmrg->path-cond tterm) env)
	  (consp (ttmrg->term tterm))
	  (not (equal (car (ttmrg->term tterm)) 'quote)))
     (ttmrg-args-correct-path
       (ttmrg->args (strengthen-ttmrg-args->path-cond
			 tterm
			 (constrain-ttmrg->args-path tterm state)))
       env))
    :in-theory (e/d (strengthen-ttmrg-args->path-cond)
		    (ttmrg-args-correct-path-when-ttmrg-correct-sk
		     ttmrg-args-correct-path-of-strengthen-ttmrg-args->path-cond-helper
		     correctness-of-constrain-ttmrg->args-path))
    :use((:instance ttmrg-args-correct-path-when-ttmrg-correct-sk)
	 (:instance ttmrg-args-correct-path-of-strengthen-ttmrg-args->path-cond-helper
		    (ttargs (ttmrg->args tterm))
		    (new-pcs (constrain-ttmrg->args-path tterm state)))
	 (:instance correctness-of-constrain-ttmrg->args-path)))

  (defrule ttmrg-correct-sk-of-strengthen-ttmrg-args->path-cond
    (implies
      (and (ev-smtcp-meta-extract-global-facts)
	   (ttmrg-correct-sk tterm))
      (ttmrg-correct-sk (strengthen-ttmrg-args->path-cond
			     tterm
			     (constrain-ttmrg->args-path tterm state))))
    :expand ((ttmrg-correct-sk (strengthen-ttmrg-args->path-cond
				     tterm
				     (constrain-ttmrg->args-path tterm state))))
    :in-theory (disable lemma-path-cond-ifargs)
    :use((:instance lemma-path-cond-ifargs
		    (env (ttmrg-correct-sk-witness (strengthen-ttmrg-args->path-cond
						     tterm
						     (constrain-ttmrg->args-path tterm state)))))))

  (defrule ttmrg-args-correct-p-of-strengthen-ttmrg-args->path-cond
    (IMPLIES
      (and (ev-smtcp-meta-extract-global-facts)
	   (ttmrg-args-correct-p (ttmrg->args tterm)))
      (ttmrg-args-correct-p
	   (ttmrg->args (strengthen-ttmrg-args->path-cond
			     tterm
			     (constrain-ttmrg->args-path tterm state)))))
    :in-theory (enable strengthen-ttmrg-args->path-cond))))

(defrule correctness-of-strengthen-ttmrg-args->path-cond
  (implies (and (ev-smtcp-meta-extract-global-facts)
		(ttmrg-correct-p tterm))
	   (ttmrg-correct-p
	     (strengthen-ttmrg-args->path-cond
	       tterm
	       (constrain-ttmrg->args-path tterm state))))
  :in-theory (disable strengthen-ttmrg-args->path-cond)
  :expand ((ttmrg-correct-p tterm)
	   (ttmrg-correct-p (strengthen-ttmrg-args->path-cond
			      tterm
			      (constrain-ttmrg->args-path tterm state)))))
