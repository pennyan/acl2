;; Copyright (C) 2015, University of British Columbia)
;; Originally written by Yan Peng (December 30th 2019)
;; Edited by Mark Greenstreet
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "ttmrg")

(set-induction-depth-limit 1)

; Mark is impatient
(local (in-theory (disable symbol-listp member-equal default-car default-cdr true-listp len
  pseudo-termp symbol-listp alistp member-equal boolean-listp
  LAMBDA-OF-PSEUDO-LAMBDAP
  ACL2::PSEUDO-LAMBDAP-WHEN-MEMBER-EQUAL-OF-PSEUDO-LAMBDA-LISTP
  CAR-IS-IF-WHEN-CONJ-CONSP
  ACL2::O<=-O-FINP-DEF
  CONSP-OF-CDR-OF-PSEUDO-LAMBDAP
  ACL2::PSEUDO-LAMBDAP-OF-CAR-WHEN-PSEUDO-TERMP
  PSEUDO-TERMP-WHEN-CONJ-P
  TTMRG-P-OF-CAR-WHEN-TTMRG-LIST-P)))

(defines ttmrg-trivial
  (define ttmrg-trivial-p ((tterm acl2::any-p))
    :returns (ok booleanp)
    :flag term
    (b* (((unless (ttmrg-syntax-p tterm)) nil)
	 ((ttmrg tterm) tterm)
	 (term tterm.term)
	 ((unless (equal tterm.path-cond ''t)) nil)
	 ((unless (equal tterm.judgements ''t)) nil)
	 ((if (atom term)) (null tterm.args))
	 (fn (car term)))
      (if (equal fn 'quote)
	(null tterm.args)
	(ttmrg-args-trivial-p tterm.args))))
	  
  (define ttmrg-args-trivial-p ((typed-args ttmrg-list-p))
    :returns (ok booleanp)
    :flag args
    (if (consp typed-args)
      (and (ttmrg-trivial-p (car typed-args))
           (ttmrg-args-trivial-p (cdr typed-args)))
      (null typed-args)))

  ///
  (more-returns ttmrg-trivial-p
    (ok :name ttmrg-trivial-p-implies-ttmrg-syntax-p
	(implies ok (ttmrg-syntax-p tterm))
	:rule-classes (:rewrite :forward-chaining)))

  (more-returns ttmrg-args-trivial-p
    (ok :name ttmrg-args-trivial-p-implies-ttmrg-list-syntax-p
	(implies ok (ttmrg-list-syntax-p typed-args))
	:hints(("Goal" :in-theory (enable ttmrg-args-trivial-p ttmrg-list-syntax-p)))
	:rule-classes (:rewrite :forward-chaining)))

  (encapsulate nil
   (local (defrule lemma-*1/2
     (implies (ttmrg-trivial-p tterm)
	      (b* (((ttmrg tterm) tterm)
		   (term tterm.term)
		   (path-cond tterm.path-cond)
		   (judgements tterm.judgements))
		 (and (equal path-cond ''t)
		      (equal judgements ''t)
		      (implies (and (consp term) (equal (car term) 'if))
			       (b* (((list ? thenx elsex) tterm.args))
				  (and (equal (ttmrg->path-cond thenx) ''t)
				       (equal (ttmrg->path-cond elsex) ''t)))))))
     :in-theory (enable ttmrg-trivial-p)
     :use ((:instance ttmrg-args-trivial-p (typed-args (ttmrg->args tterm)))
	   (:instance ttmrg-args-trivial-p (typed-args(cdr (ttmrg->args tterm))))
	   (:instance ttmrg-args-trivial-p (typed-args(cddr (ttmrg->args tterm)))))))
			
   (defthm-ttmrg-trivial-flag ttmrg-trivial-implies-correct
     (defthm ttmrg-trivial-implies-correct
       (implies (ttmrg-trivial-p tterm) (ttmrg-correct-p tterm))
       :flag term)
     (defthm ttmrg-trivial-args-implies-correct-list
       (implies (ttmrg-args-trivial-p typed-args) (ttmrg-args-correct-p typed-args))
       :flag args)
     :hints(("Goal"
       :in-theory (enable ttmrg-correct-p ttmrg-args-correct-p ttmrg-correct-sk
			  ttmrg-trivial-p ttmrg-args-trivial-p))))))

(defines make-ttmrg-trivial
  :verify-guards nil
  :hints(("Goal" :in-theory (enable pseudo-term-fix)))
  :guard-hints(("Goal" :in-theory (enable pseudo-termp)))
  (define make-ttmrg-trivial ((term pseudo-termp))
    :returns (tterm ttmrg-p)
    :flag term
    (b* ((term (pseudo-term-fix term))
	 ((unless (and (consp term) (not (equal (car term) 'quote))))
	  (make-ttmrg :term term :path-cond ''t :args nil :judgements ''t))
	 ((cons fn args) term)
	 ((if (consp fn))
	  (make-ttmrg :term 'unexpected-lambda-expresion :path-cond ''t :args nil :judgements ''t))
	 ((if (booleanp fn))
	  (make-ttmrg :term 'invalid-function-symbol :path-cond ''t :args nil :judgements ''t))
	 ((if (and (equal fn 'if) (not (and (consp args) (consp (cdr args)) (consp (cddr args)) (not (cdddr args))))))
	  (make-ttmrg :term 'bad-if :path-cond ''t :args nil :judgements ''t))
	 (ttargs (make-ttmrg-args-trivial args)))
       (make-ttmrg :term (cons fn (ttmrg-list->terms ttargs))
		   :path-cond ''t
		   :args ttargs
		   :judgements (conj-cons ''t (ttmrg-list->judgements ttargs)))))

  (define make-ttmrg-args-trivial ((args pseudo-term-listp))
    :returns (ttargs ttmrg-list-p)
    :flag args
    (b* (((unless (consp args)) nil)
	 ((cons hd tl) args))
       (cons (make-ttmrg-trivial hd)
	     (make-ttmrg-args-trivial tl))))
  ///
  (local (defrule path-cond-of-make-ttmrg-trivial
      (equal (ttmrg->path-cond (make-ttmrg-trivial term)) ''t)
      :expand ((make-ttmrg-trivial term))))

  (local (defrule make-trival-ttmrg-args-path-cond
    (args-path-cond-match-parent ''t (make-ttmrg-args-trivial args))
    :prep-lemmas (
      (defrule lemma-1
	(implies
	     (and (consp args)
		  (args-path-cond-match-parent ''t
					       (make-ttmrg-args-trivial (cdr args))))
	     (args-path-cond-match-parent ''t
					  (make-ttmrg-args-trivial args)))
	:in-theory (enable make-ttmrg-args-trivial args-path-cond-match-parent)))
    :enable (args-path-cond-match-parent)
    :in-theory (enable len)
    :induct (len args)))

  (verify-guards make-ttmrg-trivial)

  ; working our way up to showing that (ttmrg-correct-p (make-ttmrg trivial term))
  ; I believe that ttmrg-syntax-p-of-make-ttmrg-trivial should be local because it
  ; will be subsumed by ttmrg-correct-p-of-make-ttmrg-trivial below.
  (local (defthm-make-ttmrg-trivial-flag
    (defthm ttmrg-syntax-p-of-make-ttmrg-trivial
      (ttmrg-syntax-p (make-ttmrg-trivial term))
      :flag term)

    (defthm ttmrg-args-syntax-p-of-make-ttmrg-args-trivial
      (let ((ttargs (make-ttmrg-args-trivial args)))
	(ttmrg-args-syntax-p (ttmrg-list->terms ttargs)
			     ttargs
			     (ttmrg-list->judgements ttargs)))
      :flag args)
    :hints(("Goal" :in-theory (enable make-ttmrg-trivial make-ttmrg-args-trivial
				      ttmrg-list->terms ttmrg-list->judgements
				      ttmrg-syntax-p ttmrg-args-syntax-p)))))

  ; the judgements of a make-trivial value evaluate to t
  (local (defthm-make-ttmrg-trivial-flag
    (defthm ev-of-make-ttmrg-trivial->judgements
      (implies (alistp env)
	       (ev-smtcp (ttmrg->judgements (make-ttmrg-trivial term)) env))
      :flag term)
    (defthm ev-of-make-ttmrg-args-trivial->judgements
      (implies (alistp env)
	       (ev-smtcp (ttmrg-list->judgements (make-ttmrg-args-trivial args)) env))
      :flag args)
    :hints(("Goal" :in-theory (enable make-ttmrg-trivial make-ttmrg-args-trivial
				      ttmrg-list->judgements)))))

  (defthm-make-ttmrg-trivial-flag
    (defthm ttmrg-correct-p-of-make-ttmrg-trivial
      (ttmrg-correct-p (make-ttmrg-trivial term))
      :flag term)

    (defthm ttmrg-args-correct-p-of-make-ttmrg-args-trivial 
      (ttmrg-args-correct-p (make-ttmrg-args-trivial args))
      :flag args)

    :hints(("Goal" :in-theory (enable make-ttmrg-trivial make-ttmrg-args-trivial
				      ttmrg-correct-p ttmrg-args-correct-p ttmrg-correct-sk
				      ttmrg-syntax-p ttmrg-list-syntax-p))))


  (encapsulate ()
    ; Show that if term satisfies pseudo-term-syntax-p, then
    ;   (equal (ttmrg->term (make-ttmrg-trivial term)) term)
    ; We need a few lemmas for the induction cases, hence the encapsulation.
    (local(defrule lemma-*1/1
      (implies (and (pseudo-term-syntax-p term)
		    (equal (car term) 'quote))
	       (equal (ttmrg->term (make-ttmrg-trivial term)) term))
      :expand ((pseudo-term-syntax-p term)
	       (make-ttmrg-trivial term))))

    (local (defrule lemma-*1/5&9
      (implies (and (pseudo-term-syntax-p term)
		    (equal (ttmrg-list->terms (make-ttmrg-args-trivial (cdr term)))
			   (cdr term)))
	       (equal (ttmrg->term (make-ttmrg-trivial term)) term))
      :expand ((pseudo-term-syntax-p term)
	       (make-ttmrg-trivial term))))

    (local (defrule lemma-*1/10
      (implies (and (pseudo-term-syntax-p term)
		    (not (consp term)))
	       (equal (ttmrg->term (make-ttmrg-trivial term)) term))
      :expand ((pseudo-term-syntax-p term)
	       (make-ttmrg-trivial term))))

    (local (defrule lemma-*1/11
      (implies (and (equal (ttmrg->term (make-ttmrg-trivial car-args)) car-args)
		    (equal (ttmrg-list->terms (make-ttmrg-args-trivial cdr-args)) cdr-args))
	       (equal (ttmrg-list->terms (cons (make-ttmrg-trivial car-args)
					       (make-ttmrg-args-trivial cdr-args)))
		      (cons car-args cdr-args)))
      :in-theory (enable ttmrg-list->terms)))

    (defthm-make-ttmrg-trivial-flag
      (defthm make-ttmrg-trivial-when-pseudo-term-syntax-p
	(implies (pseudo-term-syntax-p term)
		 (equal (ttmrg->term (make-ttmrg-trivial term)) term))
	:flag term)

      (defthm make-ttmrg-args-trivial-when-pseudo-term-list-syntax-p
	(implies (pseudo-term-list-syntax-p args)
		 (equal (ttmrg-list->terms (make-ttmrg-args-trivial args)) args))
	:flag args)

      :hints(("Goal" :in-theory (enable pseudo-term-syntax-p pseudo-term-list-syntax-p))))))
