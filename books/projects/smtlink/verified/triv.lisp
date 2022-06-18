;; Copyright (C) 2022, University of British Columbia)
;; Initial version by Mark Greenstreet.
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")

; This book has three main exports:
;   Function that make correct ttmrg and ttmrg-args values from pseudo-termp
;       and pseudo-term-listp objects respectively.  The functions we export
;       are
;     make-ttmrg-trivial and make-ttmrg-args-trivial.
;   Theorems that show that these functions produce values satisfying
;       ttmrg-correct-p and ttmrg-args-correct-p.  These theorems are
;     ttmrg-correct-p-of-make-ttmrg-trivial and
;     ttmrg-args-correct-p-of-mke-ttmrg-args-trivial.
;   Theorems that show that term satisfies pseudo-term-syntax-p, then
;       (equal (ttmrg->term (make-ttmrg-trivial term)) term)
;     and likewise for make-ttmrg-args-trivial.  These theorems are
;       make-ttmrg-trivial-when-pseudo-term-syntax-p and
;       make-ttmrg-args-trivial-when-pseudo-term-list-syntax-p and

(include-book "ttmrg")

(set-induction-depth-limit 1)

; Mark is impatient
(local (in-theory (disable
  pseudo-termp pseudo-term-listp
  acl2::pseudo-termp-opener
  acl2::pseudo-termp-of-car-when-pseudo-term-listp
  acl2::pseudo-term-listp-of-cdr-when-pseudo-term-listp
  pseudo-term-listp-of-cdr-of-pseudo-termp
  acl2::pseudo-term-listp-of-cdr-when-pseudo-term-listp
  pseudo-termp-when-conj-p
  lambda-of-pseudo-lambdap
  symbol-listp alistp true-listp boolean-listp
  acl2::symbolp-of-car-when-symbol-listp
  acl2::symbol-listp-of-cdr-when-symbol-listp
  pseudo-term-listp-of-symbol-listp
  default-car member-equal conj-p-when-conj-consp
  acl2-count)))


(local (defrule lemma-for-make-ttmrg-trivial-measure
  (implies (consp (pseudo-term-syntax-fix term))
	   (< (acl2-count (cdr (pseudo-term-syntax-fix term)))
	      (acl2-count term)))
  :expand ((pseudo-term-syntax-fix term))
  :in-theory (disable acl2-count-of-pseudo-term-list-syntax-fix)
  :use((:instance acl2-count-of-pseudo-term-list-syntax-fix (args (cdr term))))))

(defines make-ttmrg-trivial
  :flag-local nil
  :verify-guards nil
  (define make-ttmrg-trivial ((term pseudo-term-syntax-p))
    :returns (tterm ttmrg-p)
    :flag term
    (b* ((term (pseudo-term-syntax-fix term))
	 (tterm (make-ttmrg :term term
			    :path-cond ''t
			    :args nil
			    :top-judgement ''t))
	 ((if (or (atom term) (equal (car term) 'quote))) tterm)
	 ((cons fn args) term)
	 (ttargs (make-ttmrg-args-trivial args))
	 (args-triv (ttmrg-list->terms ttargs))
	 )
      (change-ttmrg tterm :term (cons fn args-triv) :args ttargs)))

  (define make-ttmrg-args-trivial ((args pseudo-term-list-syntax-p))
    :returns (ttargs ttmrg-list-p)
    :flag args
    (b* (((unless (consp args)) nil)
	 ((cons hd tl) args))
       (cons (make-ttmrg-trivial hd)
	     (make-ttmrg-args-trivial tl))))
  ///
  (verify-guards make-ttmrg-trivial
    :hints(("Goal" :in-theory (enable pseudo-term-syntax-p
				      pseudo-term-list-syntax-p))))

  ; Show that if term satisfies pseudo-term-syntax-p, then
  ;   (equal (ttmrg->term (make-ttmrg-trivial term)) term)
  ; We need a few lemmas for the induction cases, hence the encapsulation.
  (local (defrule lemma-term
    (implies (and (pseudo-term-syntax-p term)
		  (or (not (consp term))
		      (equal (car term) 'quote)
		      (equal (ttmrg-list->terms (make-ttmrg-args-trivial (cdr term)))
			     (cdr term))))
	     (equal (ttmrg->term (make-ttmrg-trivial term)) term))
    :expand ((pseudo-term-syntax-p term)
	     (make-ttmrg-trivial term))))

  (local (defrule lemma-args
    (equal (ttmrg-list->terms
		(make-ttmrg-args-trivial (cons term args)))
	   (cons (ttmrg->term (make-ttmrg-trivial term))
		 (ttmrg-list->terms (make-ttmrg-args-trivial args))))
    :in-theory (enable ttmrg-list->terms)
    :expand ((make-ttmrg-args-trivial (cons term args)))))

  (defthm-make-ttmrg-trivial-flag
    (defthm make-ttmrg-trivial-when-pseudo-term-syntax-p
      (implies (pseudo-term-syntax-p term)
	       (equal (ttmrg->term (make-ttmrg-trivial term)) term))
      :flag term)

    (defthm make-ttmrg-args-trivial-when-pseudo-term-list-syntax-p
      (implies (pseudo-term-list-syntax-p args)
	       (equal (ttmrg-list->terms (make-ttmrg-args-trivial args)) args))
      :flag args)

    :hints(("Goal"
      :in-theory (e/d (pseudo-term-syntax-p pseudo-term-list-syntax-p)
		      (make-ttmrg-trivial make-ttmrg-args-trivial))))))


; I don't want to clutter the namespace of any book that includes this book.
; The theorems in the following encapsulation are lemmas used in the proof
; that (ttmrg-correct-p (make-ttmrg-trivial term)) and likewise for
; make-ttmrg-args-trivial.
(local (encapsulate nil
  (local (in-theory (enable
    make-ttmrg-trivial make-ttmrg-args-trivial ttmrg-list->terms
    ttmrg-list->judgements ttmrg-args-correct-values ttmrg-args-correct-path)))

  (defrule match-len-of-make-ttmrg-args-trivial
    (match-len (make-ttmrg-args-trivial args) args)
    :in-theory (enable match-len)
    :induct (len args))

  (defthm-make-ttmrg-trivial-flag
    (defthm ttmrg-syntax-p-of-make-ttmrg-trivial
      (implies (pseudo-term-syntax-p term)
               (ttmrg-syntax-p (make-ttmrg-trivial term)))
      :flag term)

    (defthm ttmrg-args-syntax-p-of-make-ttmrg-args-trivial
      (implies (pseudo-term-list-syntax-p args)
	       (ttmrg-args-syntax-p (make-ttmrg-args-trivial args)))
      :flag args)
    :hints(("Goal"
      :in-theory (enable ttmrg-syntax-p ttmrg-args-syntax-p
			 pseudo-term-syntax-p pseudo-term-list-syntax-p))))

  (acl2::defruled make-ttmrg-args-trivial-correct-values
    (ttmrg-args-correct-values
      (make-ttmrg-args-trivial args)
      (ttmrg-list->terms (make-ttmrg-args-trivial args)) env)
    :induct (len args))

  (defrule make-ttmrg-trivial->path-cond
    (equal (ttmrg->path-cond (make-ttmrg-trivial term)) ''t)
    :expand (make-ttmrg-trivial term))

  (defrule ttmrg-args-correct-path-of-make-ttmrg-trivial->args
    (ttmrg-args-correct-path
      (ttmrg->args (make-ttmrg-trivial term)) env)
    :expand ((make-ttmrg-trivial term)
	     (ttmrg-args-correct-path nil env))
    :prep-lemmas (
      (defrule make-ttmrg-args-trivial-correct-path
	(ttmrg-args-correct-path
	  (make-ttmrg-args-trivial args) env)
	:induct (len args))))

  (defrule make-ttmrg-trivial->top-judgement
    (equal (ttmrg->top-judgement (make-ttmrg-trivial term)) ''t)
    :expand (make-ttmrg-trivial term))

  (local (in-theory (disable
    make-ttmrg-trivial make-ttmrg-args-trivial ttmrg-list->terms
    ttmrg-list->judgements ttmrg-args-correct-values ttmrg-args-correct-path)))

  (defrule ttmrg->path-cond-of-if-args
    (implies (pseudo-term-syntax-p term)
      (and (equal (ttmrg->path-cond (car (ttmrg->args (make-ttmrg-trivial term)))) ''t)
	   (equal (ttmrg->path-cond (cadr (ttmrg->args (make-ttmrg-trivial term)))) ''t)
	   (equal (ttmrg->path-cond (caddr (ttmrg->args (make-ttmrg-trivial term)))) ''t)))
    :expand ((make-ttmrg-trivial term)
	     (make-ttmrg-args-trivial (cdr term))
	     (make-ttmrg-args-trivial (cddr term))
	     (make-ttmrg-args-trivial (cdddr term))))


  (defrule ttmrg-correct-sk-of-make-ttmrg-trivial
    (implies (pseudo-term-syntax-p term)
	     (ttmrg-correct-sk (make-ttmrg-trivial term)))
    :in-theory (enable ttmrg-correct-sk)
    :prep-lemmas (
      (acl2::defrule lemma-1
	(implies (and (pseudo-term-syntax-p term)
		      (pseudo-term-listp args)
		      (not (equal (car term) 'quote)))
		 (pseudo-termp (cons (car term) args)))
	:in-theory (enable pseudo-term-syntax-p pseudo-termp))

      (acl2::defrule lemma-2
	(implies
	  (and (pseudo-term-syntax-p term)
	       (consp term)
	       (not (equal (car term) 'quote)))
	  (pseudo-term-list-syntax-p (cdr term)))
	:expand (pseudo-term-syntax-p term))

      (acl2::defrule lemma-3
	(implies
	  (and (pseudo-term-syntax-p term)
	       (consp term)
	       (not (equal (car term) 'quote)))
	  (ttmrg-args-correct-values
	    (ttmrg->args (make-ttmrg-trivial term))
	    (cdr term)
	    env))
	:expand ((make-ttmrg-trivial term))
	:in-theory (disable make-ttmrg-args-trivial-when-pseudo-term-list-syntax-p)
	:use((:instance
	       make-ttmrg-args-trivial-when-pseudo-term-list-syntax-p
	       (args (cdr term)))
	     (:instance make-ttmrg-args-trivial-correct-values
			  (args (cdr term)))))))

  ; The main results of this encapsulation:
  ;   ttmrg-correct-p-of-make-ttmrg-trivial-lemma, and
  ;   ttmrg-args-correct-p-of-mak-ttmrg-args-trivial-lemma
  ; These are "lemmas" because they include the hypotheses
  ; (pseduto-term-syntax-p term) and (pseudo-term-list-syntax-p args)
  ; respectively.  We drop these hypotheses shortly.
  (encapsulate nil
    (local (defrule ttmrg-args-correct-p-of-make-ttmrg-trivial->args
      (implies (and (pseudo-term-syntax-p term)
		    (ttmrg-args-correct-p (make-ttmrg-args-trivial (cdr term))))
	       (ttmrg-args-correct-p (ttmrg->args (make-ttmrg-trivial term))))
      :expand ((make-ttmrg-trivial term))))

    (local (defrule pseudo-term-list-syntax-p-of-args-when-pseudo-term-syntax-p
      (implies (and (pseudo-term-syntax-p term)
		    (consp term)
		    (not (equal (car term) 'quote)))
	       (pseudo-term-list-syntax-p (cdr term)))
      :expand ((pseudo-term-syntax-p term))))

    (defthm-make-ttmrg-trivial-flag
      (defthm ttmrg-correct-p-of-make-ttmrg-trivial-lemma
	(implies (pseudo-term-syntax-p term)
	  (ttmrg-correct-p (make-ttmrg-trivial term)))
	:flag term)

      (defthm ttmrg-args-correct-p-of-make-ttmrg-args-trivial-lemma
	(implies (pseudo-term-list-syntax-p args)
		 (ttmrg-args-correct-p (make-ttmrg-args-trivial args)))
	:flag args)
      :hints(("Goal"
        :in-theory (enable ttmrg-correct-p ttmrg-args-correct-p
			   make-ttmrg-args-trivial pseudo-term-list-syntax-p)))))

    (acl2::defruled make-ttmrg-trivial-of-pseudo-term-syntax-fix
      (equal (make-ttmrg-trivial (pseudo-term-syntax-fix term))
	     (make-ttmrg-trivial term))
      :expand ((make-ttmrg-trivial term)
	       (make-ttmrg-trivial (pseudo-term-syntax-fix term))))

    (acl2::defruled make-ttmrg-args-trivial-of-pseudo-term-list-syntax-fix
	(equal (make-ttmrg-args-trivial (pseudo-term-list-syntax-fix args))
	       (make-ttmrg-args-trivial args))
	:in-theory (enable make-ttmrg-args-trivial pseudo-term-list-syntax-fix
			   make-ttmrg-trivial-of-pseudo-term-syntax-fix)
	:induct (len args))))


(defrule ttmrg-correct-p-of-make-ttmrg-trivial
  (ttmrg-correct-p (make-ttmrg-trivial term))
  :use((:instance make-ttmrg-trivial-of-pseudo-term-syntax-fix)))

(defrule ttmrg-args-correct-p-of-make-ttmrg-args-trivial
  (ttmrg-args-correct-p (make-ttmrg-args-trivial args))
  :use((:instance make-ttmrg-args-trivial-of-pseudo-term-list-syntax-fix)))
