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


(defines make-ttmrg-trivial
  :flag-local nil
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
  (verify-guards make-ttmrg-trivial))


; I don't want to clutter the namespace of any book that includes this book.
; The theorems in the following encapsulation are lemmas used in the proof
; that (ttmrg-correct-p (make-ttmrg-trivial term)) and likewise for
; make-ttmrg-args-trivial.
(local (encapsulate nil
  (in-theory (enable make-ttmrg-trivial make-ttmrg-args-trivial ttmrg-list->terms len
		     ttmrg-list->judgements
		     ttmrg-args-correct-values ttmrg-args-correct-path ttmrg-args-correct-judge))

  (defrule make-ttmrg-args-trivial-correct-values
    (ttmrg-args-correct-values
      (make-ttmrg-args-trivial args)
      (ttmrg-list->terms (make-ttmrg-args-trivial args)) env)
    :induct (len args))

  (defrule make-ttmrg-trivial-correct-values
    (implies (and (consp (ttmrg->term (make-ttmrg-trivial term)))
		  (not (equal (car (ttmrg->term (make-ttmrg-trivial term))) 'quote)))
	     (ttmrg-args-correct-values
			   (ttmrg->args (make-ttmrg-trivial term))
			   (cdr (ttmrg->term (make-ttmrg-trivial term)))
			   env))
    :expand ((make-ttmrg-trivial term)))


  (defrule make-ttmrg-trivial-correct-path
    (equal (ttmrg->path-cond (make-ttmrg-trivial term)) ''t)
    :expand (make-ttmrg-trivial term))

  (defrule ttmrg-args-correct-path-of-make-ttmrg-trivial->args
    (ttmrg-args-correct-path
      (ttmrg->args (make-ttmrg-trivial term)) path-cond env)
    :expand ((make-ttmrg-trivial term)
	     (ttmrg-args-correct-path nil path-cond env))
    :prep-lemmas (
      (defrule make-ttmrg-args-trivial-correct-path
	(ttmrg-args-correct-path
	  (make-ttmrg-args-trivial args) path-cond env)
	:induct (len args))))


  (defrule ttmrg-args-correct-judge-of-make-ttmrg-trivial->args
    (ttmrg-args-correct-judge
      (ttmrg->args (make-ttmrg-trivial term))
      (conj-cdr  (ttmrg->judgements (make-ttmrg-trivial term)))
      env)
    :expand ((make-ttmrg-trivial term)
	     (ttmrg-args-correct-judge nil ''t env))
    :prep-lemmas (
      (defrule make-ttmrg-args-trivial-correct-judge
	(ttmrg-args-correct-judge
	  (make-ttmrg-args-trivial args)
	  (ttmrg-list->judgements (make-ttmrg-args-trivial args))
	  env)
	:induct (len args))))


  (defrule quoted-term-facts
    (implies (and (pseudo-termp x) (consp x) (equal (car x) 'quote))
	     (and (consp x) (consp (cdr x)) (not (cddr x))))
    :in-theory (enable pseudo-termp))

  (defthm-make-ttmrg-trivial-flag
    (defthm ttmrg-syntax-p-of-make-ttmrg-trivial
      (ttmrg-syntax-p (make-ttmrg-trivial term))
      :flag term)

    (defthm ttmrg-args-syntax-p-of-make-ttmrg-args-trivial
      (let ((ttargs (make-ttmrg-args-trivial args)))
	(ttmrg-args-syntax-p ttargs
			     (ttmrg-list->terms ttargs)
			     (ttmrg-list->judgements ttargs)))
      :flag args)
    :hints(("Goal" :in-theory (enable ttmrg-syntax-p ttmrg-args-syntax-p))))

  (define conj-triv ((x conj-p))
    :returns (ok booleanp)
    :measure (acl2-count x)
    (if (conj-consp x)
      (and (conj-p (conj-car x))
	   (conj-triv (conj-car x))
	   (conj-triv (conj-cdr x)))
      (equal x ''t))
    ///
    (defrule conj-p-when-conj-triv
      (implies (conj-triv x) (conj-p x))
      :in-theory (enable conj-triv conj-p))

    (defrule conj-triv-of-conj-cons
      (implies (and (conj-triv hd) (conj-triv tl))
	       (conj-triv (conj-cons hd tl)))
      :in-theory (enable conj-triv))

    (defrule ev-smtcp-when-conj-triv
      (implies (and (conj-triv x) (alistp env)) (ev-smtcp x env))
      :in-theory (enable conj-triv)
      :prep-lemmas (
	(defrule prep-lemma
	  (implies (and (conj-consp x)
			(ev-smtcp (conj-car x) env)
			(ev-smtcp (conj-cdr x) env)
			(alistp env))
		    (ev-smtcp x env))
	  :use((:instance ev-smtcp-of-conj-cons (hd (conj-car x)) (tl (conj-cdr x)))))))

    (defthm-make-ttmrg-trivial-flag
      (defthm conj-triv-of-make-ttmrg-trivial->judgements
	(conj-triv (ttmrg->judgements (make-ttmrg-trivial term)))
	:flag term)

      (defthm conj-triv-of-make-ttmrg-trivial-args
	(conj-triv (ttmrg-list->judgements (make-ttmrg-args-trivial args)))
	:flag args)))

  (in-theory (disable make-ttmrg-trivial make-ttmrg-args-trivial ttmrg-list->terms len
		     ttmrg-list->judgements
		     ttmrg-args-correct-values ttmrg-args-correct-path ttmrg-args-correct-judge))


  (defrule ttmrg->path-cond-of-if-args
    (and (equal (ttmrg->path-cond (car (ttmrg->args (make-ttmrg-trivial term)))) ''t)
	 (equal (ttmrg->path-cond (cadr (ttmrg->args (make-ttmrg-trivial term)))) ''t)
	 (equal (ttmrg->path-cond (caddr (ttmrg->args (make-ttmrg-trivial term)))) ''t))
    :expand ((make-ttmrg-trivial term)
	     (make-ttmrg-args-trivial (cdr (pseudo-term-fix term)))
	     (make-ttmrg-args-trivial (cddr (pseudo-term-fix term)))
	     (make-ttmrg-args-trivial (cdddr (pseudo-term-fix term)))))

  (defrule ttmrg-correct-sk-of-make-ttmrg-trivial
    (ttmrg-correct-sk (make-ttmrg-trivial term))
    :in-theory (enable ttmrg-correct-sk))

  ; The proof of (ttmrg-correct-p (make-ttmrg-trivial term)) relies on
  ;   knowing that (make-ttmrg-trivial term) satisfies ttmrg-syntax-p
  ;   and ttmrg-correct-sk.  Those were proven above, so we're all happy.
  ;   Not quite.  The proof of ttmrg-correct-p-of make-ttmrg-trivial
  ;   and the one for args need to have make-ttmrg-trivial and
  ;   make-ttmrg-args-trivial enabled to show they satisify the other
  ;   conditions of the correct-p functions.  If the rewriter expands
  ;   the make-ttmrg-trivial and make-ttmrg-args-trivial terms, then
  ;   it won't match the theorems about syntax-p and correct-sk.
  ;     My solution is to include the claims about syntax-p and correct-sk
  ;   as hypotheses -- then they get rewritten just like the terms in the
  ;   main goal.  I call these "lemmas".  Then, I prove the main theorems
  ;   by stating the same claim without these extra hypotheses and with
  ;   make-ttmrg-trivial and make-ttmrg-args-trivial disabled.  The
  ;   theorems about syntax-p and correct-sk match and the proofs
  ;   succeed.
  ;     The astute reader will note that the claim for
  ;   ttmrg-args-correct-p-of-make-ttmrg-args-trivial is identical to
  ;   the claim for ttmrg-args-correct-p-of-make-ttmrg-args-trivial-lemma.
  ;   The "difference" is that the -lemma version is the in the local
  ;   encapsulation to hide all events that I don't want expose to the
  ;   outside world.  The main version is the one that gets exported.
  (defthm-make-ttmrg-trivial-flag
    (defthm ttmrg-correct-p-of-make-ttmrg-trivial-lemma
      (implies (and (ttmrg-syntax-p (make-ttmrg-trivial term))
		    (ttmrg-correct-sk (make-ttmrg-trivial term)))
	       (ttmrg-correct-p (make-ttmrg-trivial term)))
      :flag term)

    (defthm ttmrg-args-correct-p-of-make-ttmrg-args-trivial-lemma
      (ttmrg-args-correct-p (make-ttmrg-args-trivial args))
      :flag args)

    :hints(("Goal"
      :in-theory (e/d (make-ttmrg-trivial make-ttmrg-args-trivial
		       ttmrg-correct-p ttmrg-args-correct-p)
		      (ttmrg-syntax-p-of-make-ttmrg-trivial
		       ttmrg-correct-sk-of-make-ttmrg-trivial)))))))

(defrule ttmrg-correct-p-of-make-ttmrg-trivial
  (ttmrg-correct-p (make-ttmrg-trivial term)))

(defrule ttmrg-args-correct-p-of-make-ttmrg-args-trivial
  (ttmrg-args-correct-p (make-ttmrg-args-trivial args)))


(encapsulate ()
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

    :hints(("Goal" :in-theory (enable pseudo-term-syntax-p pseudo-term-list-syntax-p)))))
