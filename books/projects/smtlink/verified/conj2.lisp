;; Copyright (C) 2015, University of British Columbia)
;; Originally written by Yan Peng (December 30th 2019)
;; Edited by Mark Greenstreet
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "conj")

(set-induction-depth-limit 1)

(local (in-theory (disable  ; mark is impatient
  SYMBOL-LISTP TRUE-LIST-LISTP MEMBER-EQUAL DEFAULT-CAR DEFAULT-CDR
  PSEUDO-TERM-LISTP-OF-CDR-OF-PSEUDO-TERMP
  ACL2::TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP
  PSEUDO-TERM-LISTP-OF-SYMBOL-LISTP
  ACL2::PSEUDO-TERMP-WHEN-MEMBER-EQUAL-OF-PSEUDO-TERM-LISTP
  CONSP-OF-CDR-OF-PSEUDO-LAMBDAP
  ACL2::SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP
  ACL2::SYMBOL-LISTP-WHEN-NOT-CONSP
  ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP
  ACL2::PSEUDO-LAMBDAP-OF-CAR-WHEN-PSEUDO-TERMP
  ACL2::PSEUDO-TERMP-CAR
  ACL2::PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP
  ACL2::TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP
  ACL2::SUBSETP-CAR-MEMBER
  ACL2::PSEUDO-LAMBDAP-WHEN-MEMBER-EQUAL-OF-PSEUDO-LAMBDA-LISTP
  ACL2::PSEUDO-LAMBDAP-OF-CAR-WHEN-PSEUDO-LAMBDA-LISTP
  ACL2::PSEUDO-TERMP-LIST-CDR
  CAR-IS-IF-WHEN-CONJ-CONSP
  CONSP-OF-CDDR-OF-PSEUDO-LAMBDAP
  ACL2::SUBSETP-IMPLIES-SUBSETP-CDR)))

(define conj-merge ((c1 conj-p) (c2 conj-p))
  :returns (c conj-p)
  (b* ((c1 (conj-fix c1))
       (c2 (conj-fix c2))
       ((if (equal c1 ''t)) c2)
       ((if (equal c2 ''t)) c1))
    (conj-cons c1 c2))
  ///
  (more-returns
    (c :name ev-smtcp-of-conj-merge
       (implies (and (conj-p c1) (conj-p c2) (alistp env))
		(iff (ev-smtcp c env)
		     (and (ev-smtcp c1 env)
			  (ev-smtcp c2 env)))))))


; conj-apropos-term-p and conj-apropos-args-p
;   Check if all free variables in target (or args) are in subterms
;   that match pattern.
;   BOZO(?): conj-apropos-term-p has worst-case O(n^2) runtime due to the
;   (equal target pattern) test at each call.  I won't worry about this
;   for now.  I'm considering hons'ing terms in make-ttmrg-trivial, in
;   which case we could replace equal with hons-equal to get Theta(n) time.

(defines conj-apropos-p
  (define conj-apropos-term-p ((pattern pseudo-termp) (target pseudo-termp))
    :returns (ok booleanp)
    :flag term
    (b* (((if (equal target pattern)) t)
	 ((if (equal target ''nil)) t)
	 ((if (equal target ''t)) t)
	 ((if (atom target)) nil)
	 ((if (equal (car target) 'quote)) t)
	 ((if (consp (car target))) nil)) ; lambda expressions should have been flattened already
      (conj-apropos-args-p pattern (cdr target))))

  (define conj-apropos-args-p ((pattern pseudo-termp) (args pseudo-term-listp))
    :returns (ok booleanp)
    :flag args
    (b* (((unless (consp args)) t)
	 ((cons hd tl) args)
	 ((unless (conj-apropos-term-p pattern hd)) nil))
      (conj-apropos-args-p pattern tl))))


; (conj-apropos ((pattern pseudo-termp) (tree conj-p)))
;   Return a conj-p "list" that has all conjuncts of tree that are
;   "relevant" for pattern.  A conjunct is "relevant" if all free variables
;   in tree appear in subterms that are copies of pattern.

(define conj-apropos ((pattern pseudo-termp) (tree pseudo-termp))
  :returns (a conj-p)
  (if (and (consp tree) (equal (car tree) 'if)
	   (consp (cdddr tree)) (not (cddddr tree))
	   (equal (cadddr tree) ''nil))
    (conj-merge
      (conj-apropos pattern (cadr tree))
      (conj-apropos pattern (caddr tree)))
    (if (conj-apropos-term-p pattern tree)
      (conj-cons (pseudo-term-fix tree) ''t)
      ''t)))
