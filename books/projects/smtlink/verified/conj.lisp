(in-package "SMT")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "xdoc/top" :dir :system)

(include-book "evaluator")

(set-induction-depth-limit 1)

(local (in-theory (disable  ;; the "worst" offenders for useless runes
  pseudo-termp symbol-listp rational-listp integer-listp true-list-listp member-equal
  ACL2::PSEUDO-LAMBDAP-OF-CAR-WHEN-PSEUDO-TERMP
  CONSP-OF-CDR-OF-PSEUDO-LAMBDAP
  PSEUDO-TERM-LISTP-OF-CDR-OF-PSEUDO-TERMP
  ACL2::SUBSETP-IMPLIES-SUBSETP-CDR
  ACL2::SUBSETP-WHEN-ATOM-RIGHT
  ACL2::PSEUDO-LAMBDAP-OF-CAR-WHEN-PSEUDO-LAMBDA-LISTP
  CONSP-OF-CDDR-OF-PSEUDO-LAMBDAP
  ACL2::PSEUDO-LAMBDAP-WHEN-MEMBER-EQUAL-OF-PSEUDO-LAMBDA-LISTP
  ACL2::PSEUDO-LAMBDA-LISTP-OF-CDR-WHEN-PSEUDO-LAMBDA-LISTP
  ACL2::SUBSETP-WHEN-ATOM-LEFT
  ACL2::PSEUDO-LAMBDA-LISTP-WHEN-NOT-CONSP)))

(define conj-p ((x acl2::any-p))
  :short "recognizer for conjunction-objects."
  :long "<p>Usage:</p>
@({
     (conj-p term)
})

<p>is satisifed if @('term') is <tt>''t</tt> or if it is a @(see pseudo-termp) of
the form <tt>'(if ,hd ,tl 'nil)</tt> where @('hd') is a @(see pseudo-termp)
and @('tl') is a @('conj-p').</p>

<p>@('conj-p') objects form list-like structures corresponding to conses.
These lists are <tt>''t</tt> terminated.
In particular, if we have some pseudo-term, @('x'), we can express judgements
(e.g. type-inferences) about the subterms of @('x') by constructing an
object whose @(see conj-p) structure mirrors the the @(see consp) structure
of @('x').
</p>"
  :returns (ok booleanp)
  (and (pseudo-termp x)
       (case-match x (('if & tl ''nil) (conj-p tl))
		     (''t t)))
  ///
  (more-returns
    (ok :name pseudo-termp-when-conj-p
	(implies ok (pseudo-termp x))
	:rule-classes (:rewrite :forward-chaining))
    (ok :name booleanp-of-ev-smtcp-when-conj-p
     (implies (and ok (alistp env))
	      (booleanp (ev-smtcp x env)))
     :hints(("Goal" :in-theory (enable conj-p))))))

(define conj-fix ((x conj-p))
  :short "Coerce to a @(see conj-p)."
  :returns (xx conj-p)
  (mbe :logic (if (conj-p x) x ''t)
       :exec x)
  ///
  (more-returns
    (xx :name conj-fix-when-conj-p
	(implies (conj-p x) (equal xx x)))))

(define conj-consp ((x conj-p))
  :short "recognizer for @(see conj-p) values that are &ldquo;cons-like&rdquo;, i.e. the conjunction of two terms."
  :returns (ok booleanp)
  (if (mbt (conj-p x))
    (not (equal x ''t))
    nil)
  ///
  (more-returns
    (ok :name conj-p-when-conj-consp
	(implies ok (conj-p x))
	:rule-classes (:rewrite :forward-chaining))
    (ok :name consp-when-conj-consp
	(implies ok (consp (cdddr x)))
	:hints(("Goal" :expand ((conj-p x))))
	:rule-classes (:rewrite :forward-chaining))
    (ok :name car-is-if-when-conj-consp
	(implies ok (equal (car x) 'if))
	:hints(("Goal" :expand ((conj-p x))))
	:rule-classes (:rewrite :forward-chaining))))

(local (in-theory (enable conj-p conj-consp)))

(define conj-atom ((x acl2::any-p)) ; I want to know that if x is a conj-p
  :returns (ok booleanp)  ; not a conj-consp, then (equal x ''t).  But, I
  (equal x ''t)           ; can't have a rewrite rule with a conclusion of (equal x ''t);
  ///                     ; so, I'll introduce conj-atom instead.
  (more-returns
    (ok :name conj-atom-when-conj-p-and-not-conj-consp
	(implies (and (conj-p x) (not (conj-consp x)))
		 ok))))

(define conj-car ((x conj-p))
  :short "extract the first conjunct of a @(see conj-p) object"
  :returns (hd pseudo-termp)
  (if (conj-consp x) (cadr x) ''t)
  ///
  (more-returns
    (hd :name count-of-conj-car
	(implies (conj-consp x)
		 (< (acl2-count hd) (acl2-count x))))))

(define conj-cdr ((x conj-p))
  :short "extract the second conjunct of a @(see conj-p) object -- this second conjunct must be a @(see conj-p) object itself"
  :returns (tl conj-p)
  (if (conj-consp x) (caddr x) ''t)
  ///
  (more-returns
    (tl :name count-of-conj-cdr
	(implies (conj-consp x)
		 (< (acl2-count tl) (acl2-count x))))))

(define conj-len ((x conj-p)) 
  :short "The analog of @(see len) for @(see conj-p) objects"
  :long "The analog of @(see len) for @(see conj-p) objects.
         This function might not actually be called anywhere,
	 but I refer to it to describe other functions."
  :returns (n (and (integerp n) (<= 0 n)))
  (if (conj-consp x) (1+ (conj-len (conj-cdr x))) 0))

(define conj-cons ((hd pseudo-termp) (tl conj-p))
  :short "constructor for @(see conj-p) objects"
  :returns (conj conj-consp)
  `(if ,(pseudo-term-fix hd) ,(conj-fix tl) 'nil)
  ///
  (more-returns
    (conj :name conj-car-cons
	  (implies (pseudo-termp hd)
		   (equal (conj-car conj) hd))
	  :hints(("Goal" :in-theory (enable conj-car))))
    (conj :name conj-cdr-cons
	  (equal (conj-cdr conj) (conj-fix tl))
	  :hints(("Goal" :in-theory (enable conj-cdr)))))

  (acl2::defrule conj-cons-car-cdr
    (equal (conj-cons (conj-car x) (conj-cdr x))
	   (if (conj-consp x) x
	     (conj-cons ''t ''t)))
    :in-theory (e/d (conj-cons conj-car conj-cdr)
		    (pseudo-termp-of-conj-car conj-p-of-conj-cdr))
    :use((:instance conj-p-of-conj-cdr)
	 (:instance pseudo-termp-of-conj-car)))

  (defrule ev-smtcp-of-conj-cons
    (implies (alistp env)
	     (equal (ev-smtcp (conj-cons hd tl) env)
		    (if (ev-smtcp (pseudo-term-fix hd) env)
		      (ev-smtcp (conj-fix tl) env) nil))))

  (defrule ev-smtcp-of-conj-car
    (implies (and (conj-p x)(alistp env) (ev-smtcp x env))
	     (ev-smtcp (conj-car x) env))
    :in-theory (enable conj-car conj-consp conj-p))

  (defrule ev-smtcp-of-conj-cdr
    (implies (and (conj-p x)(alistp env) (ev-smtcp x env))
	     (ev-smtcp (conj-cdr x) env))
    :in-theory (enable conj-cdr conj-consp conj-p))

  (defrule simple-term-vars-of-conj-cons
    (implies (and (pseudo-termp hd) (conj-p tl))
	     (acl2::set-equiv (acl2::simple-term-vars (conj-cons hd tl))
			      (union-equal (acl2::simple-term-vars hd)
					   (acl2::simple-term-vars tl))))
    :in-theory (enable acl2::simple-term-vars acl2::simple-term-vars-lst)))

(local (in-theory (disable conj-p conj-consp)))

;(define conj-member ((x pseudo-termp) (conj conj-p))
;  :returns (y conj-p)
;  (b* (((unless (conj-consp conj)) ''t)
;       ((conj-cons hd tl) conj)
;       ((if (equal x hd)) conj))
;    (conj-member x tl)))
;
;
;(define conj-merge ((c1 conj-p) (c2 conj-p))
;  :returns (c conj-p)
;  (b* ((c1 (conj-fix c1))
;       (c2 (conj-fix c2))
;       ((if (equal c1 ''t)) c2)
;       ((if (equal c2 ''t)) c1))
;    (conj-cons c1 c2))
;  ///
;  (more-returns
;    (c :name ev-smtcp-of-conj-merge
;       (implies (and (conj-p c1) (conj-p c2) (alistp env))
;		(iff (ev-smtcp c env)
;		     (and (ev-smtcp c1 env)
;			  (ev-smtcp c2 env)))))))
(define conj-conj-p ((x acl2::any-p))
  :returns (ok booleanp)
  (and (conj-p x)
       (if (conj-consp x)
	 (and (conj-p (conj-car x))
	      (conj-conj-p (conj-cdr x)))
	 t))
  ///
  (more-returns
    (ok :name conj-p-when-conj-conj-p
      (implies ok (conj-p x))
      :rule-classes (:rewrite :forward-chaining))
    (ok :name conj-conj-p-of-conj-cdr-when-conj-conj-p
      (implies ok (conj-conj-p (conj-cdr x)))
      :hints(("Goal" :in-theory (enable conj-consp))))
    (ok :name conj-p-of-conj-car-when-conj-conj-p
      (implies ok (conj-p (conj-car x)))
      :hints(("Goal" :in-theory (enable conj-consp )))))

  (defrule conj-conj-p-of-conj-cons
    (implies (and (conj-p hd) (conj-conj-p tl))
	     (conj-conj-p (conj-cons hd tl))))

  (define conj-conj-fix ((x conj-conj-p))
    :returns (y conj-conj-p)
    :verify-guards nil
    (mbe :logic (if (conj-consp x)
		  (conj-cons (conj-fix (conj-car x))
			     (conj-conj-fix (conj-cdr x)))
		  ''t)
	 :exec x)
    ///
    (local (defrule lemma-1
      (implies (conj-p x)
	       (or (conj-consp x) (equal x ''t)))
      :in-theory(enable conj-p conj-consp)
      :rule-classes (:forward-chaining)))
    (defrule conj-conj-fix-when-conj-conj-p
      (implies (conj-conj-p x)
	       (equal (conj-conj-fix x) x)))
    (verify-guards conj-conj-fix)))

(define pseudo-conj-p ((x pseudo-termp))
  :returns (ok booleanp)
  (and (mbt (pseudo-termp x))
       (case-match x (''t t)
		     (('if & & ''nil) t)
	             (& nil)))
  ///
  (more-returns
    (ok :name pseudo-termp-when-pseudo-conj-p
	(implies ok (pseudo-termp x)))
    (ok :name pseudo-termp-of-cadr-when-pseudo-conj-p
	(implies ok (pseudo-termp (cadr x))))
    (ok :name pseudo-termp-of-caddr-when-pseudo-conj-p
	(implies ok (pseudo-termp (caddr x))))
    (ok :name pseudo-conj-p-when-conj-p
	(implies (conj-p x) ok)
	:hints(("Goal" :expand ((conj-p x)))))))


(define term-to-conj ((x pseudo-termp))
  :short "convert an arbitrary @(see pseudo-termp) to a @(see conj-p)"
  :returns (xx conj-p)
  :hints(("Goal" :in-theory (enable pseudo-conj-p)))
  :verify-guards nil
  (b* (((unless (pseudo-conj-p x)) (conj-cons x ''t))
       ((if (equal x ''t)) x)
       ((list & hd tl &) x))
     (conj-cons hd (term-to-conj tl)))
  ///
  (verify-guards term-to-conj
    :hints(("Goal" :expand ((pseudo-conj-p x)))))
  (more-returns
    (xx :name term-to-conj-when-conj-p
      (implies (conj-p x) (equal xx x))
      :hints(("Goal" :in-theory (enable term-to-conj conj-p conj-cons))))))

(acl2::defrule correctness-of-term-to-conj
  (implies (and (pseudo-termp x) (alistp a))
	   (iff (ev-smtcp (term-to-conj x) a)
		(ev-smtcp x a)))
  :in-theory (enable term-to-conj pseudo-conj-p conj-cons)
  :induct (term-to-conj x))


(deffixtype conj
  :pred conj-p
  :fix conj-fix
  :equiv conj-equiv
  :define t)

(deffixtype conj-conj
  :pred conj-conj-p
  :fix conj-conj-fix
  :equiv conj-conj-equiv
  :define t)


(define conj-list-fn ((args pseudo-term-listp))
  (if (consp args)
    `(conj-cons ,(car args) ,(conj-list-fn (cdr args)))
    '''t))

(defmacro conj-list (&rest args)
  (conj-list-fn args))

(define conj-list*-fn ((args pseudo-term-listp))
  :guard (and (consp args) (conj-p (car (last args))))
  :returns (x conj-p)
  (if (consp (cdr args))
    (conj-cons (car args)
	       (conj-list*-fn (cdr args)))
    (conj-fix (car args))))

(defmacro conj-list* (&rest args)
  (conj-list*-fn args))


(acl2::def-patbind-macro conj-cons
  (conj-car conj-cdr)
  :short "@(see b*) binder for @(see conj-p) decomposition."
  :long "<p>Usage:</p>
@({
     (b* (((conj-cons a b) c-lst))
       form)
})
<p>is equivalent to</p>

@({
    (b* ((a (conj-car c-lst))
         (b (conj-cdr c-lst)))
      form)
})
<p>Examples:</p>
@({
  (equal (b* (((conj-cons hd tl) (conj-cons 'x ''t)))
            (list hd tl))
         '(x 't))
  (equal (b* (((conj-cons hd tl) '(if x 't 'nil)))
            (list hd tl))
         '(x 't))
})"
)


(acl2::def-b*-binder conj-list
  :short "@(see b*) binder for conj-list decomposition, using @(see conj-car)/@(see conj-cdr)."
  :long "<p>Usage:</p>
@({
     (b* (((conj-list a b c) c-lst))
       form)
})

<p>is equivalent to</p>

@({
    (b* ((a (conj-car lst))
         (tmp1 (conj-cdr lst))
         (b (conj-car tmp1))
         (tmp2 (conj-cdr tmp1))
         (c (conj-car tmp2)))
      form)
})

<p>Each of the arguments to the @('conj-list') binder may be a recursive binder, and
@('conj-list') may be nested inside other bindings. (I hope, mrg)</p>
<p>Example:</p>
@({
     (equal (b* (((conj-list a b c) (conj-list 'x 'y 'z)))
               (list a b c))
	    '('x 'y 'z))
})"
  :decls
  ((declare (xargs :guard (acl2::destructure-guard conj-list acl2::args acl2::forms nil))))
  :body
  (if (atom acl2::args)
      acl2::rest-expr
    `(patbind-conj-cons (,(car acl2::args) (conj-list . ,(cdr acl2::args))) ,acl2::forms ,acl2::rest-expr)))

(acl2::def-b*-binder conj-list*
  :short "@(see b*) binder for @('conj-list*') decomposition using @(see car)/@(see cdr)."
  :long "<p>Usage:</p>
@({
    (b* (((conj-list* a b c) lst)) form)
})

<p>is equivalent to</p>

@({
    (b* ((a (conj-car lst))
         (tmp1 (conj-cdr lst))
         (b (conj-car tmp1))
         (c (conj-cdr tmp1)))
      form)
})

<p>Each of the arguments to the @('list*') binder may be a recursive binder,
and @('list*') may be nested inside other bindings. (I hope, mrg)</p>
<p>Example:</p>
@({
     (equal (b* ((lst (conj-list 'u 'v 'w 'x 'y 'z))
		 ((conj-list* a b c tl) lst))
               (list a b c tl))
	    '('u 'v 'w
		 (if 'x (if 'y (if 'z 't 'nil) 'nil) 'nil)))
})"
  :decls
  ((declare (xargs :guard (and (consp acl2::args)
                               (acl2::destructure-guard conj-list* acl2::args acl2::forms nil)))))
  :body
  (if (atom (cdr acl2::args))
      `(acl2::patbind ,(car acl2::args) ,acl2::forms ,acl2::rest-expr)
    `(patbind-conj-cons (,(car acl2::args) (conj-list* . ,(cdr acl2::args)))
			,acl2::forms ,acl2::rest-expr)))

