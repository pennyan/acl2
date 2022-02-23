;; define a macro that introduces a introduces the various functions and
;; types needed for defining an alist that can be translated into a z3 array.

(in-package "SMT")
(include-book "std/strings/top" :dir :system)
(include-book "std/util/top" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "alist")

; perhaps I should use acl2::deflist or fty::deflist to define
; stringable-list-p and stringable-list-list-p, but I don't want to choose
; which package to use for this proof-of-concept example.

; stringable-list-p -- a list of things that are "acceptable" for turning
;   into strings that will be interned into symbols by make-symbol.
(define stringable-list-p (x)
  :returns (ok booleanp)
  (if x
      (and (consp x)
	         (or (stringp (car x))
	             (symbolp (car x))
	             (character-listp (car x)))
	         (stringable-list-p (cdr x)))
    t))

; stringable-list-list-p -- a list of stringable-list-p's
(define stringable-list-list-p (x)
  :returns (ok booleanp)
  (if x
      (and (consp x)
	         (stringable-list-p (car x))
	         (stringable-list-list-p (cdr x)))
    t))


; stringify-list -- convert a list of stringable-p values into a list of strings
(define stringify-list ((x stringable-list-p))
  :returns (s string-listp)
  :verify-guards nil
  (b* (((unless (consp x)) nil)
       ((cons hd0 tl) x)
       (hd (acl2::implode
	          (str::upcase-charlist
	           (if (atom hd0)
		             (explode-atom hd0 10)
		           (str::character-list-fix hd0))))))
    (cons hd (stringify-list tl)))
  ///
  (verify-guards stringify-list
    :hints(("Goal" :in-theory (enable stringable-list-p)))))


; mk-symbol -- I first wrote this as make-symbol, but
;   ACL2 Error in ( DEFUN MAKE-SYMBOL ...):  Symbols in the main Lisp package,
;   such as MAKE-SYMBOL, may not be defined or constrained.
; OTOH, :doc, :pe, and :pf have nothing for make-symbol.
(define mk-symbol ((x stringable-list-p) (sym symbolp))
  :returns (s symbolp)
  (intern-in-package-of-symbol
   (str::join (stringify-list x) "-") sym))

(define mk-symbol-list ((x stringable-list-list-p) (sym symbolp))
  :returns (s symbol-listp)
  :guard-hints(("Goal" :in-theory (enable stringable-list-list-p)))
  (if (consp x)
      (cons (mk-symbol (car x) sym) (mk-symbol-list (cdr x) sym))
    nil))

(define defalist-smt-fn
  ((key-val-alist-p symbolp)
   (key-p symbolp) (key-fix symbolp)
   (val-p symbolp) (val-fix symbolp))
  :guard (and key-val-alist-p key-p val-p)
  (declare (xargs :mode :program))
  (b* ((x (explode-atom key-val-alist-p 10))
       (lenx (len x))
       (key-val (cond ((and (> lenx 7)
                            (equal (nthcdr (- lenx 7) x)
			                             (acl2::explode "-ALISTP")))
		                   (take (- lenx 7) x))
		                  ((and (> lenx 8)
			                      (equal (nthcdr (- lenx 8) x)
				                           (acl2::explode "-ALIST-P")))
		                   (take (- lenx 8) x))
		                  (t x)))
       (array-name (mk-symbol `(,key-val "array") key-val-alist-p))
       (key-val-consp (mk-symbol `(,key-val "consp") key-val-alist-p))
       (key-val-cons-fix (mk-symbol `(,key-val "cons-fix") key-val-alist-p))
       (key-val-alist-fix (mk-symbol `(,key-val "alist-fix") key-val-alist-p))
       ((list maybe-key-val-consp
              maybe-key-val-cons-fix
              maybe-key-val-cons->cons
              maybe-key-val-cons->car
              maybe-key-val-cons->cdr
              maybe-key-val-cons->nil)
        (mk-symbol-list (list
                         `(maybe ,key-val-consp)
                         `(maybe ,key-val-cons-fix)
                         `(maybe ,key-val "cons->cons")
                         `(maybe ,key-val "cons->car")
                         `(maybe ,key-val "cons->cdr")
                         `(maybe ,key-val "cons->nil"))
                         key-val-alist-p))
       ((list key-val-array-p
	            key-val-array-init
	            key-val-array-store
	            key-val-array-from-al
	            key-val-array-select
	            key-val-array-equiv
              key-val-array-equiv-consp
              key-val-array-equal
              key-val-array-equal-witness)
        (mk-symbol-list (list
	                       `(,array-name p)
	                       `(,array-name init)
	                       `(,array-name store)
	                       `(,array-name from-al)
	                       `(,array-name select)
	                       `(,array-name equiv)
                         `(,array-name equiv-consp)
                         `(,array-name equal)
                         `(,array-name equal-witness))
	                      key-val-alist-p))
       ((list key-p-equals-kp
              key-fix-equals-k-fix
	            val-p-equals-vp
              val-fix-equals-v-fix
              ;; key-p-of-key-fix
              ;; replace-of-key-fix
              ;; val-p-of-val-fix
              ;; replace-of-val-fix
	            key-val-consp-equals-kvp
              key-val-cons-fix-equals-kv-fix
	            booleanp-of-key-val-consp
              key-val-consp-of-key-val-cons-fix
              replace-of-key-val-cons-fix
              key-p-of-car-of-key-val-consp
              val-p-of-cdr-of-key-val-consp
	            maybe-key-val-consp-equals-mkvp
              maybe-key-val-cons-fix-equals-mkv-fix
              maybe-key-val-cons->cons-equals-mkv->cons
              maybe-key-val-cons->car-equals-mkv->car
              maybe-key-val-cons->cdr-equals-mkv->cdr
              car-of-cons-of-maybe-key-val-consp
              cdr-of-cons-of-maybe-key-val-consp
              cons-of-car-and-cdr-of-maybe-key-val-consp
              maybe-key-val-cons->nil-equals-mkv->nil
	            booleanp-of-maybe-key-val-consp
              booleanp-of-equal-of-maybe-key-val-consp
              val-p-of-cdr-of-maybe-key-val-consp
              replace-of-maybe-key-val-cons->nil
              maybe-key-val-consp-of-maybe-key-val-cons-fix
              maybe-key-val-consp-of-maybe-key-val-cons->cons
              key-p-of-maybe-key-val-cons->car
              val-p-of-maybe-key-val-cons->cdr
              replace-of-cdr-of-key-val-consp
              maybe-key-val-consp-of-maybe-key-val-cons->nil
              replace-of-maybe-key-val-cons-fix
              maybe-key-val-consp-canbe-key-val-consp
	            key-val-alist-p-equals-kvap
              key-val-alist-fix-equals-kva-fix
              booleanp-of-key-val-alist-p
              key-val-alist-p-of-key-val-alist-fix
              replace-of-key-val-alist-fix
              key-val-alist-p-of-acons
              maybe-key-val-consp-of-assoc-equal-of-key-val-alist-p
	            booleanp-of-key-val-array-p
	            key-val-array-p-of-key-val-array-init
	            key-val-array-p-of-key-val-array-store
	            key-val-array-p-of-key-val-array-from-al
	            maybe-key-val-consp-of-key-val-array-select
	            booleanp-of-key-val-array-equiv
	            key-val-array-select-of-key-val-array-init
	            key-val-array-select-of-key-val-array-store
              booleanp-of-key-val-array-equal
              key-val-array-equal-implies-selects-equal
              selects-of-witness-equal-implies-key-val-array-equal
	            key-val-array-translation-of-nil
	            key-val-array-translation-of-alist
	            key-val-array-translation-of-acons
	            key-val-array-translation-of-assoc-equal)
        (mk-symbol-list (list
                         `(,key-p equals kp)
                         `(,key-fix equals k-fix)
	                       `(,val-p equals vp)
                         `(,val-fix equals v-fix)
                         ;; `(,key-p of ,key-fix)
                         ;; `(replace of ,key-fix)
                         ;; `(,val-p of ,val-fix)
                         ;; `(replace of ,val-fix)
	                       `(,key-val-consp equals kvp)
                         `(,key-val-cons-fix equals kv-fix)
	                       `(booleanp of ,key-val-consp)
                         `(,key-val-consp of ,key-val-cons-fix)
                         `(replace of ,key-val-cons-fix)
                         `(,key-p of car of ,key-val-consp)
                         `(,val-p of cdr of ,key-val-consp)
	                       `(,maybe-key-val-consp equals mkvp)
                         `(,maybe-key-val-cons-fix equals mkv-fix)
                         `(,maybe-key-val-cons->cons equals mkv->cons)
                         `(,maybe-key-val-cons->car equals mkv->car)
                         `(,maybe-key-val-cons->cdr equals mkv->cdr)
                         `(car of cons of ,maybe-key-val-consp)
                         `(cdr of cons of ,maybe-key-val-consp)
                         `(cons of car and cdr of ,maybe-key-val-consp)
                         `(,maybe-key-val-cons->nil equals mkv->nil)
	                       `(booleanp of ,maybe-key-val-consp)
                         `(booleanp of equal of ,maybe-key-val-consp)
                         `(,val-p of cdr of ,maybe-key-val-consp)
                         `(replace of ,maybe-key-val-cons->nil)
                         `(,maybe-key-val-consp of ,maybe-key-val-cons-fix)
                         `(,maybe-key-val-consp of ,maybe-key-val-cons->cons)
                         `(,key-p of ,maybe-key-val-cons->car)
                         `(,val-p of ,maybe-key-val-cons->cdr)
                         `(replace of cdr of ,key-val-consp)
                         `(,maybe-key-val-consp of ,maybe-key-val-cons->nil)
                         `(replace of ,maybe-key-val-cons-fix)
                         `(,maybe-key-val-consp canbe ,key-val-consp)
	                       `(,key-val-alist-p equals kvap)
                         `(,key-val-alist-fix equals kva-fix)
                         `(booleanp of ,key-val-alist-p)
                         `(,key-val-alist-p of ,key-val-alist-fix)
                         `(replace of ,key-val-alist-fix)
                         `(,key-val-alist-p of acons)
                         `(,maybe-key-val-consp of assoc-equal of ,key-val-alist-p)
	                       `(booleanp of ,key-val-array-p)
	                       `(,key-val-array-p of ,key-val-array-init)
	                       `(,key-val-array-p of ,key-val-array-store)
	                       `(,key-val-array-p of ,key-val-array-from-al)
	                       `(,maybe-key-val-consp of ,key-val-array-select)
	                       `(booleanp of ,key-val-array-equiv)
	                       `(,key-val-array-select of ,key-val-array-init)
	                       `(,key-val-array-select of ,key-val-array-store)
                         `(booleanp of ,key-val-array-equal)
                         `(,key-val-array-equal implies selects equal)
                         `(selects of witness equal implies ,key-val-array-equal)
	                       `(,key-val array translation of nil)
	                       `(,key-val array translation of alist)
	                       `(,key-val array translation of acons)
	                       `(,key-val array translation of assoc-equal))
	                      key-val-alist-p)))
    `(progn
       (local (encapsulate nil
	              (define kp (x)
	                :returns (ok booleanp)
	                (,key-p x))

                (define k-fix (x)
                  :returns (r kp :hints (("Goal" :in-theory (enable kp))))
                  (,key-fix x)
                  ///
                  (more-returns
                   (r :name replace-of-k-fix
                      (implies (kp x) (equal r x))
                      :hints (("Goal" :in-theory (enable kp))))))

	              (define vp (x)
	                :returns (ok booleanp)
	                (,val-p x))

                (define v-fix (x)
                  :returns (r vp :hints (("Goal" :in-theory (enable vp))))
                  (,val-fix x)
                  ///
                  (more-returns
                   (r :name replace-of-v-fix
                      (implies (vp x) (equal r x))
                      :hints (("Goal" :in-theory (enable vp))))))

	              (define kvp (x)
	                (and (consp x)
	                     (kp (car x))
	                     (vp (cdr x))))

                (define kv-fix (x)
                  (if (kvp x) x
                    (cons (k-fix nil) (v-fix nil))))

	              (define mkvp (x) (implies x (kvp x)))

                (define mkv-fix (x)
                  (if (mkvp x) x nil))

                (define mkv->cons (x y)
                  (cons (k-fix x) (v-fix y)))

                (define mkv->car (x)
                  :verify-guards nil
                  (k-fix (car (mkv-fix x))))

                (define mkv->cdr (x)
                  :verify-guards nil
                  (v-fix (cdr (mkv-fix x))))

                (define mkv->nil () nil)

	              (define kvap (x)
	                (if x
	                    (and (consp x)
		                       (kvp (car x))
		                       (kvap (cdr x)))
	                  t))

                (define kva-fix (x)
                  (if (kvap x) x nil))
	              
	              (acl2::define-sk ar-kv-p (ar)
	                :returns (ok)
	                (forall (k)
	                        (and (ua-p ar)
		                           (mkvp (ua-select ar k)))))

	              (define ar-kv-init ()
	                (ua-init nil)
	                ///
	                (in-theory (disable (:e ar-kv-init))))

	              (define ar-kv-store ((ar ar-kv-p) (k kp) (kv mkvp))
	                :verify-guards nil
	                (if (and (kp k) (mkvp kv) (ar-kv-p ar))
	                    (ua-store ar k kv)
	                  (ar-kv-init)))

	              (define ar-kv-from-al ((al kvap))
	                :verify-guards nil
	                (if (and (consp al) (kvp (car al)))
	                    (ar-kv-store (ar-kv-from-al (cdr al)) (caar al) (car al))
	                  (ar-kv-init)))

	              (define ar-kv-select ((ar ar-kv-p) (k kp))
	                (if (ar-kv-p ar)
	                    (ua-select ar k)
	                  nil))

	              (acl2::define-sk ar-kv-equiv (al ar)
	                :returns (ok)
	                :verify-guards nil
	                (forall (k)
		                      (and (kvap al)
		                           (ar-kv-p ar)
		                           (equal (assoc-equal k al) (ar-kv-select ar k)))))

                (define ar-kv-equiv-consp (x)
                  :returns (ok)
                  :verify-guards nil
                  (and (consp x) (ar-kv-equiv (car x) (cdr x))))

                (define ar-kv-equal ((a1 ar-kv-p) (a2 ar-kv-p))
                  (if (and (ar-kv-p a1) (ar-kv-p a2))
                      (ua-equal a1 a2)
                    nil))

                (define ar-kv-equal-witness ((a1 ar-kv-p) (a2 ar-kv-p))
                  (if (and (ar-kv-p a1) (ar-kv-p a2))
                      (ua-equal-witness a1 a2)
                    nil))

	              ;; Rather than writing the long functional instantiation hint for each of the
	              ;; theorems below, I'll wrap it up with a macro.
	              (defmacro fi-thm (name claim ar-thm
                                       &key (rule-classes ':rewrite) (theory 'nil))
	                `(defthm ,name ,claim :hints(("Goal"
	                                              :in-theory ,theory
	                                              :use((:functional-instance
                                                      ,ar-thm
					                                            ;; instantiate the generic functions
					                                            (ar-key-p kp)
                                                      (ar-key-fix k-fix)
				                                              (ar-val-p vp)
                                                      (ar-val-fix v-fix)
					                                            ;; instantiate the other relevant functions
					                                            (ar-key-val-consp kvp)
                                                      (ar-key-val-cons-fix kv-fix)
					                                            (ar-maybe-key-val-consp mkvp)
                                                      (ar-maybe-key-val-cons-fix
                                                       mkv-fix)
                                                      (ar-maybe-key-val-consp->cons
                                                       mkv->cons)
                                                      (ar-maybe-key-val-consp->car
                                                       mkv->car)
                                                      (ar-maybe-key-val-consp->cdr
                                                       mkv->cdr)
                                                      (ar-maybe-key-val-consp->nil
                                                       mkv->nil)
					                                            (ar-key-val-alist-p kvap)
                                                      (ar-key-val-alist-fix kva-fix)
					                                            (ar-p ar-kv-p)
					                                            (ar-p-witness ar-kv-p-witness)
					                                            (ar-init ar-kv-init)
					                                            (ar-store ar-kv-store)
					                                            (ar-from-al ar-kv-from-al)
					                                            (ar-select ar-kv-select)
					                                            (ar-equiv ar-kv-equiv)
                                                      (ar-equiv-consp
                                                       ar-kv-equiv-consp)
					                                            (ar-equiv-witness
                                                       ar-kv-equiv-witness)
                                                      (ar-equal ar-kv-equal)
                                                      (ar-equal-witness
                                                       ar-kv-equal-witness)))))
                     :rule-classes ,rule-classes))


	              ;; return type theorems
	              ;;   In addition to providing returns theorems used by Smtlink, proving
	              ;;   these theorems by functional instantiation has the salubrious effect
	              ;;   of establishing the constraints for funcitional instantation one
	              ;;   function at a time.  This seems to avoid having ACL2 generate a big,
	              ;;   complicated constraint that it then is unable to discharge.

	              (fi-thm booleanp-of-kvp
                 (booleanp (kvp x))
                 booleanp-of-ar-key-val-consp
                 :theory '(kvp booleanp-of-kp booleanp-of-vp
                               kp-of-k-fix vp-of-v-fix
                               replace-of-k-fix replace-of-v-fix))

                (fi-thm kvp-of-kv-fix
                        (kvp (kv-fix x))
                        ar-key-val-consp-of-ar-key-val-cons-fix
                        :theory '(kv-fix))
                
                (fi-thm replace-of-kv-fix
                        (implies (kvp x)
                                 (equal (kv-fix x) x))
                        replace-of-ar-key-val-cons-fix)

                (fi-thm kp-of-car-of-kvp
                        (implies (kvp x)
                                 (kp (car x)))
                        ar-key-p-of-car-of-ar-key-val-consp)

                (fi-thm vp-of-cdr-of-kvp
                        (implies (kvp x)
                                 (vp (cdr x)))
                        ar-val-p-of-cdr-of-ar-key-val-consp)

                (fi-thm booleanp-of-mkvp
                        (booleanp (mkvp x))
                        booleanp-of-ar-maybe-key-val-consp
                        :theory '(mkvp (:t kvp)))

                (fi-thm mkvp-of-mkv-fix
                        (mkvp (mkv-fix x))
                        ar-maybe-key-val-consp-of-ar-maybe-key-val-cons-fix
                        :theory '(mkv-fix))

                (fi-thm mkvp-of-mkv->cons
                        (implies (and (kp x) (vp y)) (mkvp (mkv->cons x y)))
                        ar-maybe-key-val-consp-of-ar-maybe-key-val-consp->cons
                        :theory '(mkv->cons))

                (fi-thm kp-of-mkv->car
                        (implies (and (mkvp x) (not (equal x nil))) (kp (mkv->car x)))
                        ar-key-p-of-ar-maybe-key-val-consp->car
                        :theory '(mkv->car))

                (fi-thm vp-of-mkv->cdr
                        (implies (and (mkvp x) (not (equal x nil))) (vp (mkv->cdr x)))
                        ar-val-p-of-ar-maybe-key-val-consp->cdr
                        :theory '(mkv->cdr))

                (fi-thm replace-of-cdr-of-kvp
                        (implies (kvp x) (equal (cdr x) (mkv->cdr x)))
                        replace-of-cdr-of-ar-key-val-consp)

                (fi-thm car-of-cons-of-mkvp
                        (implies (and (kp x) (vp y))
                                 (equal (mkv->car (mkv->cons x y)) x))
                        car-of-cons-of-maybe-key-val-consp)

                (fi-thm cdr-of-cons-of-mkvp
                        (implies (and (kp x) (vp y))
                                 (equal (mkv->cdr (mkv->cons x y)) y))
                        cdr-of-cons-of-maybe-key-val-consp)

                (fi-thm cons-of-car-and-cdr-of-mkvp
                        (implies (and (mkvp x) x)
                                 (equal (mkv->cons (mkv->car x) (mkv->cdr x)) x))
                        cons-of-car-and-cdr-of-ar-maybe-key-val-consp)

                (fi-thm mkvp-of-mkv->nil
                        (mkvp (mkv->nil))
                        ar-maybe-key-val-consp-of-ar-maybe-key-val-consp->nil
                        :theory '(mkv->nil))

                (fi-thm replace-of-mkv-fix
                        (implies (mkvp x)
                                 (equal (mkv-fix x) x))
                        replace-of-ar-maybe-key-val-cons-fix)

                (fi-thm mkvp-canbe-kvp
                        (implies (and (mkvp x) (not (equal x nil)))
                                 (kvp x))
                        ar-maybe-key-val-consp-canbe-ar-key-val-consp)

                (fi-thm booleanp-of-kvap
                        (booleanp (kvap x))
                        booleanp-of-ar-key-val-alist-p
                        :theory '(kvap))

                (fi-thm kvap-of-kva-fix
                        (kvap (kva-fix x))
                        ar-key-val-alist-p-of-ar-key-val-alist-fix
                        :theory '(kva-fix))

                (fi-thm replace-of-kva-fix
                        (implies (kvap x)
                                 (equal (kva-fix x) x))
                        replace-of-ar-key-val-alist-fix)

                (fi-thm kvap-of-acons
                        (implies (and (kvap x) (kp k) (vp v)) (kvap (acons k v x)))
                        ar-key-val-alist-p-of-acons)

                (fi-thm mkvp-of-assoc-equal-of-kvap
                        (implies (and (kp k) (kvap x)) (mkvp (assoc-equal k x)))
                        ar-maybe-key-val-consp-of-assoc-equal-of-ar-key-val-alist-p)

                (fi-thm booleanp-of-equal-of-mkvp
                        (implies (and (mkvp x) (mkvp y))
                                 (booleanp (equal x y)))
                        booleanp-of-equal-of-ar-maybe-key-val-consp)

                (fi-thm vp-of-cdr-of-mkvp
                        (implies (and (mkvp x) (not (equal x nil)))
                                 (vp (cdr x)))
                        ar-val-p-of-cdr-of-ar-maybe-key-val-consp)

                (fi-thm replace-of-mkv->nil
                        (implies (mkvp nil)
                                 (equal nil (mkv->nil)))
                        replace-of-ar-maybe-key-val-consp->nil
                        :rule-classes nil)

	              (encapsulate nil
	                ;; booleanp-of-ar-kv-p can be prove using functional instantiation of
	                ;;   booleanp-of-ar-p in the theory '(ar-kv-p ar-kv-p-necc).  So, why
	                ;;   am I proving it by introducing three lemmas and using those?
	                ;;   My reason is that the proof for boolean-p-of-ar-kv-equiv (below)
	                ;;   fails with the corresponding hint.  I believe that's because the
	                ;;   functional constraints require showing that the bodies of
	                ;;   ar-kv-equiv and ar-kv-equiv-witness are what one would expect.
	                ;;   Sadly, the rewrite rule for ar-kv-equiv-necc has a hypothesis of
	                ;;     (ar-kv-equiv al ar)
	                ;;   The corresponding term in the proof goal gets re-written by the
	                ;;   rule (:d ar-kv-equiv), and then the rule for ar-kv-equiv-necc fails
	                ;;   to match.  At least that's what I think is happening.
	                ;;     I fixed the problem by using proof-builder to identify a sufficient
	                ;;   set of lemmas, prove those, and then prove the main theorem.  I'm
	                ;;   using the same approach here because I'm concerned that even though
	                ;;   the more succinct proof just using theory '(ar-kv-p ar-kv-p-necc)
	                ;;   succeeds, it may be sensitive to the order in which rewrites are
	                ;;   performed.  The current proof seems likely to be more robust.
	                ;;
	                ;; Here's how I got the lemmas.  I gave the commands:
	                ;;   ACL2 !> (verify (booleanp (ar-kv-equiv al ar)))
	                ;;   ->: (use (:functional-instance booleanp-of-ar-equiv ...))
	                ;;   ->: :s  ;; main.1 is trivial to discharge
	                ;;   ->: :split  ;; produces 7 goals corresponding to the functional constraints.
	                ;;   ->: print-all-goals
	                ;; I stated a lemma for each of the goals printed above.  The lemma
	                ;; main.4 is the contrapositive of main.1, and unused in the final proof;
;  so I don't state a lemma for it here.
	                (local (defthm fi-ar-kv-p-1
	                         (implies (ar-kv-p ar) (ua-p ar))
	                         :hints(("Goal" :in-theory '(ar-kv-p-necc)))))

	                (local (defthm fi-ar-kv-p-2
	                         (implies (ar-kv-p ar) (mkvp (ua-select ar k)))
	                         :hints(("Goal" :in-theory '(ar-kv-p-necc)))))

	                (local (defthm fi-ar-kv-p-3
	                         (implies (ua-p ar)
		                                (equal (ar-kv-p ar)
			                                     (mkvp (ua-select ar (ar-kv-p-witness ar)))))
	                         :hints(("Goal" :in-theory '(ar-kv-p)))))

	                (fi-thm booleanp-of-ar-kv-p
	                        (booleanp (ar-kv-p ar)) 
	                        booleanp-of-ar-p
                          :theory '(fi-ar-kv-p-1 fi-ar-kv-p-2 fi-ar-kv-p-3)))

	              (fi-thm ar-kv-p-of-ar-kv-init
	                      (ar-kv-p (ar-kv-init))
	                      ar-p-of-ar-init
                        :theory '(ar-kv-init))

	              (fi-thm ar-kv-p-of-ar-kv-store
	                      (ar-kv-p (ar-kv-store ar k kv))
	                      ar-p-of-ar-store
                        :theory '(ar-kv-store))

	              (verify-guards ar-kv-store)

	              (fi-thm ar-kv-p-of-ar-kv-from-al
	                      (ar-kv-p (ar-kv-from-al al))
	                      ar-p-of-ar-from-al
                        :theory '(ar-kv-from-al))

	              (verify-guards ar-kv-from-al
	                :hints(("Goal"
	                        :in-theory '(ar-kv-p-of-ar-kv-from-al kvap mkvp kvp))))

	              (fi-thm mkvp-of-ar-kv-select
	                      (mkvp (ar-kv-select ar k))
	                      ar-maybe-key-val-consp-of-ar-select
                        :theory '(ar-kv-select))

	              ;; init select and store behave like they should for arrays
	              (fi-thm ar-kv-select-of-ar-kv-init
	                      (equal (ar-kv-select (ar-kv-init) k) nil)
	                      ar-select-of-ar-init)

	              (fi-thm ar-kv-select-of-ar-kv-store
	                      (implies (and (ar-kv-p ar) (kp k0) (mkvp kv0))
		                             (equal (ar-kv-select (ar-kv-store ar k0 kv0) k1)
			                                  (if (equal k1 k0)
			                                      kv0
			                                    (ar-kv-select ar k1))))
	                      ar-select-of-ar-store)

                (fi-thm booleanp-of-ar-kv-equal
                        (booleanp (ar-kv-equal a1 a2))
                        booleanp-of-ar-equal
                        :theory '(ar-kv-equal))

                (fi-thm ar-kv-equal-implies-selects-equal
                        (implies (and (ar-kv-p a1) (ar-kv-p a2) (kp k)
                                      (ar-kv-equal a1 a2))
	                               (equal (ar-kv-select a1 k)
		                                    (ar-kv-select a2 k)))
                        ar-equal-implies-selects-equal)

                (fi-thm selects-of-witness-equal-implies-ar-kv-equal
                        (implies (and (ar-kv-p a1) (ar-kv-p a2))
                                 (let ((k (ar-kv-equal-witness a1 a2)))
                                   (equal (ar-kv-equal a1 a2)
	                                        (equal (ar-kv-select a1 k)
			                                           (ar-kv-select a2 k)))))
                        selects-of-witness-equal-implies-ar-equal
                        :theory '(ar-kv-equal-witness))

	              ;; translation of alist operations to operations on arrays
	              (encapsulate nil
	                ;; See the comments with the proof of booleanp-of-ar-kv-p to see
	                ;;   how I came up with these lemmas and why.
	                (local (defthm fi-ar-kv-equiv-1
	                         (implies (ar-kv-equiv al ar)
		                                (kvap al))
	                         :hints(("Goal" :in-theory '(ar-kv-equiv-necc)))))

	                (local (defthm fi-ar-kv-equiv-2
	                         (implies (ar-kv-equiv al ar)
		                                (equal (assoc-equal k al) (ar-kv-select ar k)))
	                         :hints(("Goal" :in-theory '(ar-kv-equiv-necc)))))

	                (local (defthm fi-ar-kv-equiv-3
	                         (implies (ar-kv-equiv al ar)
		                                (ar-kv-p ar))
	                         :hints(("Goal" :in-theory '(ar-kv-equiv-necc)))))

	                (local (defthm fi-ar-kv-equiv-5
	                         (implies (and (kvap al)
			                                   (ar-kv-p ar)
			                                   (equal (assoc-equal (ar-kv-equiv-witness al ar) al)
				                                        (ar-kv-select ar (ar-kv-equiv-witness al ar))))
		                                (equal (ar-kv-equiv al ar) t))
	                         :hints(("Goal" :in-theory '(ar-kv-equiv)))))

	                (fi-thm booleanp-of-ar-kv-equiv
	                        (booleanp (ar-kv-equiv al ar))
	                        booleanp-of-ar-equiv
	                        :theory '(fi-ar-kv-equiv-1
                                    fi-ar-kv-equiv-2
	                                  fi-ar-kv-equiv-3
	                                  fi-ar-kv-equiv-5)))

                (fi-thm ar-kv-translation-of-nil
                        (implies (kvap nil)
                                 (and (equal nil (car (cons nil (ar-kv-init))))
                                      (ar-kv-p (ar-kv-init))
                                      (ar-kv-equiv-consp (cons nil (ar-kv-init)))))
                        ar-translation-of-nil
                        :theory '(ar-kv-equiv-consp)
                        :rule-classes nil)

	              (fi-thm ar-kv-translation-of-acons
                        (implies (and (kp k)
		                                  (vp v)
                                      (ar-kv-equiv-consp (cons al ar)))
                                 (and (equal (acons k v (car (cons al ar)))
                                             (car (cons (acons k v al)
                                                        (ar-kv-store ar k (cons k v)))))
                                      (kvp (cons k v))
                                      (kvap (acons k v al))
                                      (ar-kv-p (ar-kv-store ar k (cons k v)))
                                      (ar-kv-equiv-consp
                                       (cons (acons k v al)
                                             (ar-kv-store ar k (cons k v))))))
                        ar-translation-of-acons)

	              (fi-thm ar-kv-translation-of-alist
                        (implies (kvap al)
                                 (and (equal al (car (cons al (ar-kv-from-al al))))
                                      (var-term (ar-kv-from-al al))
                                      (var-hyp (ar-kv-p (ar-kv-from-al al)))
                                      (hyp-judge (booleanp (ar-kv-p (ar-kv-from-al al))))
                                      (ar-kv-equiv-consp (cons al (ar-kv-from-al al)))))
                        ar-translation-of-alist
                        :rule-classes nil)

	              (fi-thm ar-kv-translation-of-assoc-equal
                        (implies (and (ar-kv-equiv-consp (cons al ar))
                                      (kp k))
	                               (equal (assoc-equal k (car (cons al ar)))
                                        (ar-kv-select ar k)))
                        ar-translation-of-assoc-equal)))

       (local (defthmd ,key-p-equals-kp
	              (equal (,key-p x) (kp x))        
	              :hints(("Goal" :in-theory '(kp ,key-p)))))

       (local (defthmd ,val-p-equals-vp
	              (equal (,val-p x) (vp x))        
	              :hints(("Goal" :in-theory '(vp ,val-p)))))

       (local (defthmd ,key-fix-equals-k-fix
                (equal (,key-fix x) (k-fix x))
                :hints(("Goal" :in-theory '(k-fix)))))

       (local (defthmd ,val-fix-equals-v-fix
                (equal (,val-fix x) (v-fix x))
                :hints(("Goal" :in-theory '(v-fix)))))

       ;; (local (defthmd ,key-p-of-key-fix
       ;;          (,key-p (,key-fix x))
       ;;          :hints(("Goal" :in-theory '(kp-of-k-fix
       ;;                                      ,key-p-equals-kp
       ;;                                      ,key-fix-equals-k-fix)))))

       ;; (local (defthmd ,replace-of-key-fix
       ;;          (implies (,key-p x) (equal (,key-fix x) x))
       ;;          :hints(("Goal" :in-theory '(replace-of-k-fix
       ;;                                      ,key-p-equals-kp
       ;;                                      ,key-fix-equals-k-fix)))))

       ;; (local (defthmd ,val-p-of-val-fix
       ;;          (,val-p (,val-fix x))
       ;;          :hints(("Goal" :in-theory '(vp-of-v-fix
       ;;                                      ,val-p-equals-vp
       ;;                                      ,val-fix-equals-v-fix)))))

       ;; (local (defthmd ,replace-of-val-fix
       ;;          (implies (,val-p x) (equal (,val-fix x) x))
       ;;          :hints(("Goal" :in-theory '(replace-of-v-fix
       ;;                                      ,val-p-equals-vp
       ;;                                      ,val-fix-equals-v-fix)))))

       (define ,key-val-consp (x)
	       (and (consp x)
	            (,key-p (car x))
	            (,val-p (cdr x))))

       (define ,key-val-cons-fix (x)
         (if (,key-val-consp x) x
           (cons (,key-fix nil) (,val-fix nil))))

       (local (defthmd ,key-val-consp-equals-kvp
	              (equal (,key-val-consp x) (kvp x))
	              :hints(("Goal"
	                      :in-theory '(,key-p-equals-kp ,val-p-equals-vp)
	                      :expand((,key-val-consp x) (kvp x))))))

       (local (defthmd ,key-val-cons-fix-equals-kv-fix
                (equal (,key-val-cons-fix x) (kv-fix x))
                :hints(("Goal"
                        :in-theory '(,key-val-consp-equals-kvp
                                     ,key-fix-equals-k-fix
                                     ,val-fix-equals-v-fix)
                        :expand ((,key-val-cons-fix x) (kv-fix x))))))

       (local (defthmd ,booleanp-of-key-val-consp
	              (booleanp (,key-val-consp x))
	              :hints(("Goal"
	                      :in-theory '(,key-val-consp-equals-kvp
	                                   booleanp-of-kvp)))))

       (local (defthmd ,key-val-consp-of-key-val-cons-fix
                (,key-val-consp (,key-val-cons-fix x))
                :hints(("Goal" :in-theory '(,key-val-consp-equals-kvp
                                            ,key-val-cons-fix-equals-kv-fix
                                            kvp-of-kv-fix)))))

       (local (defthmd ,replace-of-key-val-cons-fix
                (implies (,key-val-consp x) (equal (,key-val-cons-fix x) x))
                :hints(("Goal" :in-theory '(replace-of-kv-fix
                                            ,key-val-consp-equals-kvp
                                            ,key-val-cons-fix-equals-kv-fix)))))

       (local (defthmd ,key-p-of-car-of-key-val-consp
	              (implies (,key-val-consp x) (,key-p (car x)))
	              :hints(("Goal"
	                      :in-theory '(,key-val-consp-equals-kvp
                                     ,key-p-equals-kp
	                                   kp-of-car-of-kvp)))))

       (local (defthmd ,val-p-of-cdr-of-key-val-consp
	              (implies (,key-val-consp x) (,val-p (cdr x)))
	              :hints(("Goal"
	                      :in-theory '(,key-val-consp-equals-kvp
                                     ,val-p-equals-vp
	                                   vp-of-cdr-of-kvp)))))

       (define ,maybe-key-val-consp (x)
	       (implies x (,key-val-consp x)))

       (define ,maybe-key-val-cons-fix (x)
         (if (,key-val-consp x) x nil))

       (define ,maybe-key-val-cons->cons (x y)
         (cons (,key-fix x) (,val-fix y)))

       (define ,maybe-key-val-cons->car (x)
         :verify-guards nil
         (,key-fix (car (,maybe-key-val-cons-fix x))))

       (define ,maybe-key-val-cons->cdr (x)
         :verify-guards nil
         (,val-fix (cdr (,maybe-key-val-cons-fix x))))

       (define ,maybe-key-val-cons->nil () nil)

       (local (defthmd ,maybe-key-val-consp-equals-mkvp
	              (equal (,maybe-key-val-consp x) (mkvp x))
	              :hints(("Goal"
	                      :in-theory '(mkvp
                                     ,maybe-key-val-consp
	                                   ,key-val-consp-equals-kvp)))))

       (local (defthmd ,maybe-key-val-cons-fix-equals-mkv-fix
                (equal (,maybe-key-val-cons-fix x) (mkv-fix x))
                :hints(("Goal"
                        :in-theory '(mkvp ,key-val-consp-equals-kvp)
                        :expand ((,maybe-key-val-cons-fix x) (mkv-fix x))))))

       (local (defthmd ,maybe-key-val-cons->cons-equals-mkv->cons
         (equal (,maybe-key-val-cons->cons x y) (mkv->cons x y))
         :hints(("Goal"
                 :in-theory '(,key-fix-equals-k-fix ,val-fix-equals-v-fix)
                 :expand ((,maybe-key-val-cons->cons x y) (mkv->cons x y))))))

       (local (defthmd ,maybe-key-val-cons->car-equals-mkv->car
                (equal (,maybe-key-val-cons->car x) (mkv->car x))
                :hints(("Goal"
                        :in-theory '(,maybe-key-val-cons-fix-equals-mkv-fix
                                     ,key-fix-equals-k-fix)
                        :expand ((,maybe-key-val-cons->car x) (mkv->car x))))))

       (local (defthmd ,maybe-key-val-cons->cdr-equals-mkv->cdr
                (equal (,maybe-key-val-cons->cdr x) (mkv->cdr x))
                :hints(("Goal"
                        :in-theory '(,maybe-key-val-cons-fix-equals-mkv-fix
                                     ,val-fix-equals-v-fix)
                        :expand ((,maybe-key-val-cons->cdr x) (mkv->cdr x))))))

       (local (defthm ,car-of-cons-of-maybe-key-val-consp
         (implies (and (,key-p x) (,val-p y))
                  (equal (,maybe-key-val-cons->car
                          (,maybe-key-val-cons->cons x y))
                         x))
         :hints (("Goal" :in-theory (enable car-of-cons-of-maybe-key-val-consp
                                            ,key-p-equals-kp
                                            ,val-p-equals-vp
                                            ,maybe-key-val-cons->car-equals-mkv->car
                                            ,maybe-key-val-cons->cons-equals-mkv->cons)))))

       (local (defthm ,cdr-of-cons-of-maybe-key-val-consp
                (implies (and (,key-p x) (,val-p y))
                         (equal (,maybe-key-val-cons->cdr
                                 (,maybe-key-val-cons->cons x y))
                                y))
                :hints (("Goal" :in-theory (enable cdr-of-cons-of-maybe-key-val-consp
                                                   ,key-p-equals-kp
                                                   ,val-p-equals-vp
                                                   ,maybe-key-val-cons->cdr-equals-mkv->cdr
                                                   ,maybe-key-val-cons->cons-equals-mkv->cons)))))

       (local (defthm ,cons-of-car-and-cdr-of-maybe-key-val-consp
                (implies (and (,maybe-key-val-consp x) x)
                         (equal (,maybe-key-val-cons->cons
                                 (,maybe-key-val-cons->car x)
                                 (,maybe-key-val-cons->cdr x))
                                x))
                :hints (("Goal"
                         :in-theory (enable cons-of-car-and-cdr-of-mkvp
                                            ,maybe-key-val-consp-equals-mkvp
                                            ,maybe-key-val-cons->cons-equals-mkv->cons
                                            ,maybe-key-val-cons->car-equals-mkv->car
                                            ,maybe-key-val-cons->cdr-equals-mkv->cdr)))))

       (local (defthmd ,maybe-key-val-cons->nil-equals-mkv->nil
                (equal (,maybe-key-val-cons->nil) (mkv->nil))
                :hints(("Goal" :expand ((,maybe-key-val-cons->nil) (mkv->nil))))))

       (local (defthmd ,booleanp-of-maybe-key-val-consp
	              (booleanp (,maybe-key-val-consp x))
	              :hints(("Goal"
	                      :in-theory '(,maybe-key-val-consp-equals-mkvp
	                                   booleanp-of-mkvp)))))

       (local (defthmd ,booleanp-of-equal-of-maybe-key-val-consp
                (implies (and (,maybe-key-val-consp x)
                              (,maybe-key-val-consp y))
                         (booleanp (equal x y)))
                :hints (("Goal"
                         :in-theory '(,maybe-key-val-consp-equals-mkvp
                                      booleanp-of-equal-of-mkvp)))))

       (local (defthmd ,val-p-of-cdr-of-maybe-key-val-consp
                (implies (and (,maybe-key-val-consp x) (not (equal x nil)))
                         (,val-p (cdr x)))
                :hints (("Goal"
                         :in-theory '(,maybe-key-val-consp-equals-mkvp
                                      ,val-p-equals-vp vp-of-cdr-of-mkvp)))))

       (local (defthm ,replace-of-maybe-key-val-cons->nil
                (implies (,maybe-key-val-consp nil)
                         (equal nil (,maybe-key-val-cons->nil)))
                :hints (("Goal"
                         :in-theory '(,maybe-key-val-consp-equals-mkvp
                                      ,maybe-key-val-cons->nil-equals-mkv->nil)
                         :use ((:instance replace-of-mkv->nil))))
                :rule-classes nil))


       (local (defthmd ,maybe-key-val-consp-of-maybe-key-val-cons-fix
                (,maybe-key-val-consp (,maybe-key-val-cons-fix x))
                :hints(("Goal" :in-theory '(,maybe-key-val-consp-equals-mkvp
                                            ,maybe-key-val-cons-fix-equals-mkv-fix
                                            mkvp-of-mkv-fix)))))

       (local (defthmd ,maybe-key-val-consp-of-maybe-key-val-cons->cons
                (implies (and (,key-p x) (,val-p y))
                         (,maybe-key-val-consp (,maybe-key-val-cons->cons x y)))
                :hints (("Goal" :in-theory '(mkvp-of-mkv->cons
                                             ,key-p-equals-kp
                                             ,val-p-equals-vp
                                             ,maybe-key-val-consp-equals-mkvp
                                             ,maybe-key-val-cons->cons-equals-mkv->cons
                                             )))))

       (local (defthmd ,key-p-of-maybe-key-val-cons->car
                (implies (and (,maybe-key-val-consp x) (not (equal x nil)))
                         (,key-p (,maybe-key-val-cons->car x)))
                :hints (("Goal" :in-theory '(kp-of-mkv->car
                                             ,key-p-equals-kp
                                             ,maybe-key-val-consp-equals-mkvp
                                             ,maybe-key-val-cons->car-equals-mkv->car)))))

       (local (defthmd ,val-p-of-maybe-key-val-cons->cdr
                (implies (and (,maybe-key-val-consp x) (not (equal x nil)))
                         (,val-p (,maybe-key-val-cons->cdr x)))
                :hints (("Goal" :in-theory '(vp-of-mkv->cdr
                                             ,val-p-equals-vp
                                             ,maybe-key-val-consp-equals-mkvp
                                             ,maybe-key-val-cons->cdr-equals-mkv->cdr)))))

       (local (defthmd ,replace-of-cdr-of-key-val-consp
                (implies (,key-val-consp x)
                         (equal (cdr x) (,maybe-key-val-cons->cdr x)))
                :hints (("Goal" :in-theory '(replace-of-cdr-of-kvp
                                             ,key-val-consp-equals-kvp
                                             ,maybe-key-val-cons->cdr-equals-mkv->cdr)))))

       (local (defthmd ,maybe-key-val-consp-of-maybe-key-val-cons->nil
                (,maybe-key-val-consp (,maybe-key-val-cons->nil))
                :hints (("Goal" :in-theory '(mkvp-of-mkv->nil
                                             ,maybe-key-val-consp-equals-mkvp
                                             ,maybe-key-val-cons->nil-equals-mkv->nil)))))

       (local (defthmd ,replace-of-maybe-key-val-cons-fix
                (implies (,maybe-key-val-consp x)
                         (equal (,maybe-key-val-cons-fix x) x))
                :hints(("Goal" :in-theory '(replace-of-mkv-fix
                                            ,maybe-key-val-consp-equals-mkvp
                                            ,maybe-key-val-cons-fix-equals-mkv-fix)))))

       (local (defthmd ,maybe-key-val-consp-canbe-key-val-consp
                (implies (and (,maybe-key-val-consp x) (not (equal x nil)))
                         (,key-val-consp x))
                :hints(("Goal"
                        :in-theory '(,maybe-key-val-consp-equals-mkvp
                                     ,key-val-consp-equals-kvp
                                     mkvp-canbe-kvp)))))

       (define ,key-val-alist-p (x)
	       (or (not x)
	           (and (consp x)
		              (consp (car x))
		              (,key-p (caar x))
		              (,val-p (cdar x))
		              (,key-val-alist-p (cdr x)))))

       (define ,key-val-alist-fix (x)
         (if (,key-val-alist-p x) x nil))

       (local (defthmd ,key-val-alist-p-equals-kvap
	              (equal (,key-val-alist-p x) (kvap x))
	              :hints(("Goal"
	                      :in-theory (e/d (,key-val-alist-p
                                         kvap kvp ,key-p-equals-kp
	                                       ,val-p-equals-vp)
                                        (,replace-of-cdr-of-key-val-consp
                                         replace-of-cdr-of-kvp))))))

       (local (defthmd ,key-val-alist-fix-equals-kva-fix
                (equal (,key-val-alist-fix x) (kva-fix x))
                :hints(("Goal"
                        :in-theory '(,key-val-alist-p-equals-kvap)
                        :expand ((,key-val-alist-fix x) (kva-fix x))))))

       (local (defthmd ,booleanp-of-key-val-alist-p
	              (booleanp (,key-val-alist-p x))
	              :hints(("Goal"
	                      :in-theory '(,key-val-alist-p-equals-kvap
	                                   booleanp-of-kvap)))))

       (local (defthmd ,key-val-alist-p-of-key-val-alist-fix
                (,key-val-alist-p (,key-val-alist-fix x))
                :hints(("Goal" :in-theory '(,key-val-alist-p-equals-kvap
                                            ,key-val-alist-fix-equals-kva-fix
                                            kvap-of-kva-fix)))))

       (local (defthmd ,replace-of-key-val-alist-fix
                (implies (,key-val-alist-p x) (equal (,key-val-alist-fix x) x))
                :hints(("Goal" :in-theory '(replace-of-kva-fix
                                            ,key-val-alist-p-equals-kvap
                                            ,key-val-alist-fix-equals-kva-fix)))))

       (local (defthmd ,key-val-alist-p-of-acons
                (implies (and (,key-val-alist-p x) (,key-p k) (,val-p v))
                         (,key-val-alist-p (acons k v x)))
                :hints (("Goal"
                         :in-theory '(kvap-of-acons
                                      ,key-p-equals-kp ,val-p-equals-vp
                                      ,key-val-alist-p-equals-kvap)))))

       (local (defthmd ,maybe-key-val-consp-of-assoc-equal-of-key-val-alist-p
                (implies (and (,key-p k) (,key-val-alist-p x))
                         (,maybe-key-val-consp (assoc-equal k x)))
                :hints(("Goal"
                        :in-theory '(,key-val-alist-p-equals-kvap
                                     ,key-p-equals-kp
                                     ,maybe-key-val-consp-equals-mkvp
                                     mkvp-of-assoc-equal-of-kvap)))))

       (encapsulate
	       (((,key-val-array-p *) => *)
	        ((,key-val-array-init) => *)
	        ((,key-val-array-store * * *) => *)
	        ((,key-val-array-from-al *) => *)
	        ((,key-val-array-select * *) => *)
	        ((,key-val-array-equiv * *) => *)
          ((,key-val-array-equiv-consp *) => *)
          ((,key-val-array-equal * *) => *)
          ((,key-val-array-equal-witness * *) => *))

	       (local (defun ,key-val-array-p (ar) (ar-kv-p ar)))
	       (local (defun ,key-val-array-init () (ar-kv-init)))
	       (local (defun ,key-val-array-store (ar k kv) (ar-kv-store ar k kv)))
	       (local (defun ,key-val-array-from-al (al) (ar-kv-from-al al)))
	       (local (defun ,key-val-array-select (ar k) (ar-kv-select ar k)))
	       (local (defun ,key-val-array-equiv (al ar) (ar-kv-equiv al ar)))
         (local (defun ,key-val-array-equiv-consp (x) (ar-kv-equiv-consp x)))
         (local (defun ,key-val-array-equal (a1 a2) (ar-kv-equal a1 a2)))
         (local (defun ,key-val-array-equal-witness (a1 a2) (ar-kv-equal-witness a1 a2)))

	       ;; return type constraints
	       (defthmd ,booleanp-of-key-val-array-p
	         (booleanp (,key-val-array-p ar))
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-p)
	                 :use((:instance booleanp-of-ar-kv-p (ar ar))))))

	       (defthmd ,key-val-array-p-of-key-val-array-init
	         (,key-val-array-p (,key-val-array-init))
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-init ,key-val-array-p ar-kv-p-of-ar-kv-init))))

	       (defthmd ,key-val-array-p-of-key-val-array-store
	         (,key-val-array-p (,key-val-array-store ar k kv))
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-store ,key-val-array-p ar-kv-p-of-ar-kv-store))))

	       (defthmd ,key-val-array-p-of-key-val-array-from-al
	         (,key-val-array-p (,key-val-array-from-al al))
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-from-al ,key-val-array-p ar-kv-p-of-ar-kv-from-al))))

	       (defthmd ,maybe-key-val-consp-of-key-val-array-select
	         (,maybe-key-val-consp (,key-val-array-select ar k))
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-select ,maybe-key-val-consp-equals-mkvp mkvp-of-ar-kv-select))))

	       (defthmd ,booleanp-of-key-val-array-equiv
	         (booleanp (,key-val-array-equiv al ar))
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-equiv booleanp-of-ar-kv-equiv))))

	       ;; array operation constraints
	       (defthmd ,key-val-array-select-of-key-val-array-init
	         (equal (,key-val-array-select (,key-val-array-init) k) nil)
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-select ,key-val-array-init ,key-p-equals-kp)
	                 :use((:instance ar-kv-select-of-ar-kv-init)))))

	       (defthmd ,key-val-array-select-of-key-val-array-store
	         (implies (and (,key-val-array-p ar) (,key-p k0) (,maybe-key-val-consp kv0))
		                (equal (,key-val-array-select (,key-val-array-store ar k0 kv0) k1)
			                     (if (equal k1 k0)
			                         kv0
			                       (,key-val-array-select ar k1))))
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-select ,key-val-array-store ,key-val-array-p
			                                                ,key-p-equals-kp ,maybe-key-val-consp-equals-mkvp)
	                 :use((:instance ar-kv-select-of-ar-kv-store)))))

         (defthmd ,booleanp-of-key-val-array-equal
           (booleanp (,key-val-array-equal a1 a2))
           :hints (("Goal"
                    :in-theory '(,key-val-array-equal)
                    :use ((:instance booleanp-of-ar-kv-equal)))))

         (defthmd ,key-val-array-equal-implies-selects-equal
           (implies (and (,key-val-array-p a1) (,key-val-array-p a2) (,key-p k)
                         (,key-val-array-equal a1 a2))
	                  (equal (,key-val-array-select a1 k)
		                       (,key-val-array-select a2 k)))
           :hints (("Goal"
                    :in-theory '(,key-val-array-equal
                                 ,key-val-array-p ,key-p-equals-kp ,key-val-array-select)
                    :use ((:instance ar-kv-equal-implies-selects-equal)))))

         (defthmd ,selects-of-witness-equal-implies-key-val-array-equal
           (implies (and (,key-val-array-p a1) (,key-val-array-p a2))
                    (let ((k (,key-val-array-equal-witness a1 a2)))
                      (equal (,key-val-array-equal a1 a2)
	                           (equal (,key-val-array-select a1 k)
			                              (,key-val-array-select a2 k)))))
           :hints (("Goal"
                    :in-theory '(,key-val-array-equal-witness
                                 ,key-val-array-equal ,key-val-array-p
                                 ,key-val-array-select)
                    :use ((:instance selects-of-witness-equal-implies-ar-kv-equal)))))

	       ;; translating alist values and operations to array versions
         (defthm ,key-val-array-translation-of-nil
           (implies (,key-val-alist-p nil)
                    (and (equal nil (car (cons nil (,key-val-array-init))))
                         (,key-val-array-p (,key-val-array-init))
                         (,key-val-array-equiv-consp (cons nil (,key-val-array-init)))))
           :hints(("Goal"
                   :in-theory '(,key-val-alist-p-equals-kvap
                                ,key-val-array-p
                                ,key-val-array-equiv-consp
                                ,key-val-array-init)
                   :use ((:instance ar-kv-translation-of-nil))))
           :rule-classes nil)

         (defthm ,key-val-array-translation-of-alist
           (implies (,key-val-alist-p al)
                    (and (equal al (car (cons al (,key-val-array-from-al al))))
                         (var-term (,key-val-array-from-al al))
                         (var-hyp (,key-val-array-p (,key-val-array-from-al al)))
                         (hyp-judge (booleanp (,key-val-array-p (,key-val-array-from-al al))))
                         (,key-val-array-equiv-consp (cons al (,key-val-array-from-al al)))))
           :hints(("Goal" :in-theory '(,key-val-alist-p-equals-kvap
                                       ,key-val-array-from-al
                                       ,key-val-array-p
                                       ,key-val-array-equiv-consp)
                   :use ((:instance ar-kv-translation-of-alist))))
           :rule-classes nil)

         (defthmd ,key-val-array-translation-of-acons
           (implies (and (,key-val-array-equiv-consp (cons al ar))
		                     (,key-p k)
		                     (,val-p v))
                    (and (equal (acons k v (car (cons al ar)))
                                (car (cons (acons k v al)
                                           (,key-val-array-store ar k (cons k v)))))
                         (,key-val-consp (cons k v))
                         (,key-val-alist-p (acons k v al))
                         (,key-val-array-p (,key-val-array-store ar k (cons k v)))
                         (,key-val-array-equiv-consp
                          (cons (acons k v al)
                                (,key-val-array-store ar k (cons k v))))))
           :hints(("Goal" :in-theory '(,key-p-equals-kp
                                       ,val-p-equals-vp
                                       ,key-val-consp-equals-kvp
                                       ,key-val-alist-p-equals-kvap
                                       ,key-val-array-p
                                       ,key-val-array-store
                                       ,key-val-array-equiv-consp
                                       ar-kv-translation-of-acons))))

         (defthmd ,key-val-array-translation-of-assoc-equal
           (implies (and (,key-val-array-equiv-consp (cons al ar))
                         (,key-p k))
                    (equal (assoc-equal k (car (cons al ar)))
                           (,key-val-array-select ar k)))
           :hints(("Goal" :in-theory '(,key-val-array-p
                                       ,key-p-equals-kp
                                       ,key-val-array-select
                                       ,key-val-array-equiv-consp
                                       ar-kv-translation-of-assoc-equal))))))))

(defmacro defalist-smt (key-val-alist-p key-p key-fix val-p val-fix)
  (defalist-smt-fn key-val-alist-p key-p key-fix val-p val-fix))
