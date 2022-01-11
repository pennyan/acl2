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
  ((key-val-alist-p symbolp) (key-p symbolp) (val-p symbolp))
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
       (key-val-consp (mk-symbol `(,key-val "key-val-cons-p") key-val-alist-p))
       ((list maybe-key-val-consp
              key-val-array-p
	            key-val-array-init
	            key-val-array-store
	            key-val-array-from-al
	            key-val-array-select
	            key-val-array-equiv)
        (mk-symbol-list (list
	                       `(maybe ,key-val-consp)
	                       `(,array-name p)
	                       `(,array-name init)
	                       `(,array-name store)
	                       `(,array-name from-al)
	                       `(,array-name select)
	                       `(,array-name equiv))
	                      key-val-alist-p))
       ((list key-p-equals-kp
	            val-p-equals-vp
	            key-val-consp-equals-kvp
	            booleanp-of-key-val-consp
	            maybe-key-val-consp-equals-mkvp
	            booleanp-of-maybe-key-val-consp
	            key-val-alist-p-equals-kvap
	            booleanp-of-key-val-array-p
	            key-val-array-p-of-key-val-array-init
	            key-val-array-p-of-key-val-array-store
	            key-val-array-p-of-key-val-array-from-al
	            maybe-key-val-consp-of-key-val-array-select
	            booleanp-of-key-val-array-equiv
	            key-val-array-select-of-key-val-array-init
	            key-val-array-select-of-key-val-array-store
	            key-val-translation-of-nil
	            key-val-translation-of-alist
	            key-val-translation-of-acons
	            key-val-translation-of-assoc-equal)
        (mk-symbol-list (list
	                       `(,key-p equals kp)
	                       `(,val-p equals vp)
	                       `(,key-val-consp equals kvp)
	                       `(booleanp of ,key-val-consp)
	                       `(,maybe-key-val-consp equals mkvp)
	                       `(booleanp of ,maybe-key-val-consp)
	                       `(,key-val-alist-p equals kvap)
	                       `(booleanp of ,key-val-array-p)
	                       `(,key-val-array-p of ,key-val-array-init)
	                       `(,key-val-array-p of ,key-val-array-store)
	                       `(,key-val-array-p of ,key-val-array-from-al)
	                       `(,maybe-key-val-consp of ,key-val-array-select)
	                       `(booleanp of ,key-val-array-equiv)
	                       `(,key-val-array-select of ,key-val-array-init)
	                       `(,key-val-array-select of ,key-val-array-store)
	                       `(,key-val translation of nil)
	                       `(,key-val translation of alist)
	                       `(,key-val translation of acons)
	                       `(,key-val translation of assoc-equal))
	                      key-val-alist-p)))
    `(progn
       (local (encapsulate nil
	              (define kp (x)
	                :returns (ok booleanp)
	                (,key-p x))

	              (define vp (x)
	                :returns (ok booleanp)
	                (,val-p x))

	              (define kvp (x)
	                (and (consp x)
	                     (kp (car x))
	                     (vp (cdr x))))

	              (define mkvp (x) (implies x (kvp x)))

	              (define kvap (x)
	                (if x
	                    (and (consp x)
		                       (kvp (car x))
		                       (kvap (cdr x)))
	                  t))
	              
	              (acl2::define-sk ar-kv-p (ar)
	                :returns (ok)
	                (forall (k)
	                        (and (ua-p ar)
		                           (mkvp (ua-select k ar)))))

	              (define ar-kv-init ()
	                (ua-init nil)
	                ///
	                (in-theory (disable (:e ar-kv-init))))

	              (define ar-kv-store ((k kp) (kv mkvp) (ar ar-kv-p))
	                :verify-guards nil
	                (if (and (kp k) (mkvp kv) (ar-kv-p ar))
	                    (ua-store k kv ar)
	                  (ar-kv-init)))

	              (define ar-kv-from-al ((al kvap))
	                :verify-guards nil
	                (if (and (consp al) (kvp (car al)))
	                    (ar-kv-store (caar al) (car al) (ar-kv-from-al (cdr al)))
	                  (ar-kv-init)))

	              (define ar-kv-select ((k kp) (ar ar-kv-p))
	                (if (ar-kv-p ar)
	                    (ua-select k ar)
	                  nil))

	              (acl2::define-sk ar-kv-equiv (al ar)
	                :returns (ok)
	                :verify-guards nil
	                (forall (k)
		                      (and (kvap al)
		                           (ar-kv-p ar)
		                           (equal (assoc-equal k al) (ar-kv-select k ar)))))


	              ;; Rather than writing the long functional instantiation hint for each of the
	              ;; theorems below, I'll wrap it up with a macro.
	              (defmacro fi-thm (name claim ar-thm &optional theory)
	                `(defthm ,name ,claim :hints(("Goal"
	                                              :in-theory ,theory
	                                              :use((:functional-instance ,ar-thm
					                                                                 ;; instantiate the generic functions
					                                                                 (ar-key-p kp)
					                                                                 (ar-val-p vp)
					                                                                 ;; instantiate the other relevant functions
					                                                                 (ar-key-val-consp kvp)
					                                                                 (ar-maybe-key-val-consp mkvp)
					                                                                 (ar-key-val-alist-p kvap)
					                                                                 (ar-p ar-kv-p)
					                                                                 (ar-p-witness ar-kv-p-witness)
					                                                                 (ar-init ar-kv-init)
					                                                                 (ar-store ar-kv-store)
					                                                                 (ar-from-al ar-kv-from-al)
					                                                                 (ar-select ar-kv-select)
					                                                                 (ar-equiv ar-kv-equiv)
					                                                                 (ar-equiv-witness ar-kv-equiv-witness)))))))


	              ;; return type theorems
	              ;;   In addition to providing returns theorems used by Smtlink, proving
	              ;;   these theorems by functional instantiation has the salubrious effect
	              ;;   of establishing the constraints for funcitional instantation one
	              ;;   function at a time.  This seems to avoid having ACL2 generate a big,
	              ;;   complicated constraint that it then is unable to discharge.

	              (fi-thm booleanp-of-kvp
	                      (booleanp (kvp x))
	                      booleanp-of-ar-key-val-consp '(kvp booleanp-of-kp booleanp-of-vp))

	              (fi-thm booleanp-of-mkvp
	                      (booleanp (mkvp x))
	                      booleanp-of-ar-maybe-key-val-consp '(mkvp (:t kvp)))

	              (fi-thm booleanp-of-kvap
	                      (booleanp (kvap x))
	                      booleanp-of-ar-key-val-alist-p '(kvap))

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
	                         (implies (ar-kv-p ar) (mkvp (ua-select k ar)))
	                         :hints(("Goal" :in-theory '(ar-kv-p-necc)))))

	                (local (defthm fi-ar-kv-p-3
	                         (implies (ua-p ar)
		                                (equal (ar-kv-p ar)
			                                     (mkvp (ua-select (ar-kv-p-witness ar) ar))))
	                         :hints(("Goal" :in-theory '(ar-kv-p)))))

	                (fi-thm booleanp-of-ar-kv-p
	                        (booleanp (ar-kv-p ar)) 
	                        booleanp-of-ar-p '(fi-ar-kv-p-1 fi-ar-kv-p-2 fi-ar-kv-p-3)))

	              (fi-thm ar-kv-p-of-ar-kv-init
	                      (ar-kv-p (ar-kv-init))
	                      ar-p-of-ar-init '(ar-kv-init))

	              (fi-thm ar-kv-p-of-ar-kv-store
	                      (ar-kv-p (ar-kv-store k kv ar))
	                      ar-p-of-ar-store '(ar-kv-store))

	              (verify-guards ar-kv-store)

	              (fi-thm ar-kv-p-of-ar-kv-from-al
	                      (ar-kv-p (ar-kv-from-al al))
	                      ar-p-of-ar-from-al '(ar-kv-from-al))

	              (verify-guards ar-kv-from-al
	                :hints(("Goal"
	                        :in-theory '(ar-kv-p-of-ar-kv-from-al kvap mkvp kvp))))

	              (fi-thm mkvp-of-ar-kv-select
	                      (mkvp (ar-kv-select k ar))
	                      ar-maybe-key-val-consp-of-ar-select '(ar-kv-select))

	              ;; init select and store behave like they should for arrays
	              (fi-thm ar-kv-select-of-ar-kv-init
	                      (equal (ar-kv-select k (ar-kv-init)) nil)
	                      ar-select-of-ar-init)

	              (fi-thm ar-kv-select-of-ar-kv-store
	                      (implies (and (ar-kv-p ar) (kp k0) (mkvp kv0))
		                             (equal (ar-kv-select k1 (ar-kv-store k0 kv0 ar))
			                                  (if (equal k1 k0)
			                                      kv0
			                                    (ar-kv-select k1 ar))))
	                      ar-select-of-ar-store)


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
		                                (equal (assoc-equal k al) (ar-kv-select k ar)))
	                         :hints(("Goal" :in-theory '(ar-kv-equiv-necc)))))

	                (local (defthm fi-ar-kv-equiv-3
	                         (implies (ar-kv-equiv al ar)
		                                (ar-kv-p ar))
	                         :hints(("Goal" :in-theory '(ar-kv-equiv-necc)))))

	                (local (defthm fi-ar-kv-equiv-5
	                         (implies (and (kvap al)
			                                   (ar-kv-p ar)
			                                   (equal (assoc-equal (ar-kv-equiv-witness al ar) al)
				                                        (ar-kv-select (ar-kv-equiv-witness al ar) ar)))
		                                (equal (ar-kv-equiv al ar) t))
	                         :hints(("Goal" :in-theory '(ar-kv-equiv)))))

	                (fi-thm booleanp-of-ar-kv-equiv
	                        (booleanp (ar-kv-equiv al ar))
	                        booleanp-of-ar-equiv
	                        '(fi-ar-kv-equiv-1 fi-ar-kv-equiv-2 fi-ar-kv-equiv-3 fi-ar-kv-equiv-5)))

	              (fi-thm ar-kv-translation-of-nil
	                      (ar-kv-equiv nil (ar-kv-init))
	                      ar-translation-of-nil)

	              (fi-thm ar-kv-translation-of-acons
	                      (implies (and (ar-kv-equiv al ar)
			                                (kp k)
			                                (vp v))
		                             (ar-kv-equiv (cons (cons k v) al) (ar-kv-store k (cons k v) ar)))
	                      ar-translation-of-acons)

	              (fi-thm ar-kv-translation-of-alist
	                      (implies (kvap al) (ar-kv-equiv al (ar-kv-from-al al)))
	                      ar-translation-of-alist)

	              (fi-thm ar-kv-translation-of-assoc-equal
	                      (implies (ar-kv-equiv al ar)
		                             (equal (assoc-equal k al) (ar-kv-select k ar)))
	                      ar-translation-of-assoc-equal)))

       (local (defthm ,key-p-equals-kp
	              (equal (,key-p x) (kp x))        
	              :hints(("Goal" :in-theory '(kp ,key-p)))))

       (local (defthm ,val-p-equals-vp
	              (equal (,val-p x) (vp x))        
	              :hints(("Goal" :in-theory '(vp ,val-p)))))

       (define ,key-val-consp (x)
	       (and (consp x)
	            (,key-p (car x))
	            (,val-p (cdr x))))

       (local (defthm ,key-val-consp-equals-kvp
	              (equal (,key-val-consp x) (kvp x))
	              :hints(("Goal"
	                      :in-theory '(,key-p-equals-kp ,val-p-equals-vp)
	                      :expand((,key-val-consp x) (kvp x))))))

       (local (defthm ,booleanp-of-key-val-consp
	              (booleanp (,key-val-consp x))
	              :hints(("Goal"
	                      :in-theory '(,key-val-consp-equals-kvp booleanp-of-kvp)))))

       (define ,maybe-key-val-consp (x)
	       (implies x (,key-val-consp x)))

       (local (defthm ,maybe-key-val-consp-equals-mkvp
	              (equal (,maybe-key-val-consp x) (mkvp x))
	              :hints(("Goal"
	                      :in-theory '(,maybe-key-val-consp mkvp ,key-val-consp-equals-kvp)))))

       (local (defthm ,booleanp-of-maybe-key-val-consp
	              (booleanp (,maybe-key-val-consp x))
	              :hints(("Goal"
	                      :in-theory '(,maybe-key-val-consp-equals-mkvp booleanp-of-mkvp)))))

       (define ,key-val-alist-p (x)
	       (or (not x)
	           (and (consp x)
		              (consp (car x))
		              (,key-p (caar x))
		              (,val-p (cdar x))
		              (,key-val-alist-p (cdr x)))))

       (local (defthm ,key-val-alist-p-equals-kvap
	              (equal (,key-val-alist-p x) (kvap x))
	              :hints(("Goal"
	                      :in-theory (enable ,key-val-alist-p kvap kvp)))))

       (encapsulate
	       (((,key-val-array-p *) => *)
	        ((,key-val-array-init) => *)
	        ((,key-val-array-store * * *) => *)
	        ((,key-val-array-from-al *) => *)
	        ((,key-val-array-select * *) => *)
	        ((,key-val-array-equiv * *) => *))

	       (local (defun ,key-val-array-p (ar) (ar-kv-p ar)))
	       (local (defun ,key-val-array-init () (ar-kv-init)))
	       (local (defun ,key-val-array-store (k kv ar) (ar-kv-store k kv ar)))
	       (local (defun ,key-val-array-from-al (al) (ar-kv-from-al al)))
	       (local (defun ,key-val-array-select (k ar) (ar-kv-select k ar)))
	       (local (defun ,key-val-array-equiv (al ar) (ar-kv-equiv al ar)))

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
	         (,key-val-array-p (,key-val-array-store k kv ar))
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-store ,key-val-array-p ar-kv-p-of-ar-kv-store))))

	       (defthmd ,key-val-array-p-of-key-val-array-from-al
	         (,key-val-array-p (,key-val-array-from-al al))
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-from-al ,key-val-array-p ar-kv-p-of-ar-kv-from-al))))

	       (defthmd ,maybe-key-val-consp-of-key-val-array-select
	         (,maybe-key-val-consp (,key-val-array-select k ar))
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-select ,maybe-key-val-consp-equals-mkvp mkvp-of-ar-kv-select))))

	       (defthmd ,booleanp-of-key-val-array-equiv
	         (booleanp (,key-val-array-equiv al ar))
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-equiv booleanp-of-ar-kv-equiv))))

	       ;; array operation constraints
	       (defthmd ,key-val-array-select-of-key-val-array-init
	         (equal (,key-val-array-select k (,key-val-array-init)) nil)
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-select ,key-val-array-init ,key-p-equals-kp)
	                 :use((:instance ar-kv-select-of-ar-kv-init)))))

	       (defthmd ,key-val-array-select-of-key-val-array-store
	         (implies (and (,key-val-array-p ar) (,key-p k0) (,maybe-key-val-consp kv0))
		                (equal (,key-val-array-select k1 (,key-val-array-store k0 kv0 ar))
			                     (if (equal k1 k0)
			                         kv0
			                       (,key-val-array-select k1 ar))))
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-select ,key-val-array-store ,key-val-array-p
			                                                ,key-p-equals-kp ,maybe-key-val-consp-equals-mkvp)
	                 :use((:instance ar-kv-select-of-ar-kv-store)))))

	       ;; translating alist values and operations to array versions
	       (defthmd ,key-val-translation-of-nil
	         (,key-val-array-equiv nil (,key-val-array-init))
	         :hints(("Goal"
	                 :in-theory '(,key-val-array-equiv ,key-val-array-init
			                                               ar-kv-translation-of-nil))))

	       (defthmd ,key-val-translation-of-alist
	         (implies (,key-val-alist-p al)
		                (,key-val-array-equiv al (,key-val-array-from-al al)))
	         :hints(("Goal" :in-theory '(
	                                     ,key-val-alist-p-equals-kvap ,key-val-array-equiv ,key-val-array-from-al
	                                     ar-kv-translation-of-alist))))

	       (defthmd ,key-val-translation-of-acons
	         (implies (and (,key-val-array-equiv al ar)
			                   (,key-p k)
			                   (,val-p v))
		                (,key-val-array-equiv (cons (cons k v) al)
					                                (,key-val-array-store k (cons k v) ar)))
	         :hints(("Goal" :in-theory '(
	                                     ,key-p-equals-kp ,val-p-equals-vp ,key-val-alist-p-equals-kvap
	                                     ,key-val-array-p ,key-val-array-equiv ,key-val-array-store
	                                     ar-kv-translation-of-acons))))

	       (defthmd ,key-val-translation-of-assoc-equal
	         (implies (,key-val-array-equiv al ar)
		                (equal (assoc-equal k al) (,key-val-array-select k ar)))
	         :hints(("Goal" :in-theory '(
	                                     ,key-val-consp-equals-kvp ,key-val-alist-p-equals-kvap ,key-p-equals-kp
	                                     ,key-val-array-p ,key-val-array-equiv ,key-val-array-select
	                                     ar-kv-translation-of-assoc-equal))))))))

(defmacro defalist-smt (key-val-alist-p key-p val-p)
  (defalist-smt-fn key-val-alist-p key-p val-p))
