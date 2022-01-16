;; define an alist that maps natural numbers to symbols, and then introduce
;; the theorems Smtlink needs to translate such alists to Z3 arrays.
;;
;; https://www.sandraboynton.com/sboynton/Amazing%20Cows%20interview.html

(in-package "SMT")
(include-book "std/util/top" :dir :system)
(include-book "alist")
(set-gag-mode nil)

(local (encapsulate nil
         (define kp (x)
           :returns (ok booleanp)
           (natp x))

         (define k-fix (x)
           :returns (r kp :hints (("Goal" :in-theory (enable kp))))
           (nfix x)
           ///
           (more-returns
            (r :name replace-of-k-fix
               (implies (kp x) (equal r x))
               :hints (("Goal" :in-theory (enable kp))))))

         (define vp (x)
           :returns (ok booleanp)
           (symbolp x))

         (define v-fix (x)
           :returns (r vp :hints (("Goal" :in-theory (enable vp))))
           (symbol-fix x)
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
                                               (ar-maybe-key-val-cons-fix mkv-fix)
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
         ;;   of establishing the constraints for functional instantation one
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
                 (implies (kvp x)
                          (equal (cdr x) (mkv->cdr x)))
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
           ;; booleanp-of-ar-kv-p can be proven using functional instantiation of
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
                   :theory '(fi-ar-kv-equiv-1 fi-ar-kv-equiv-2 fi-ar-kv-equiv-3
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


;; Having established the main results using kp and vp, I'll now restate
;; them with natp and symbolp to produce the theorems needed by Smtlink.

(local (defthmd natp-equals-kp
         (equal (natp x) (kp x))        
         :hints(("Goal" :in-theory '(kp natp)))))

(local (defthmd symbolp-equals-vp
         (equal (symbolp x) (vp x))        
         :hints(("Goal" :in-theory '(vp symbolp)))))

(local (defthmd nfix-equals-k-fix
         (equal (nfix x) (k-fix x))
         :hints(("Goal" :in-theory '(k-fix)))))

(local (defthmd symbol-fix-equals-v-fix
         (equal (symbol-fix x) (v-fix x))
         :hints(("Goal" :in-theory '(v-fix)))))

;; (local (defthmd natp-of-nfix
;;          (natp (nfix x))
;;          :hints(("Goal" :in-theory '(kp-of-k-fix
;;                                      natp-equals-kp
;;                                      nfix-equals-k-fix)))))

;; (local (defthmd replace-of-nfix
;;          (implies (natp x) (equal (nfix x) x))
;;          :hints(("Goal" :in-theory '(replace-of-k-fix
;;                                      natp-equals-kp
;;                                      nfix-equals-k-fix)))))

;; (local (defthmd symbolp-of-symbol-fix
;;          (symbolp (symbol-fix x))
;;          :hints(("Goal" :in-theory '(vp-of-v-fix
;;                                      symbolp-equals-vp
;;                                      symbol-fix-equals-v-fix)))))

;; (local (defthmd replace-of-vfix
;;          (implies (symbolp x) (equal (symbol-fix x) x))
;;          :hints(("Goal" :in-theory '(replace-of-v-fix
;;                                      symbolp-equals-vp
;;                                      symbol-fix-equals-v-fix)))))

(define nat-sym-consp (x)
  (and (consp x)
       (natp (car x))
       (symbolp (cdr x))))

(define nat-sym-cons-fix (x)
  (if (nat-sym-consp x) x
    (cons (nfix nil) (symbol-fix nil))))

(local (defthmd nat-sym-consp-equals-kvp
         (equal (nat-sym-consp x) (kvp x))
         :hints(("Goal"
                 :in-theory '(natp-equals-kp symbolp-equals-vp)
                 :expand((nat-sym-consp x) (kvp x))))))

(local (defthmd nat-sym-cons-fix-equals-kv-fix
         (equal (nat-sym-cons-fix x) (kv-fix x))
         :hints(("Goal"
                 :in-theory '(nat-sym-consp-equals-kvp
                              nfix-equals-k-fix
                              symbol-fix-equals-v-fix)
                 :expand ((nat-sym-cons-fix x) (kv-fix x))))))

(local (defthmd booleanp-of-nat-sym-consp
         (booleanp (nat-sym-consp x))
         :hints(("Goal"
                 :in-theory '(nat-sym-consp-equals-kvp booleanp-of-kvp)))))

(local (defthmd nat-sym-consp-of-nat-sym-cons-fix
         (nat-sym-consp (nat-sym-cons-fix x))
         :hints(("Goal" :in-theory '(nat-sym-consp-equals-kvp
                                     nat-sym-cons-fix-equals-kv-fix
                                     kvp-of-kv-fix)))))

(local (defthmd replace-of-nat-sym-cons-fix
         (implies (nat-sym-consp x) (equal (nat-sym-cons-fix x) x))
         :hints(("Goal" :in-theory '(replace-of-kv-fix
                                     nat-sym-consp-equals-kvp
                                     nat-sym-cons-fix-equals-kv-fix)))))

(local (defthmd natp-of-car-of-nat-sym-consp
         (implies (nat-sym-consp x) (natp (car x)))
         :hints(("Goal"
                 :in-theory '(nat-sym-consp-equals-kvp
                              natp-equals-kp
                              kp-of-car-of-kvp)))))

(local (defthmd symbolp-of-cdr-of-nat-sym-consp
         (implies (nat-sym-consp x) (symbolp (cdr x)))
         :hints(("Goal"
                 :in-theory '(nat-sym-consp-equals-kvp
                              symbolp-equals-vp
                              vp-of-cdr-of-kvp)))))

(define maybe-nat-sym-consp (x)
  (implies x (nat-sym-consp x)))

(define maybe-nat-sym-cons-fix (x)
  (if (nat-sym-consp x) x nil))

(define maybe-nat-sym-cons->cons (x y)
  (cons (nfix x) (symbol-fix y)))

(define maybe-nat-sym-cons->car (x)
  :verify-guards nil
  (nfix (car (maybe-nat-sym-cons-fix x))))

(define maybe-nat-sym-cons->cdr (x)
  :verify-guards nil
  (symbol-fix (cdr (maybe-nat-sym-cons-fix x))))

(define maybe-nat-sym-cons->nil () nil)

(local (defthmd maybe-nat-sym-consp-equals-mkvp
         (equal (maybe-nat-sym-consp x) (mkvp x))
         :hints(("Goal"
                 :in-theory '(mkvp
                              maybe-nat-sym-consp
                              nat-sym-consp-equals-kvp)))))

(local (defthmd maybe-nat-sym-cons-fix-equals-mkv-fix
         (equal (maybe-nat-sym-cons-fix x) (mkv-fix x))
         :hints(("Goal"
                 :in-theory '(mkvp nat-sym-consp-equals-kvp)
                 :expand ((maybe-nat-sym-cons-fix x) (mkv-fix x))))))

(local (defthmd maybe-nat-sym-cons->cons-equals-mkv->cons
         (equal (maybe-nat-sym-cons->cons x y) (mkv->cons x y))
         :hints(("Goal"
                 :in-theory '(nfix-equals-k-fix symbol-fix-equals-v-fix)
                 :expand ((maybe-nat-sym-cons->cons x y) (mkv->cons x y))))))

(local (defthmd maybe-nat-sym-cons->car-equals-mkv->car
         (equal (maybe-nat-sym-cons->car x) (mkv->car x))
         :hints(("Goal"
                 :in-theory '(maybe-nat-sym-cons-fix-equals-mkv-fix
                              nfix-equals-k-fix)
                 :expand ((maybe-nat-sym-cons->car x) (mkv->car x))))))

(local (defthmd maybe-nat-sym-cons->cdr-equals-mkv->cdr
         (equal (maybe-nat-sym-cons->cdr x) (mkv->cdr x))
         :hints(("Goal"
                 :in-theory '(maybe-nat-sym-cons-fix-equals-mkv-fix
                              symbol-fix-equals-v-fix)
                 :expand ((maybe-nat-sym-cons->cdr x) (mkv->cdr x))))))

(local (defthm car-of-cons-of-maybe-nat-sym-consp
         (implies (and (natp x) (symbolp y))
                  (equal (maybe-nat-sym-cons->car
                          (maybe-nat-sym-cons->cons x y))
                         x))
         :hints (("Goal" :in-theory (enable car-of-cons-of-maybe-key-val-consp
                                            natp-equals-kp
                                            symbolp-equals-vp
                                            maybe-nat-sym-cons->car-equals-mkv->car
                                            maybe-nat-sym-cons->cons-equals-mkv->cons)))))

(local (defthm cdr-of-cons-of-maybe-nat-sym-consp
         (implies (and (natp x) (symbolp y))
                  (equal (maybe-nat-sym-cons->cdr
                          (maybe-nat-sym-cons->cons x y))
                         y))
         :hints (("Goal" :in-theory (enable cdr-of-cons-of-maybe-key-val-consp
                                            natp-equals-kp
                                            symbolp-equals-vp
                                            maybe-nat-sym-cons->cdr-equals-mkv->cdr
                                            maybe-nat-sym-cons->cons-equals-mkv->cons)))))

(local (defthmd cons-of-car-and-cdr-of-maybe-nat-sym-consp
         (implies (and (maybe-nat-sym-consp x) x)
                  (equal (maybe-nat-sym-cons->cons
                          (maybe-nat-sym-cons->car x)
                          (maybe-nat-sym-cons->cdr x))
                         x))
         :hints (("Goal"
                  :in-theory (enable cons-of-car-and-cdr-of-mkvp
                                     maybe-nat-sym-consp-equals-mkvp
                                     maybe-nat-sym-cons->cons-equals-mkv->cons
                                     maybe-nat-sym-cons->car-equals-mkv->car
                                     maybe-nat-sym-cons->cdr-equals-mkv->cdr)))))

(local (defthmd maybe-nat-sym-cons->nil-equals-mkv->nil
         (equal (maybe-nat-sym-cons->nil) (mkv->nil))
         :hints(("Goal" :expand ((maybe-nat-sym-cons->nil) (mkv->nil))))))

(local (defthmd booleanp-of-maybe-nat-sym-consp
         (booleanp (maybe-nat-sym-consp x))
         :hints(("Goal"
                 :in-theory '(maybe-nat-sym-consp-equals-mkvp
                              booleanp-of-mkvp)))))

(local (defthmd booleanp-of-equal-of-maybe-nat-sym-consp
         (implies (and (maybe-nat-sym-consp x)
                       (maybe-nat-sym-consp y))
                  (booleanp (equal x y)))
         :hints (("Goal"
                  :in-theory '(maybe-nat-sym-consp-equals-mkvp
                               booleanp-of-equal-of-mkvp)))))

(local (defthmd symbolp-of-cdr-of-maybe-nat-sym-consp
         (implies (and (maybe-nat-sym-consp x) (not (equal x nil)))
                  (symbolp (cdr x)))
         :hints (("Goal"
                  :in-theory '(maybe-nat-sym-consp-equals-mkvp
                               symbolp-equals-vp vp-of-cdr-of-mkvp)))))

(local (defthm replace-of-maybe-nat-sym-consp->nil
         (implies (maybe-nat-sym-consp nil)
                  (equal nil (maybe-nat-sym-cons->nil)))
         :hints (("Goal"
                  :in-theory '(maybe-nat-sym-consp-equals-mkvp
                               maybe-nat-sym-cons->nil-equals-mkv->nil)
                  :use ((:instance replace-of-mkv->nil))))
         :rule-classes nil))

(local (defthmd maybe-nat-sym-consp-of-maybe-nat-sym-cons-fix
         (maybe-nat-sym-consp (maybe-nat-sym-cons-fix x))
         :hints(("Goal" :in-theory '(maybe-nat-sym-consp-equals-mkvp
                                     maybe-nat-sym-cons-fix-equals-mkv-fix
                                     mkvp-of-mkv-fix)))))

(local (defthmd maybe-nat-sym-consp-of-maybe-nat-sym-cons->cons
         (implies (and (natp x) (symbolp y))
                  (maybe-nat-sym-consp (maybe-nat-sym-cons->cons x y)))
         :hints (("Goal" :in-theory '(mkvp-of-mkv->cons
                                      natp-equals-kp
                                      symbolp-equals-vp
                                      maybe-nat-sym-consp-equals-mkvp
                                      maybe-nat-sym-cons->cons-equals-mkv->cons)))))

(local (defthmd natp-of-maybe-nat-sym-cons->car
         (implies (and (maybe-nat-sym-consp x) (not (equal x nil)))
                  (natp (maybe-nat-sym-cons->car x)))
         :hints (("Goal" :in-theory '(kp-of-mkv->car
                                      natp-equals-kp
                                      maybe-nat-sym-consp-equals-mkvp
                                      maybe-nat-sym-cons->car-equals-mkv->car)))))

(local (defthmd symbolp-of-maybe-nat-sym-cons->cdr
         (implies (and (maybe-nat-sym-consp x) (not (equal x nil)))
                  (symbolp (maybe-nat-sym-cons->cdr x)))
         :hints (("Goal" :in-theory '(vp-of-mkv->cdr
                                      symbolp-equals-vp
                                      maybe-nat-sym-consp-equals-mkvp
                                      maybe-nat-sym-cons->cdr-equals-mkv->cdr)))))

(local (defthmd replace-of-cdr-of-nat-sym-consp
         (implies (nat-sym-consp x)
                  (equal (cdr x) (maybe-nat-sym-cons->cdr x)))
         :hints (("Goal" :in-theory '(replace-of-cdr-of-kvp
                                      nat-sym-consp-equals-kvp
                                      maybe-nat-sym-cons->cdr-equals-mkv->cdr)))))

(local (defthmd maybe-nat-sym-consp-of-maybe-nat-sym-cons->nil
         (maybe-nat-sym-consp (maybe-nat-sym-cons->nil))
         :hints (("Goal" :in-theory '(mkvp-of-mkv->nil
                                      maybe-nat-sym-consp-equals-mkvp
                                      maybe-nat-sym-cons->nil-equals-mkv->nil)))))

(local (defthmd replace-of-maybe-nat-sym-cons-fix
         (implies (maybe-nat-sym-consp x) (equal (maybe-nat-sym-cons-fix x) x))
         :hints(("Goal" :in-theory '(replace-of-mkv-fix
                                     maybe-nat-sym-consp-equals-mkvp
                                     maybe-nat-sym-cons-fix-equals-mkv-fix)))))

(local (defthmd maybe-nat-sym-consp-canbe-nat-sym-consp
         (implies (and (maybe-nat-sym-consp x) (not (equal x nil)))
                  (nat-sym-consp x))
         :hints(("Goal"
                 :in-theory '(maybe-nat-sym-consp-equals-mkvp
                              nat-sym-consp-equals-kvp
                              Mkvp-canbe-kvp)))))

(define nat-sym-alist-p (x)
  (or (not x)
      (and (consp x)
	         (consp (car x))
	         (natp (caar x))
	         (symbolp (cdar x))
	         (nat-sym-alist-p (cdr x)))))

(define nat-sym-alist-fix (x)
  (if (nat-sym-alist-p x) x nil))

(local (defthmd nat-sym-alist-p-equals-kvap
         (equal (nat-sym-alist-p x) (kvap x))
         :hints(("Goal"
                 :in-theory (e/d (nat-sym-alist-p
                                  kvap kvp natp-equals-kp
                                  symbolp-equals-vp)
                                 (replace-of-cdr-of-nat-sym-consp
                                  replace-of-cdr-of-kvp))))))

(local (defthmd nat-sym-alist-fix-equals-kva-fix
         (equal (nat-sym-alist-fix x) (kva-fix x))
         :hints(("Goal"
                 :in-theory '(nat-sym-alist-p-equals-kvap)
                 :expand ((nat-sym-alist-fix x) (kva-fix x))))))

(local (defthmd booleanp-of-nat-sym-alist-p
         (booleanp (nat-sym-alist-p x))
         :hints(("Goal"
                 :in-theory '(nat-sym-alist-p-equals-kvap booleanp-of-kvap)))))

(local (defthmd nat-sym-alist-p-of-nat-sym-alist-fix
         (nat-sym-alist-p (nat-sym-alist-fix x))
         :hints(("Goal" :in-theory '(nat-sym-alist-p-equals-kvap
                                     nat-sym-alist-fix-equals-kva-fix
                                     kvap-of-kva-fix)))))

(local (defthmd replace-of-alist-fix
         (implies (nat-sym-alist-p x) (equal (nat-sym-alist-fix x) x))
         :hints(("Goal" :in-theory '(replace-of-kva-fix
                                     nat-sym-alist-p-equals-kvap
                                     nat-sym-alist-fix-equals-kva-fix)))))

(local (defthmd maybe-nat-sym-consp-of-assoc-equal-of-nat-sym-alist-p
         (implies (and (natp k) (nat-sym-alist-p x))
                  (maybe-nat-sym-consp (assoc-equal k x)))
         :hints(("Goal"
                 :in-theory '(nat-sym-alist-p-equals-kvap
                              natp-equals-kp
                              maybe-nat-sym-consp-equals-mkvp
                              mkvp-of-assoc-equal-of-kvap)))))

(encapsulate
  (((nat-sym-array-p *) => *)
   ((nat-sym-array-init) => *)
   ((nat-sym-array-store * * *) => *)
   ((nat-sym-array-from-al *) => *)
   ((nat-sym-array-select * *) => *)
   ((nat-sym-array-equiv * *) => *)
   ((nat-sym-array-equiv-consp *) => *)
   ((nat-sym-array-equal * *) => *)
   ((nat-sym-array-equal-witness * *) => *))

  (local (defun nat-sym-array-p (ar) (ar-kv-p ar)))
  (local (defun nat-sym-array-init () (ar-kv-init)))
  (local (defun nat-sym-array-store (ar k kv) (ar-kv-store ar k kv)))
  (local (defun nat-sym-array-from-al (al) (ar-kv-from-al al)))
  (local (defun nat-sym-array-select (ar k) (ar-kv-select ar k)))
  (local (defun nat-sym-array-equiv (al ar) (ar-kv-equiv al ar)))
  (local (defun nat-sym-array-equiv-consp (x) (ar-kv-equiv-consp x)))
  (local (defun nat-sym-array-equal (a1 a2) (ar-kv-equal a1 a2)))
  (local (defun nat-sym-array-equal-witness (a1 a2) (ar-kv-equal-witness a1 a2)))

  ;; return type constraints
  (defthmd booleanp-of-nat-sym-array-p
    (booleanp (nat-sym-array-p ar))
    :hints(("Goal"
            :in-theory '(nat-sym-array-p)
            :use((:instance booleanp-of-ar-kv-p (ar ar))))))

  (defthmd nat-sym-array-p-of-nat-sym-array-init
    (nat-sym-array-p (nat-sym-array-init))
    :hints(("Goal"
            :in-theory '(nat-sym-array-init nat-sym-array-p
                                            ar-kv-p-of-ar-kv-init))))

  (defthmd nat-sym-array-p-of-nat-sym-array-store
    (nat-sym-array-p (nat-sym-array-store ar k kv))
    :hints(("Goal"
            :in-theory '(nat-sym-array-store nat-sym-array-p
                                             ar-kv-p-of-ar-kv-store))))

  (defthmd nat-sym-array-p-of-nat-sym-array-from-al
    (nat-sym-array-p (nat-sym-array-from-al al))
    :hints(("Goal"
            :in-theory '(nat-sym-array-from-al nat-sym-array-p
                                               ar-kv-p-of-ar-kv-from-al))))

  (defthmd maybe-nat-sym-cons-of-nat-sym-array-select
    (maybe-nat-sym-consp (nat-sym-array-select ar k))
    :hints(("Goal"
            :in-theory '(nat-sym-array-select maybe-nat-sym-consp-equals-mkvp
                                              mkvp-of-ar-kv-select))))

  (defthmd booleanp-of-man-sym-array-equiv
    (booleanp (nat-sym-array-equiv al ar))
    :hints(("Goal"
            :in-theory '(nat-sym-array-equiv booleanp-of-ar-kv-equiv))))

  ;; array operation constraints
  (defthmd nat-sym-array-select-of-nat-sym-array-init
    (equal (nat-sym-array-select (nat-sym-array-init) k) nil)
    :hints(("Goal"
            :in-theory '(nat-sym-array-select nat-sym-array-init natp-equals-kp)
            :use((:instance ar-kv-select-of-ar-kv-init)))))

  (defthmd nat-sym-array-select-of-nat-sym-array-store
    (implies (and (nat-sym-array-p ar) (natp k0) (maybe-nat-sym-consp kv0))
	           (equal (nat-sym-array-select (nat-sym-array-store ar k0 kv0) k1)
		                (if (equal k1 k0)
			                  kv0
			                (nat-sym-array-select ar k1))))
    :hints(("Goal"
            :in-theory '(nat-sym-array-select
                         nat-sym-array-store nat-sym-array-p
		                     natp-equals-kp maybe-nat-sym-consp-equals-mkvp)
            :use((:instance ar-kv-select-of-ar-kv-store)))))

  (defthmd booleanp-of-of-nat-sym-array-equal
    (booleanp (nat-sym-array-equal a1 a2))
    :hints (("Goal"
             :in-theory '(nat-sym-array-equal)
             :use ((:instance booleanp-of-ar-kv-equal)))))

  (defthm nat-sym-array-equal-implies-selects-equal
    (implies (and (nat-sym-array-p a1) (nat-sym-array-p a2) (natp k)
                  (nat-sym-array-equal a1 a2))
	           (equal (nat-sym-array-select a1 k)
		                (nat-sym-array-select a2 k)))
    :hints (("Goal"
             :in-theory '(nat-sym-array-equal
                          nat-sym-array-p natp-equals-kp nat-sym-array-select)
             :use ((:instance ar-kv-equal-implies-selects-equal)))))

  (defthm selects-of-witness-equal-implies-nat-sym-array-equal
    (implies (and (nat-sym-array-p a1) (nat-sym-array-p a2))
             (let ((k (nat-sym-array-equal-witness a1 a2)))
               (equal (nat-sym-array-equal a1 a2)
	                    (equal (nat-sym-array-select a1 k)
			                       (nat-sym-array-select a2 k)))))
    :hints (("Goal"
             :in-theory '(nat-sym-array-equal-witness
                          nat-sym-array-equal nat-sym-array-p
                          nat-sym-array-select)
             :use ((:instance selects-of-witness-equal-implies-ar-kv-equal)))))

;; translating alist values and operations to array versions
(defthm nat-sym-array-translation-of-nil
  (implies (nat-sym-alist-p nil)
           (and (equal nil (car (cons nil (nat-sym-array-init))))
                (nat-sym-array-p (nat-sym-array-init))
                (nat-sym-array-equiv-consp (cons nil (nat-sym-array-init)))))
  :hints(("Goal"
          :in-theory '(nat-sym-alist-p-equals-kvap
                       nat-sym-array-p
                       nat-sym-array-equiv-consp
                       nat-sym-array-init)
          :use ((:instance ar-kv-translation-of-nil))))
  :rule-classes nil)

(defthm nat-sym-array-translation-of-alist
  (implies (nat-sym-alist-p al)
           (and (equal al (car (cons al (nat-sym-array-from-al al))))
                (var-term (nat-sym-array-from-al al))
                (var-hyp (nat-sym-array-p (nat-sym-array-from-al al)))
                (hyp-judge (booleanp (nat-sym-array-p (nat-sym-array-from-al al))))
                (nat-sym-array-equiv-consp (cons al (nat-sym-array-from-al al)))))
  :hints(("Goal" :in-theory '(nat-sym-alist-p-equals-kvap
                              nat-sym-array-from-al
                              nat-sym-array-p
                              nat-sym-array-equiv-consp)
          :use ((:instance ar-kv-translation-of-alist))))
  :rule-classes nil)

(defthmd nat-sym-array-translation-of-acons
  (implies (and (nat-sym-array-equiv-consp (cons al ar))
		            (natp k)
		            (symbolp v))
           (and (equal (acons k v (car (cons al ar)))
                       (car (cons (acons k v al)
                                  (nat-sym-array-store ar k (cons k v)))))
                (nat-sym-consp (cons k v))
                (nat-sym-alist-p (acons k v al))
                (nat-sym-array-p (nat-sym-array-store ar k (cons k v)))
                (nat-sym-array-equiv-consp
                 (cons (acons k v al)
                       (nat-sym-array-store ar k (cons k v))))))
  :hints(("Goal" :in-theory '(natp-equals-kp
                              symbolp-equals-vp
                              nat-sym-consp-equals-kvp
                              nat-sym-alist-p-equals-kvap
                              nat-sym-array-p
                              nat-sym-array-store
                              ar-kv-translation-of-acons
                              nat-sym-array-equiv-consp))))

(defthmd nat-sym-array-translation-of-assoc-equal
  (implies (and (nat-sym-array-equiv-consp (cons al ar))
                (natp k))
           (equal (assoc-equal k (car (cons al ar)))
                  (nat-sym-array-select ar k)))
  :hints(("Goal" :in-theory '(nat-sym-array-p
                              natp-equals-kp
                              nat-sym-array-select
                              nat-sym-array-equiv-consp
                              ar-kv-translation-of-assoc-equal))))
)

