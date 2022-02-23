(in-package "SMT")
(include-book "std/util/top" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "identity-fns")
(include-book "array")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate ;; Type recognizers for indices and elements of alists
  (((ar-key-p *) => *)
   ((ar-val-p *) => *)
   ((ar-key-fix *) => *)
   ((ar-val-fix *) => *))

  (local (defun ar-key-p (x) (booleanp x)))
  (local (defun ar-key-fix (x) (bool-fix x)))
  (local (defun ar-val-p (x) (rationalp x)))
  (local (defun ar-val-fix (x) (rfix x)))

  (defthm booleanp-of-ar-key-p (booleanp (ar-key-p x)))
  (defthm booleanp-of-ar-val-p (booleanp (ar-val-p x)))
  (defthm ar-key-p-of-ar-key-fix (ar-key-p (ar-key-fix x)))
  (defthm ar-val-p-of-ar-val-fix (ar-val-p (ar-val-fix x)))
  (defthm replace-of-ar-key-fix
    (implies (ar-key-p x) (equal (ar-key-fix x) x)))
  (defthm replace-of-ar-val-fix
    (implies (ar-val-p x) (equal (ar-val-fix x) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; typed  alists

(define ar-key-val-consp (x)
  :returns (ok booleanp)
  :enabled t
  (and (consp x)
       (ar-key-p (car x))
       (ar-val-p (cdr x)))
  ///
  (more-returns
   (ok :name consp-when-ar-key-val-consp
	     (implies ok (consp x)))
   (ok (implies ok (ar-key-p (car x)))
	     :name ar-key-p-of-car-of-ar-key-val-consp)
   (ok (implies ok (ar-val-p (cdr x)))
	     :name ar-val-p-of-cdr-of-ar-key-val-consp)))

(define ar-key-val-cons-fix (x)
  :returns (r ar-key-val-consp)
  (if (ar-key-val-consp x) x
    (cons (ar-key-fix nil) (ar-val-fix nil)))
  ///
  (more-returns
   (r :name replace-of-ar-key-val-cons-fix
      (implies (ar-key-val-consp x) (equal r x)))))

(define ar-maybe-key-val-consp (x)
  :returns (ok booleanp)
  :enabled t
  (implies x (ar-key-val-consp x))
  ///
  (more-returns
   (ok :name ar-maybe-key-val-consp-when-ar-key-val-consp
	     (implies (ar-key-val-consp x) ok))
   (ok :name ar-maybe-key-val-consp-canbe-ar-key-val-consp
       (implies (and ok (not (equal x nil)))
                (ar-key-val-consp x))))
  (defthmd booleanp-of-equal-of-ar-maybe-key-val-consp
    (implies (and (ar-maybe-key-val-consp x)
                  (ar-maybe-key-val-consp y))
             (booleanp (equal x y))))
  (defthmd ar-val-p-of-cdr-of-ar-maybe-key-val-consp
    (implies (and (ar-maybe-key-val-consp x) (not (equal x nil)))
             (ar-val-p (cdr x)))))

(define ar-maybe-key-val-cons-fix (x)
  :returns (r ar-maybe-key-val-consp)
  (if (ar-maybe-key-val-consp x) x nil)
  ///
  (more-returns
   (r :name replace-of-ar-maybe-key-val-cons-fix
      (implies (ar-maybe-key-val-consp x) (equal r x)))))

(define ar-maybe-key-val-consp->cons (x y)
  :returns (r)
  (cons (ar-key-fix x) (ar-val-fix y))
  ///
  (more-returns
   (r :name ar-maybe-key-val-consp-of-ar-maybe-key-val-consp->cons
      (implies (and (ar-key-p x) (ar-val-p y))
               (ar-maybe-key-val-consp r)))))

(define ar-maybe-key-val-consp->car (x)
  :returns (k)
  (ar-key-fix (car (ar-maybe-key-val-cons-fix x)))
  ///
  (more-returns
   (k :name ar-key-p-of-ar-maybe-key-val-consp->car
      (implies (and (ar-maybe-key-val-consp x) (not (equal x nil)))
               (ar-key-p k)))))

(define ar-maybe-key-val-consp->cdr (x)
  :returns (v)
  (ar-val-fix (cdr (ar-maybe-key-val-cons-fix x)))
  ///
  (more-returns
   (v :name ar-val-p-of-ar-maybe-key-val-consp->cdr
      (implies (and (ar-maybe-key-val-consp x) (not (equal x nil)))
               (ar-val-p v))))
  (defthmd replace-of-cdr-of-ar-key-val-consp
    (implies (ar-key-val-consp x)
             (equal (cdr x) (ar-maybe-key-val-consp->cdr x)))))

(defthm car-of-cons-of-maybe-key-val-consp
  (implies (and (ar-key-p x) (ar-val-p y))
           (equal (ar-maybe-key-val-consp->car
                   (ar-maybe-key-val-consp->cons x y))
                  x))
  :hints (("Goal"
           :in-theory (enable ar-maybe-key-val-consp->car
                              ar-maybe-key-val-consp->cons))))

(defthm cdr-of-cons-of-maybe-key-val-consp
  (implies (and (ar-key-p x) (ar-val-p y))
           (equal (ar-maybe-key-val-consp->cdr
                   (ar-maybe-key-val-consp->cons x y))
                  y))
  :hints (("Goal"
           :in-theory (enable ar-maybe-key-val-consp->cdr
                              ar-maybe-key-val-consp->cons))))

(defthm cons-of-car-and-cdr-of-ar-maybe-key-val-consp
  (implies (and (ar-maybe-key-val-consp x) x)
           (equal (ar-maybe-key-val-consp->cons
                   (ar-maybe-key-val-consp->car x)
                   (ar-maybe-key-val-consp->cdr x))
                  x))
  :hints (("Goal"
           :in-theory (enable ar-maybe-key-val-consp->cons
                              ar-maybe-key-val-consp->car
                              ar-maybe-key-val-consp->cdr))))

(define ar-maybe-key-val-consp->nil ()
  :returns (r ar-maybe-key-val-consp)
  nil
  ///
  (defthm replace-of-ar-maybe-key-val-consp->nil
    (implies (ar-maybe-key-val-consp nil)
             (equal nil (ar-maybe-key-val-consp->nil)))
    :rule-classes nil))

(define ar-key-val-alist-p (x)
  :returns (ok booleanp)
  (if x
      (and (consp x)
	         (ar-key-val-consp (car x))
	         (ar-key-val-alist-p (cdr x)))
    t)
  ///
  (more-returns
   (ok (implies ok (alistp x))
       :name alistp-when-ar-key-val-alist-p
	     :hints(("Goal" :in-theory (enable ar-key-val-alist-p))))
   (ok (implies (and ok x) (consp x))
       :name consp-when-ar-key-val-alist-p)
   (ok (implies ok (ar-key-val-alist-p (cdr x)))
	     :name cdr-when-ar-key-val-alist-p
	     :hints(("Goal" :in-theory (enable ar-key-val-alist-p))))
   (ok (implies (and x ok)
                (and (consp (car x)) (ar-key-val-consp (car x))))
	     :name car-when-ar-key-val-alist-p
	     :rule-classes (:rewrite (:forward-chaining :trigger-terms ((ar-key-val-alist-p x))))
	     :hints(("Goal" :in-theory (enable ar-key-val-alist-p))))
   (ok (implies (and ok (ar-key-p k) (ar-val-p v))
                (ar-key-val-alist-p (acons k v x)))
       :name ar-key-val-alist-p-of-acons)
   (ok (implies (and (ar-key-p k) ok) (ar-maybe-key-val-consp (assoc-equal k x)))
       :name ar-maybe-key-val-consp-of-assoc-equal-of-ar-key-val-alist-p)))

(define ar-key-val-alist-fix (x)
  :returns (r ar-key-val-alist-p)
  (if (ar-key-val-alist-p x) x nil)
  ///
  (more-returns
   (r :name replace-of-ar-key-val-alist-fix
      (implies (ar-key-val-alist-p x) (equal r x)))))

(in-theory (disable ar-key-val-consp ar-maybe-key-val-consp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ar-p and associated operators.
;; arrays that represents ar-key-val-alist-p values.

(acl2::define-sk ar-p (ar)
                 (forall (k)
                         (and (ua-p ar)
                              (ar-maybe-key-val-consp (ua-select ar k))))
                 ///
                 (local (in-theory (enable ar-p)))
                 (defthm ua-p-when-ar-p (implies (ar-p ar) (ua-p ar)))
                 (defthm ar-p-of-ua-init (ar-p (ua-init nil))))

(define ar-init () ;; create an empty array
  :returns (ar)
  (ua-init nil)
  ///
  (in-theory (disable (:e ar-init)))
  (more-returns (ar (ar-p ar) :name ar-p-of-ar-init)))

(define ar-store ((ar ar-p) (k ar-key-p) (kv ar-maybe-key-val-consp))
  :returns (ar2 ar-p
                :hints(("Goal"
                        :cases ((equal (ar-p-witness (ua-store ar k kv)) k))
                        :in-theory (e/d (ar-p) (ar-p-necc))
                        :use((:instance ar-p-necc
                                        (k (ar-p-witness (ua-store ar k kv))))))))
  (if (and (ar-key-p k) (ar-maybe-key-val-consp kv) (ar-p ar))
      (ua-store ar k kv)
    (ar-init)))

(define ar-select ((ar ar-p) (k ar-key-p))
  :returns (kv ar-maybe-key-val-consp)
  (if (ar-p ar)
      (ua-select ar k)
    nil))

(define ar-from-al ((al ar-key-val-alist-p)) ;; convert an alist to an array
  :returns (ar ar-p)
  :verify-guards nil
  (if (and (consp al) (ar-key-val-consp (car al)))
      (ar-store (ar-from-al (cdr al)) (caar al) (car al))
    (ar-init))
  ///
  (verify-guards ar-from-al ;; needs ar-p-of-ar-from-al
    :hints(("Goal" :in-theory (enable ar-key-val-consp)))))

(defthm ar-select-of-ar-init
  (equal (ar-select (ar-init) k) nil)
  :hints(("Goal" :in-theory (enable (:d ar-init) ar-select))))

(local (defthm ar-select-of-ar-store-when-keys-equal
         (implies (and (ar-p ar) (ar-key-p k) (ar-maybe-key-val-consp kv))
	                (equal (ar-select (ar-store ar k kv) k) kv))
         :hints(("Goal"
                 :in-theory (e/d (ar-select ar-store) ())
                 :use((:instance ar-p-of-ar-store))))))

(local (defthm ar-select-of-ar-store-when-keys-not-equal
         (implies (and (ar-p ar) (ar-key-p k0) (ar-maybe-key-val-consp kv0)
		                   (not (equal k1 k0)))
	                (equal (ar-select (ar-store ar k0 kv0) k1)
		                     (ar-select ar k1)))
         :hints(("Goal"
                 :in-theory (e/d (ar-select ar-store) (ar-p-of-ar-store))
                 :use((:instance ar-p-of-ar-store (k k0) (kv kv0)))))))

(defthm ar-select-of-ar-store
  (implies (and (ar-p ar) (ar-key-p k0) (ar-maybe-key-val-consp kv0))
	         (equal (ar-select (ar-store ar k0 kv0) k1)
		              (if (equal k1 k0)
		                  kv0
		                (ar-select ar k1)))))

(define ar-equal ((a1 ar-p) (a2 ar-p))
  :returns (ok booleanp)
  (if (and (ar-p a1) (ar-p a2))
      (ua-equal a1 a2)
    nil))

(define ar-equal-witness ((a1 ar-p) (a2 ar-p))
  :returns (ok)
  (if (and (ar-p a1) (ar-p a2))
      (ua-equal-witness a1 a2)
    nil))

(defthm ar-equal-implies-selects-equal
  (implies (and (ar-p a1) (ar-p a2) (ar-key-p k)
                (ar-equal a1 a2))
	         (equal (ar-select a1 k)
		              (ar-select a2 k)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable ar-equal ar-select)
           :use ((:instance ua-equal-implies-selects-equal)))))

(defthm selects-of-witness-equal-implies-ar-equal
  (implies (and (ar-p a1) (ar-p a2))
           (let ((k (ar-equal-witness a1 a2)))
             (equal (ar-equal a1 a2)
	                  (equal (ar-select a1 k)
			                     (ar-select a2 k)))))
  :hints (("Goal"
           :in-theory (enable ar-equal ar-select
                              ar-equal-witness))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; equivalence -- theorems that justify replacing operations on alists
;;   with operations on arrays.

(acl2::define-sk ar-equiv (al ar)
                 :returns (ok booleanp)
                 :verify-guards nil ;; we intend the stronger claim that ar-select and
                 (forall (k)        ;; assoc-equal match even for "bad" keys.
                         (and (ar-key-val-alist-p al)
	                            (ar-p ar)
	                            (equal (assoc-equal k al) (ar-select ar k)))))

(define ar-equiv-consp ((x))
  :returns (ok booleanp)
  :verify-guards nil
  (and (consp x) (ar-equiv (car x) (cdr x))))

(defthm ar-translation-of-nil
  (implies (ar-key-val-alist-p nil)
           (and (equal nil (car (cons nil (ar-init))))
                (ar-p (ar-init))
                (ar-equiv-consp (cons nil (ar-init)))))
  :hints (("Goal"
           :in-theory (enable ar-equiv-consp ar-equiv)))
  :rule-classes nil)

(defthm ar-translation-of-acons
  (implies (and (ar-key-p k)
		            (ar-val-p v)
                (ar-equiv-consp (cons al ar)))
           (and (equal (acons k v (car (cons al ar)))
                       (car (cons (acons k v al)
                                  (ar-store ar k (cons k v)))))
                (ar-key-val-consp (cons k v))
                (ar-key-val-alist-p (acons k v al))
                (ar-p (ar-store ar k (cons k v)))
                (ar-equiv-consp (cons (acons k v al)
                                      (ar-store ar k (cons k v))))))
  :hints(("Goal"
          :do-not-induct t
          :in-theory (e/d (ar-equiv ar-key-val-consp ar-key-val-alist-p ar-equiv-consp)
		                      (ar-equiv-necc))
          :use((:instance ar-equiv-necc
		                      (k (ar-equiv-witness (cons (cons k v) al)
					                                     (ar-store ar k (cons k v)))))))))

(encapsulate ()
  (local (defthm lemma1
           (ar-equiv nil (ar-init))
           :hints (("Goal"
                    :in-theory (enable ar-equiv)))))

  (local (defthm lemma2
           (implies (and (ar-equiv al ar)
                         (ar-key-p k)
                         (ar-val-p v))
                    (ar-equiv (cons (cons k v) al) (ar-store ar k (cons k v))))
           :hints(("Goal"
                   :do-not-induct t
                   :in-theory (e/d (ar-equiv ar-key-val-consp
                                             ar-key-val-alist-p)
                                   (ar-equiv-necc))
                   :use((:instance ar-equiv-necc
 		                               (k (ar-equiv-witness
                                       (cons (cons k v) al)
 					                             (ar-store ar k (cons k v))))))))))

  (local (defthm lemma-base
           (implies (and (ar-key-val-alist-p al) (not (consp al)))
	                  (ar-equiv al (ar-init)))
           :hints(("Goal" :cases (al)))))

  (local (defthm lemma-induct-lemma
           (implies (and (ar-key-val-alist-p al) (consp al))
	                  (and (ar-key-p (caar al))
		                     (ar-val-p (cdar al))))
           :hints(("Goal" :expand(
                                  (ar-key-val-alist-p al)
                                  (ar-key-val-consp (car al)))))))

  (local (defthm lemma-induct
           (let ((ar-cdr (ar-from-al (cdr al))))
             (implies (and (consp al)
		                       (ar-equiv (cdr al) ar-cdr)
		                       (ar-key-val-alist-p al))
	                    (ar-equiv al (ar-store ar-cdr (caar al) (car al)))))
           :hints(("Goal"
                   :in-theory (e/d (ar-key-val-consp)
		                               (lemma2 lemma-induct-lemma))
                   :use(
	                      (:instance lemma2
		                               (al (cdr al))
		                               (k  (caar al))
		                               (v  (cdar al))
		                               (ar (ar-from-al (cdr al))))
	                      (:instance lemma-induct-lemma (al al)))))))

  (local (defthm ar-translation-of-alist-helper-lemma
           (implies (ar-key-val-alist-p al)
	                  (ar-equiv al (ar-from-al al)))
           :hints(("Goal" :in-theory (enable ar-from-al)))))

  (defthm ar-translation-of-alist
    (implies (ar-key-val-alist-p al)
             (and (equal al (car (cons al (ar-from-al al))))
                  (var-term (ar-from-al al))
                  (var-hyp (ar-p (ar-from-al al)))
                  (hyp-judge (booleanp (ar-p (ar-from-al al))))
                  (ar-equiv-consp (cons al (ar-from-al al)))))
    :hints (("Goal"
             :in-theory (enable ar-equiv-consp var-hyp hyp-judge)))
    :rule-classes nil)
  )

(defthm ar-translation-of-assoc-equal
  (implies (and (ar-equiv-consp (cons al ar))
                (ar-key-p k))
	         (equal (assoc-equal k (car (cons al ar))) (ar-select ar k)))
  :hints(("Goal"
          :in-theory (e/d (ar-equiv ar-select ar-equiv-consp) (ar-equiv-necc))
          :use((:instance ar-equiv-necc)))))
