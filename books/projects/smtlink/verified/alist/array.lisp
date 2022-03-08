(in-package "SMT")
(include-book "std/util/top" :dir :system)

(encapsulate
; A model of arrays where the values of indices and elements can
; be of arbitrary types.
; The prefix ua- stands for "untyped array"
  (((ua-element-default) => *)
   ((ua-p *) => *)
   ((ua-init *) => *)
   ((ua-store * * *) => *)
   ((ua-select * *) => *)
   ((ua-get-default-element *) => *)
   ((ua-equal * *) => *)
   ((ua-equal-witness * *) => *))

  (local (define ua-element-default () nil))

  (local (define ua-alist-p ((x acl2::any-p))
           :returns (ok booleanp)
           :enabled t
           (or (not x)
	             (and (consp x)
	                  (consp (car x))
	                  (ua-alist-p (cdr x))))
           ///
           (more-returns
            (ok :name alistp-when-ua-alist-p
	              (implies ok (alistp x))
	              :hints(("Goal" :in-theory (enable ua-alist-p)))))))

  (local (define ua-alist-fix ((x ua-alist-p))
           :returns (xx ua-alist-p)
           (if (atom x)
               nil
             (let ((hd (car x)) (tl (cdr x)))
	             (cons
	              (if (consp hd)
	                  hd
	                (cons nil (ua-element-default)))
	              (ua-alist-fix tl))))
           ///
           (more-returns
            (xx :name ua-alist-fix-when-ua-alist-p
	              (implies (ua-alist-p x) (equal xx x))
                :hints(("Goal" :in-theory(enable ua-alist-p))))
            (xx :name len-of-ua-alist-fix
	              (equal (len xx) (len x))))))

  (local (define ua-p ((x acl2::any-p))
           :enabled t
           (and (consp x)
	              (ua-alist-p (car x)))))

  (local (define ua-fix ((ua ua-p))
           :returns (ar2 ua-p)
           :enabled t
           (if (consp ua)
               (cons (ua-alist-fix (car ua)) (cdr ua))
             (cons nil (ua-element-default)))
           ///
           (more-returns
            (ar2 :name ua-fix-when-ua-p
	               (implies (ua-p ua) (equal ar2 ua))))))

  (local (define ua-get-default-element ((ua ua-p))
           :returns (v0 acl2::any-p)
           :enabled t
           (cdr (ua-fix ua))))

  (local (define ua-init ((default-value acl2::any-p))
           :enabled t
           (cons nil default-value)))

  (local (define ua-store ((ua ua-p) (i acl2::any-p) (e acl2::any-p))
           :enabled t
           (let ((ua (ua-fix ua)))
             (cons (acons i e (car ua)) (cdr ua)))))

  (local (define ua-select ((ua ua-p) (i acl2::any-p))
           :enabled t
           (let ((ua (ua-fix ua))
	               (a  (assoc-equal i (car ua))))
             (if a
                 (cdr a)
	             (cdr ua)))))

  (local (acl2::define-sk ua-equal ((a1 ua-p) (a2 ua-p))
                          :returns (ok acl2::any-p)
                          (forall (k) (equal (ua-select a1 k) (ua-select a2 k)))))

; The theorems that create the constraints on the functions in our signature
  (defthm ua-p-of-ua-init (ua-p (ua-init v0)))

  (defthm ua-p-of-ua-store (ua-p (ua-store ua i v)))

  (defthm ua-get-default-element-of-ua-init
    (equal (ua-get-default-element (ua-init v0)) v0))

  (defthm ua-get-default-element-of-ua-store
    (implies (ua-p ua)
             (equal (ua-get-default-element (ua-store ua i v))
		                (ua-get-default-element ua))))

  (defthm ua-select-of-ua-init (equal (ua-select (ua-init v) i) v))

  (defthm ua-select-of-ua-store-when-indices-equal
    (implies (ua-p ua)
	           (equal (ua-select (ua-store ua i v0) i) v0)))

  (defthm ua-select-of-ua-store-when-indices-not-equal
    (implies (and (ua-p ua) (not (equal i1 i0)))
	           (equal (ua-select (ua-store ua i0 v0) i1)
		                (ua-select ua i1))))

  (defthm booleanp-of-ua-equal
    (booleanp (ua-equal a1 a2))
    :hints (("Goal"
             :in-theory (enable ua-equal))))

  (defthm reflexivity-of-ua-equal
    (ua-equal ua ua)
    :hints (("Goal" :in-theory (enable ua-equal))))

  (defthm symmetricity-of-ua-equal
    (implies (ua-equal a1 a2) (ua-equal a2 a1))
    :hints (("Goal"
             :in-theory (e/d (ua-equal) (ua-select))
             :use ((:instance ua-equal-necc
                              (k (ua-equal-witness a2 a1)))))))

  (defthm ua-equal-implies-select-equal
    (implies (ua-equal a1 a2)
	           (equal (ua-select a1 k)
		                (ua-select a2 k)))
    :rule-classes nil
    :hints (("Goal"
             :use((:instance ua-equal-necc)))))

  (defthm transitivity-of-ua-equal
    (implies (and (ua-equal a1 a2) (ua-equal a2 a3))
             (ua-equal a1 a3))
    :hints (("Goal"
             :in-theory (e/d (ua-equal) (ua-select))
             :use ((:instance ua-equal-implies-select-equal
                              (a1 a1)
                              (a2 a2)
                              (k (ua-equal-witness a1 a3)))
                   (:instance ua-equal-implies-select-equal
                              (a1 a2)
                              (a2 a3)
                              (k (ua-equal-witness a1 a3)))))))

  (defthm select-of-witness-equal-implies-ua-equal
    (let ((k (ua-equal-witness a1 a2)))
      (equal (ua-equal a1 a2)
	           (equal (ua-select a1 k)
			              (ua-select a2 k))))
    :hints (("Goal"
             :in-theory (enable ua-equal))))
  )
