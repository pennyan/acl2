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
   ;; ((ua-equal * *) => *)
   )

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

  (local (define ua-store ((i acl2::any-p) (e acl2::any-p) (ua ua-p))
           :enabled t
           (let ((ua (ua-fix ua)))
             (cons (acons i e (car ua)) (cdr ua)))))

  (local (define ua-select ((i acl2::any-p) (ua ua-p))
           :enabled t
           (let ((ua (ua-fix ua))
	               (a  (assoc-equal i (car ua))))
             (if a
                 (cdr a)
	             (cdr ua)))))

; The theorems that create the constraints on the functions in our signature
  (defthm ua-p-of-ua-init (ua-p (ua-init v0)))

  (defthm ua-p-of-ua-store (ua-p (ua-store i v ua)))

  (defthm ua-get-default-element-of-ua-init
    (equal (ua-get-default-element (ua-init v0)) v0))

  (defthm ua-get-default-element-of-ua-store
    (implies (ua-p ua)
             (equal (ua-get-default-element (ua-store i v ua))
		                (ua-get-default-element ua))))

  (defthm ua-select-of-ua-init (equal (ua-select i (ua-init v)) v))

  (defthm ua-select-of-ua-store-when-indices-equal
    (implies (ua-p ua)
	           (equal (ua-select i (ua-store i v0 ua)) v0)))

  (defthm ua-select-of-ua-store-when-indices-not-equal
    (implies (and (ua-p ua) (not (equal i1 i0)))
	           (equal (ua-select i1 (ua-store i0 v0 ua))
		                (ua-select i1 ua))))
  )
