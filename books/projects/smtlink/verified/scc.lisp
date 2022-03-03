;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (Feb 25th 2022)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "std/alists/alist-fix" :dir :system)

(include-book "../utils/basics")

;; ----------------------------------------------------------------
;;  Tarjan's strongly connected components algorithm

(defprod scc-tarjan-args
  ((ids symbol-integer-alistp)
   (low symbol-integer-alistp)
   (on-stack symbol-boolean-alistp)
   (stack symbol-listp)
   (count natp :default 0)))

(define pop-stack-helper ((args scc-tarjan-args-p)
                          (node symbolp))
  :returns (new-args scc-tarjan-args-p)
  :measure (len (scc-tarjan-args->stack (scc-tarjan-args-fix args)))
  (b* ((args (scc-tarjan-args-fix args))
       ((scc-tarjan-args a) args)
       (node (symbol-fix node))
       ((unless a.stack)
        (prog2$ (er hard? 'scc=>pop-stack-helper
                    "INTERNAL: Tarjan's strongly connected component ~
                     reaches impossible state.~%")
                a))
       ((cons stack-top new-stack) a.stack)
       (new-on-stack (acons stack-top nil a.on-stack))
       (args-1 (change-scc-tarjan-args a
                                       :stack new-stack
                                       :on-stack new-on-stack))
       ((if (equal stack-top node)) args-1))
    (pop-stack-helper args-1 node))
  ///
  (more-returns
   (new-args (equal (scc-tarjan-args->ids new-args)
                    (scc-tarjan-args->ids args))
             :name pop-stack-helper-maintains-ids)))

(define pop-stack ((args scc-tarjan-args-p)
                   (stop symbolp))
  :returns (new-args scc-tarjan-args-p)
  (b* ((args (scc-tarjan-args-fix args))
       (stop (symbol-fix stop)))
    (pop-stack-helper args stop))
  ///
  (more-returns
   (new-args (equal (scc-tarjan-args->ids new-args)
                    (scc-tarjan-args->ids args))
             :name pop-stack-maintains-ids)))

(defines scc-tarjan-dfs
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil
  :ruler-extenders :all

  (define scc-tarjan-dfs-loop ((children symbol-listp)
                               (parent symbolp)
                               (map symbol-symbol-list-alistp)
                               (args scc-tarjan-args-p)
                               (clock natp))
    :returns (new-args scc-tarjan-args-p)
    :measure (list (nfix clock) (len (symbol-list-fix children)))
    (b* ((children (symbol-list-fix children))
         (map (symbol-symbol-list-alist-fix map))
         (args (scc-tarjan-args-fix args))
         (clock (nfix clock))
         ((scc-tarjan-args a) args)
         ((unless (consp children)) a)
         ((cons child-hd child-tl) children)
         (visited? (assoc-equal child-hd a.ids))
         (args-1 (if visited? a (scc-tarjan-dfs child-hd map args clock)))
         ((scc-tarjan-args a1) args-1)
         ((unless (cdr (assoc-equal child-hd a1.on-stack))) a)
         (parent-exists? (assoc-equal parent a1.low))
         (child-hd-exists? (assoc-equal child-hd a1.low))
         ((unless (and parent-exists? child-hd-exists?))
          (prog2$
           (er hard? 'scc=>scc-tarjan-dfs
               "INTERNAL: Tarjan's strongly connected component reaches ~
                impossible state.~%")
           a))
         (parent-low (min (cdr parent-exists?) (cdr child-hd-exists?))))
      (scc-tarjan-dfs-loop child-tl parent map
                           (change-scc-tarjan-args
                            a1 :low (acons parent parent-low a1.low))
                           clock)))

  (define scc-tarjan-dfs ((vertex symbolp)
                          (map symbol-symbol-list-alistp)
                          (args scc-tarjan-args-p)
                          (clock natp))
    :returns (new-args scc-tarjan-args-p)
    :measure (list (nfix clock) 0)
    (b* ((vertex (symbol-fix vertex))
         (map (symbol-symbol-list-alist-fix map))
         (args (scc-tarjan-args-fix args))
         (clock (nfix clock))
         ((if (zp clock)) args)
         ((scc-tarjan-args a) args)
         (args-1
          (change-scc-tarjan-args a
                                  :stack (cons vertex a.stack)
                                  :on-stack (acons vertex t a.on-stack)
                                  :ids (acons vertex a.count a.ids)
                                  :low (acons vertex a.count a.low)
                                  :count (1+ a.count)))
         (vertex-exists? (assoc-equal vertex map))
         ((unless vertex-exists?)
          (prog2$
           (er hard? 'scc=>scc-tarjan-dfs
               "INTERNAL: Tarjan's strongly connected component reaches ~
                          impossible state.~%")
           a))
         (children (cdr vertex-exists?))
         (args-2 (scc-tarjan-dfs-loop children vertex map args-1 (1- clock)))
         ((scc-tarjan-args a2) args-2)
         (ids-exists? (assoc-equal vertex a2.ids))
         (low-exists? (assoc-equal vertex a2.low))
         ((unless (and low-exists? ids-exists?))
          (prog2$
           (er hard? 'scc=>scc-tarjan-dfs
               "INTERNAL: Tarjan's strongly connected component reaches ~
                          impossible state.~%")
           a))
         ((if (equal (cdr ids-exists?) (cdr low-exists?)))
          (pop-stack a2 vertex)))
      args-2))
  )

(encapsulate ()
  (local (defthm crock
           (implies (integerp x) (rationalp x))))
  (verify-guards scc-tarjan-dfs))

(define scc-tarjan ((map symbol-symbol-list-alistp)
                    (args scc-tarjan-args-p))
  :returns (new-args scc-tarjan-args-p)
  :measure (len (symbol-symbol-list-alist-fix map))
  (b* ((map (symbol-symbol-list-alist-fix map))
       (args (scc-tarjan-args-fix args))
       ((scc-tarjan-args a) args)
       ((unless (consp map)) args)
       ((cons vertex-hd vertex-tl) map)
       ((cons vertex &) vertex-hd)
       ((if (assoc-equal vertex a.ids))
        (scc-tarjan vertex-tl args))
       (new-args (scc-tarjan-dfs vertex map args (len map))))
    (scc-tarjan vertex-tl new-args)))

(define scc-top ((map symbol-symbol-list-alistp))
  :returns (sccs scc-tarjan-args-p)
  (b* ((map (symbol-symbol-list-alist-fix map)))
    (scc-tarjan map (make-scc-tarjan-args))))

;; (scc-top '((a . (b))
;;            (b . (c))
;;            (c . (d))
;;            (d . (a))))

;; (scc-top '((a . (b))
;;            (b . (c))
;;            (c . (d e))
;;            (d . (a))
;;            (e . (f))
;;            (f . (g))
;;            (g . (e h))
;;            (h . ())
;;            (i . (h))
;;            (j . ())))


;; ----------------------------------------------------------------

(defthm alist-fix-of-integer-integer-list-alistp
  (implies (integer-integer-list-alistp x)
           (equal (acl2::alist-fix x) (integer-integer-list-alist-fix x)))
  :hints (("Goal" :in-theory (enable integer-integer-list-alistp))))

(defthm alist-fix-of-integer-symbol-list-alistp
  (implies (integer-symbol-list-alistp x)
           (equal (acl2::alist-fix x) (integer-symbol-list-alist-fix x)))
  :hints (("Goal" :in-theory (enable integer-symbol-list-alistp))))

(defthm alist-fix-of-symbol-integer-alistp
  (implies (symbol-integer-alistp x)
           (equal (acl2::alist-fix x) (symbol-integer-alist-fix x)))
  :hints (("Goal" :in-theory (enable symbol-integer-alistp))))

(define alist-clean ((alst alistp)
                     (acc alistp))
  :returns (new-alst alistp)
  :measure (len (acl2::alist-fix alst))
  :hints (("Goal" :in-tHeory (enable acl2::alist-fix)))
  (b* ((alst (acl2::alist-fix alst))
       (acc (acl2::alist-fix acc))
       ((unless (consp alst)) acc)
       ((cons hd tl) alst)
       ((cons key val) hd)
       (exists? (assoc-equal key acc))
       ((if exists?) (alist-clean tl acc)))
    (alist-clean tl (acons key val acc)))
  ///
  (more-returns
   (new-alst (implies (and (integer-integer-list-alistp alst)
                           (integer-integer-list-alistp acc))
                      (integer-integer-list-alistp new-alst))
             :name integer-integer-list-alistp-of-alist-clean)
   (new-alst (implies (and (integer-symbol-list-alistp alst)
                           (integer-symbol-list-alistp acc))
                      (integer-symbol-list-alistp new-alst))
             :name integer-symbol-list-alistp-of-alist-clean)
   (new-alst (implies (and (symbol-integer-alistp alst)
                           (symbol-integer-alistp acc))
                      (symbol-integer-alistp new-alst))
             :name symbol-integer-alistp-of-alist-clean)))

(define process-scc-helper ((vertex symbolp)
                            (children symbol-listp)
                            (scc-alst symbol-integer-alistp)
                            (acc integer-integer-list-alistp))
  :returns (id-alst integer-integer-list-alistp)
  :measure (len children)
  (b* ((vertex (symbol-fix vertex))
       (children (symbol-list-fix children))
       (scc-alst (symbol-integer-alist-fix scc-alst))
       (acc (integer-integer-list-alist-fix acc))
       ((unless (consp children)) acc)
       ((cons child-hd child-tl) children)
       (from-exists? (assoc-equal vertex scc-alst))
       (to-exists? (assoc-equal child-hd scc-alst))
       ((unless (and from-exists? to-exists?))
        (er hard? 'scc=>process-scc-helper
            "INTERNAL: Processing strongly connected component ~
             reaches impossible state.~%"))
       (from (cdr from-exists?))
       (to (cdr to-exists?))
       ((if (equal from to))
        (process-scc-helper vertex child-tl scc-alst acc))
       (curr (cdr (assoc-equal from acc)))
       ((if (member-equal to curr))
        (process-scc-helper vertex child-tl scc-alst acc)))
    (process-scc-helper vertex child-tl scc-alst
                        (acons from (cons to curr) acc))))

(define process-scc ((map symbol-symbol-list-alistp)
                     (scc-args scc-tarjan-args-p)
                     (acc integer-integer-list-alistp))
  :returns (id-alst integer-integer-list-alistp)
  :measure (len (symbol-symbol-list-alist-fix map))
  (b* ((map (symbol-symbol-list-alist-fix map))
       (scc-args (scc-tarjan-args-fix scc-args))
       ((scc-tarjan-args a) scc-args)
       (acc (integer-integer-list-alist-fix acc))
       ((unless (consp map)) acc)
       ((cons map-hd map-tl) map)
       ((cons vertex children) map-hd)
       (exists? (assoc-equal vertex a.low))
       ((unless exists?)
        (er hard? 'scc=>process-scc
            "INTERNAL: Processing strongly connected component ~
             reaches impossible state.~%"))
       (vertex-id (cdr exists?))
       (id-exists? (assoc-equal vertex-id acc))
       (new-acc
        (process-scc-helper vertex children a.low
                            (if id-exists? acc (acons vertex-id nil acc)))))
    (process-scc map-tl a new-acc)))

(define process-scc-top ((map symbol-symbol-list-alistp)
                         (scc-args scc-tarjan-args-p)
                         (acc integer-integer-list-alistp))
  :returns (id-alst integer-integer-list-alistp)
  (b* ((map (symbol-symbol-list-alist-fix map))
       (scc-args (scc-tarjan-args-fix scc-args))
       (acc (integer-integer-list-alist-fix acc)))
    (alist-clean (process-scc map scc-args acc) nil)))

;; (process-scc-top '((a . (b))
;;                    (b . (c))
;;                    (c . (d e))
;;                    (d . (a))
;;                    (e . (f))
;;                    (f . (g))
;;                    (g . (e h))
;;                    (h . ())
;;                    (i . (h))
;;                    (j . ()))
;;                  (scc-top '((a . (b))
;;                             (b . (c))
;;                             (c . (d e))
;;                             (d . (a))
;;                             (e . (f))
;;                             (f . (g))
;;                             (g . (e h))
;;                             (h . ())
;;                             (i . (h))
;;                             (j . ())))
;;                  nil)

;; ----------------------------------------------------------------

;; BOZO: implement a polymorphic topological sort and use it for
;; reorder-hypotheses and scc.

(define get-reverse-map-helper ((children integer-listp)
                                (vertex integerp)
                                (acc integer-integer-list-alistp))
  :returns (new-acc integer-integer-list-alistp)
  :measure (len children)
  (b* ((children (acl2::integer-list-fix children))
       (vertex (ifix vertex))
       (acc (integer-integer-list-alist-fix acc))
       ((unless (consp children)) acc)
       ((cons child-hd child-tl) children)
       (val-lst (cdr (assoc-equal child-hd acc)))
       (acc-1 (acons child-hd (cons vertex val-lst) acc)))
    (get-reverse-map-helper child-tl vertex acc-1)))

(define get-reverse-map ((scc-map integer-integer-list-alistp)
                         (acc integer-integer-list-alistp))
  :returns (new-acc integer-integer-list-alistp)
  :measure (len (integer-integer-list-alist-fix scc-map))
  (b* ((scc-map (integer-integer-list-alist-fix scc-map))
       (acc (integer-integer-list-alist-fix acc))
       ((unless (consp scc-map)) acc)
       ((cons scc-hd scc-tl) scc-map)
       ((cons vertex children) scc-hd)
       (acc-1 (if (assoc-equal vertex acc) acc (acons vertex nil acc)))
       (acc-2 (get-reverse-map-helper children vertex acc-1)))
    (get-reverse-map scc-tl acc-2)))

(define get-reverse-map-top ((scc-map integer-integer-list-alistp))
  :returns (new-acc integer-integer-list-alistp)
  (b* ((scc-map (integer-integer-list-alist-fix scc-map)))
    (alist-clean (get-reverse-map scc-map nil) nil)))

;; (get-reverse-map-top '((0 4) (4 7) (7) (8 7) (9)))

(define get-root ((rev-map integer-integer-list-alistp))
  :returns (roots integer-listp)
  :measure (len (integer-integer-list-alist-fix rev-map))
  (b* ((rev-map (integer-integer-list-alist-fix rev-map))
       ((unless (consp rev-map)) nil)
       ((cons rev-hd rev-tl) rev-map)
       ((cons vertex parents) rev-hd)
       ((if parents) (get-root rev-tl)))
    (cons vertex (get-root rev-tl))))

;; ---------------------------------------------------------
(defthm assoc-equal-of-integer-integer-list-alist
  (implies (and (integer-integer-list-alistp alst)
                (cdr (assoc-equal node alst)))
           (and (assoc-equal node alst)
                (consp (strip-cars alst)))))

(defthm implies-of-assoc-equal-of-integer-integer-list-alist
  (implies (and (integer-integer-list-alistp alst)
                (assoc-equal x alst))
           (integer-listp (cdr (assoc-equal x alst)))))

(defthm integer-list-of-remove-equal
  (implies (integer-listp lst)
           (integer-listp (remove-equal x lst))))

(define number-of-unresolved-scc ((rev-map integer-integer-list-alistp)
                                  (total integer-listp))
  :returns (m natp)
  :measure (len (acl2::integer-list-fix total))
  (b* ((rev-map (integer-integer-list-alist-fix rev-map))
       (total (acl2::integer-list-fix total))
       ((unless (consp total)) 0)
       ((cons total-hd total-tl) total)
       (exists? (assoc-equal total-hd rev-map))
       ((unless exists?) (number-of-unresolved-scc rev-map total-tl))
       (parents (cdr exists?))
       ((unless parents) (number-of-unresolved-scc rev-map total-tl)))
    (1+ (number-of-unresolved-scc rev-map total-tl)))
  ///
  (local (in-theory (enable number-of-unresolved-scc)))
  (local (defthm lemma-1
           (implies (and (integerp x)
                         (integer-listp klst)
                         (integer-integer-list-alistp alst)
                         (not (member-equal x klst)))
                    (equal (number-of-unresolved-scc (cons (list x) alst) klst)
                           (number-of-unresolved-scc alst klst)))))

  (local (defthm lemma-2
           (implies (and (integerp key)
                         (integer-listp klst)
                         (integer-integer-list-alistp alst)
                         (member-equal key klst)
                         (cdr (assoc-equal key alst)))
                    (< (number-of-unresolved-scc (cons (list key) alst) klst)
                       (number-of-unresolved-scc alst klst)))))

  (local (defthm lemma-3-*1/3
           (implies (and (not (member-equal key klst))
		                     (integerp key)
                         (integer-listp klst)
                         (integer-integer-list-alistp alst)
                         (integer-listp vars)
		                     (cdr (assoc-equal key alst)))
	                  (<= (number-of-unresolved-scc (cons (cons key vars) alst) klst)
		                    (number-of-unresolved-scc alst klst)))
           :hints(("Goal" :in-theory (disable integer-listp)))
           :rule-classes :linear))

  (local (defthm lemma-3
           (implies (and (integerp key)
                         (integer-listp klst)
                         (integer-integer-list-alistp alst)
                         (integer-listp vars)
                         (member-equal key klst)
                         (cdr (assoc-equal key alst)))
                    (<= (number-of-unresolved-scc (cons (cons key vars) alst) klst)
                        (number-of-unresolved-scc alst klst)))
           :hints (("Goal"
                    :in-theory (e/d (number-of-unresolved-scc)
                                    (integer-listp))))))

  (defthm assoc-equal-of-subsetp-equal-1
    (implies (and (integerp node)
                  (integer-integer-list-alistp rev-map)
                  (integer-listp total)
                  (cdr (assoc-equal node rev-map))
                  (subsetp-equal (strip-cars rev-map) total))
             (member-equal node total)))

  (defthm number-of-unresolved-scc-decreases-rev-map-1
    (implies (and (integerp node)
                  (integer-integer-list-alistp rev-map)
                  (integer-listp total)
                  (cdr (assoc-equal node rev-map))
                  (subsetp-equal (strip-cars rev-map) total))
             (< (number-of-unresolved-scc (cons (list node) rev-map) total)
                (number-of-unresolved-scc rev-map total)))
    :hints (("Goal"
             :in-theory (enable number-of-unresolved-scc)))
    :rule-classes :linear)

  (defthm number-of-unresolved-scc-decreases-rev-map-2
    (implies (and (integerp node)
                  (integer-integer-list-alistp rev-map)
                  (integer-listp total)
                  (integerp resolved)
                  (cdr (assoc-equal node rev-map))
                  (subsetp-equal (strip-cars rev-map) total))
             (<=
              (number-of-unresolved-scc
               (cons (cons node
                           (remove-equal resolved
                                         (cdr (assoc-equal node rev-map))))
                     rev-map)
               total)
              (number-of-unresolved-scc rev-map total)))
    :rule-classes :linear))

(defthm subsetp-equal-of-cdr
  (implies (subsetp-equal x (cdr y))
           (subsetp-equal x y)))

(defthm remove-equal-decreases-1
  (implies (remove-equal x lst)
           (<= (len (remove-equal x lst)) (len lst)))
  :rule-classes :linear)

(define update-work-lst-and-rev-map ((children integer-listp)
                                     (rev-map integer-integer-list-alistp)
                                     (work-lst integer-listp)
                                     (parent integerp))
  :returns (mv (new-rev-map integer-integer-list-alistp)
               (new-work-lst integer-listp))
  :measure (len children)
  (b* ((children (acl2::integer-list-fix children))
       (rev-map (integer-integer-list-alist-fix rev-map))
       (work-lst (acl2::integer-list-fix work-lst))
       (parent (ifix parent))
       ((unless (consp children)) (mv rev-map work-lst))
       ((cons child-hd child-tl) children)
       (exist? (assoc-equal child-hd rev-map))
       ((unless exist?)
        (update-work-lst-and-rev-map child-tl rev-map work-lst parent))
       (rev-nodes (cdr exist?))
       ((unless rev-nodes)
        (update-work-lst-and-rev-map child-tl rev-map work-lst parent))
       (new-nodes (remove-equal parent rev-nodes))
       ((unless new-nodes)
        (update-work-lst-and-rev-map child-tl (acons child-hd nil rev-map)
                                     (cons child-hd work-lst) parent)))
    (update-work-lst-and-rev-map child-tl (acons child-hd new-nodes rev-map)
                                 work-lst parent))
  ///
  (defthm subsetp-equal-of-rev-map-of-update
    (implies (and (integer-listp children)
                  (integer-integer-list-alistp rev-map)
                  (integer-listp work-lst)
                  (integer-listp total)
                  (integerp parent)
                  (subsetp-equal (strip-cars rev-map) total))
             (b* (((mv new-rev-map &)
                   (update-work-lst-and-rev-map children rev-map work-lst parent)))
               (subsetp-equal (strip-cars new-rev-map) total)))
    :hints (("Goal"
             :induct (update-work-lst-and-rev-map children rev-map work-lst parent))))

  (defthm update-rev-map-not-increase
    (implies (and (integer-listp children)
                  (integer-integer-list-alistp rev-map)
                  (integer-listp work-lst)
                  (integer-listp total)
                  (integerp parent)
                  (subsetp-equal (strip-cars rev-map) total))
             (b* (((mv new-rev-map &)
                   (update-work-lst-and-rev-map children rev-map work-lst parent)))
               (<= (number-of-unresolved-scc new-rev-map total)
                   (number-of-unresolved-scc rev-map total))))
    :hints (("Goal"
             :induct (update-work-lst-and-rev-map children rev-map work-lst parent)))
    :rule-classes :linear)

  (defthm update-rev-map-decrease
    (implies (and (integer-listp children)
                  (integer-integer-list-alistp rev-map)
                  (integer-listp work-lst)
                  (integer-listp total)
                  (integerp parent)
                  (subsetp-equal (strip-cars rev-map) total))
             (b* (((mv new-rev-map new-work)
                   (update-work-lst-and-rev-map children rev-map work-lst parent)))
               (implies (> (len new-work) (len work-lst))
                        (< (number-of-unresolved-scc new-rev-map total)
                           (number-of-unresolved-scc rev-map total)))))
    :hints (("Goal"
             :induct (update-work-lst-and-rev-map children rev-map work-lst parent)))
    :rule-classes :linear)
  )

(define measure-of-sort-scc-helper ((rev-map integer-integer-list-alistp)
                                    (total integer-listp)
                                    (work-lst integer-listp))
  :returns (m nat-listp)
  (b* ((rev-map (integer-integer-list-alist-fix rev-map))
       (work-lst (acl2::integer-list-fix work-lst)))
    (list (number-of-unresolved-scc rev-map total)
          (len work-lst))))

(define sort-scc-helper ((work-lst integer-listp)
                         (scc-map integer-integer-list-alistp)
                         (rev-map integer-integer-list-alistp)
                         (total integer-listp))
  :returns (order integer-listp)
  :guard (subsetp-equal (strip-cars rev-map) total)
  :verify-guards nil
  :measure (measure-of-sort-scc-helper (integer-integer-list-alist-fix rev-map)
                                       (acl2::integer-list-fix total)
                                       (acl2::integer-list-fix work-lst))
  :hints (("Goal"
           :in-theory (e/d (measure-of-sort-scc-helper) (update-rev-map-decrease))
           :use ((:instance update-rev-map-decrease
                            (children (cdr (assoc-equal (car (acl2::integer-list-fix work-lst))
                                                        (integer-integer-list-alist-fix scc-map))))
                            (rev-map (integer-integer-list-alist-fix rev-map))
                            (work-lst (cdr (acl2::integer-list-fix work-lst)))
                            (total (acl2::integer-list-fix total))
                            (parent (car (acl2::integer-list-fix work-lst)))))))
  :well-founded-relation l<
  (b* ((work-lst (acl2::integer-list-fix work-lst))
       (scc-map (integer-integer-list-alist-fix scc-map))
       (rev-map (integer-integer-list-alist-fix rev-map))
       (total (acl2::integer-list-fix total))
       ((unless (mbt (subsetp-equal (strip-cars rev-map) total))) nil)
       ((unless (consp work-lst)) nil)
       ((cons work-hd work-tl) work-lst)
       (exists? (assoc-equal work-hd scc-map))
       ((unless exists?)
        (cons work-hd (sort-scc-helper work-tl scc-map rev-map total)))
       ((mv new-rev-map new-work-lst)
        (update-work-lst-and-rev-map (cdr exists?) rev-map work-tl work-hd)))
    (cons work-hd (sort-scc-helper new-work-lst scc-map new-rev-map total))))

(verify-guards sort-scc-helper)

(defthm integer-listp-of-strip-cars-of-integer-integer-list-alistp
  (implies (integer-integer-list-alistp x)
           (integer-listp (strip-cars x))))

(defthm subset-equal-reflexivity
  (subsetp-equal x x)
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(define sort-scc ((scc-map integer-integer-list-alistp))
  :returns (order integer-listp)
  :guard-hints (("Goal" :in-theory (enable subsetp-equal)))
  (b* ((scc-map (integer-integer-list-alist-fix scc-map))
       (rev-map (get-reverse-map-top scc-map))
       (roots (get-root rev-map)))
    (sort-scc-helper roots scc-map rev-map (strip-cars rev-map))))

;; (sort-scc '((0 4) (4 7) (7) (8 7) (9)))

(define sum-low-helper ((id-alst symbol-integer-alistp)
                        (acc integer-symbol-list-alistp))
  :returns (new-acc integer-symbol-list-alistp)
  :measure (len (symbol-integer-alist-fix id-alst))
  (b* ((id-alst (symbol-integer-alist-fix id-alst))
       (acc (integer-symbol-list-alist-fix acc))
       ((unless (consp id-alst)) acc)
       ((cons id-hd id-tl) id-alst)
       ((cons sym id) id-hd)
       (sym-lst (cdr (assoc-equal id acc)))
       ((if (member-equal sym sym-lst))
        (sum-low-helper id-tl acc))
       (acc-1 (acons id (cons sym sym-lst) acc)))
    (sum-low-helper id-tl acc-1)))

(define sum-low ((id-alst symbol-integer-alistp))
  :returns (new-alst integer-symbol-list-alistp)
  (b* ((id-alst (symbol-integer-alist-fix id-alst)))
    (alist-clean (sum-low-helper id-alst nil) nil)))

(define find-and-sort-scc ((map symbol-symbol-list-alistp))
  :returns (mv (scc-alst integer-symbol-list-alistp)
               (order-lst integer-listp))
  (b* ((map (symbol-symbol-list-alist-fix map))
       (scc-args (scc-top map))
       (id-alst (process-scc-top map scc-args nil))
       (order-lst (sort-scc id-alst))
       (scc-alst (sum-low (alist-clean (scc-tarjan-args->low scc-args) nil))))
    (mv scc-alst (reverse order-lst))))

;; (find-and-sort-scc '((a . (b))
;;                      (b . (c))
;;                      (c . (d e))
;;                      (d . (a))
;;                      (e . (f))
;;                      (f . (g))
;;                      (g . (e h))
;;                      (h . ())
;;                      (i . (h))
;;                      (j . ())))
