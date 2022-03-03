;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 25th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;
(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

;; easy-fix is a macro for defining a fty::deffixtype when we've got a
;;   recognizer function and a default value.
(defun easy-fix-fn (type-name default-value)
  (b* ((type-str (symbol-name type-name))
       (type-pred (intern-in-package-of-symbol (concatenate 'string type-str "-P") type-name))
       (type-fix (intern-in-package-of-symbol (concatenate 'string type-str "-FIX") type-name))
       (type-fix-lemma (intern-in-package-of-symbol (concatenate 'string type-str "-FIX-WHEN-" type-str "-P") type-name))
       (type-equiv (intern-in-package-of-symbol (concatenate 'string type-str "-EQUIV") type-name)))
    `(defsection ,type-name
       (define ,type-fix ((x ,type-pred))
         :returns(fix-x ,type-pred)
         (mbe :logic (if (,type-pred x) x ,default-value)
              :exec  x)
         ///
         (more-returns
          (fix-x (implies (,type-pred x) (equal fix-x x))
                 :hints(("Goal" :in-theory (enable ,type-fix)))
                 :name ,type-fix-lemma)))
       (deffixtype ,type-name
         :pred   ,type-pred
         :fix    ,type-fix
         :equiv  ,type-equiv
         :define t
         :topic  ,type-name))))

(defmacro easy-fix (type-name default-value)
  `(make-event (easy-fix-fn ',type-name ',default-value)))

(define true-list-fix ((lst true-listp))
  :parents (SMT-hint-interface)
  :short "Fixing function for true-listp."
  :returns (fixed-lst true-listp)
  (mbe :logic (if (consp lst)
                  (cons (car lst)
                        (true-list-fix (cdr lst)))
                nil)
       :exec lst))

(defthm true-list-fix-idempotent-lemma
  (equal (true-list-fix (true-list-fix x))
         (true-list-fix x))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm true-list-fix-preserve-length
  (equal (len (true-list-fix x))
         (len x))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm true-list-fix-when-true-listp
  (implies (true-listp x)
           (equal (true-list-fix x) x))
  :hints (("Goal" :in-theory (enable true-listp true-list-fix))))

(deffixtype true-list
  :fix true-list-fix
  :pred true-listp
  :equiv true-list-equiv
  :define t
  :forward t
  :topic true-listp)

(define string-list-fix ((lst string-listp))
  :parents (SMT-hint-interface)
  :short "Fixing function for string-listp."
  :returns (fixed-lst string-listp)
  (mbe :logic (if (string-listp lst) lst nil)
       :exec lst))

(defthm string-list-fix-idempotent-lemma
  (equal (string-list-fix (string-list-fix x))
         (string-list-fix x))
  :hints (("Goal" :in-theory (enable string-list-fix))))

(deffixtype string-list
  :fix string-list-fix
  :pred string-listp
  :equiv string-list-equiv
  :define t
  :forward t
  :topic string-listp)

(defalist symbol-symbol-alist
  :key-type symbolp
  :val-type symbolp
  :pred symbol-symbol-alistp
  :true-listp t)

(defthm cdr-of-symbol-symbol-alistp
  (implies (symbol-symbol-alistp x)
           (symbol-symbol-alistp (cdr x))))

(defthm strip-cars-of-symbol-symbol-alistp
  (implies (symbol-symbol-alistp x)
           (symbol-listp (strip-cars x)))
  :hints (("Goal" :in-theory (enable strip-cars))))

(defthm strip-cdrs-of-symbol-symbol-alistp
  (implies (symbol-symbol-alistp x)
           (symbol-listp (strip-cdrs x)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(deflist symbol-list-list
  :elt-type symbol-listp
  :pred symbol-list-listp
  :true-listp t)

(define symbol-alist-fix ((x symbol-alistp))
  :returns (fix-x symbol-alistp)
  (mbe :logic (if (symbol-alistp x) x nil)
       :exec x)
  ///
  (more-returns
   (fix-x (implies (symbol-alistp x) (equal fix-x x))
          :name symbol-alist-fix-when-symbol-alistp)))

(deffixtype symbol-alist
  :pred symbol-alistp
  :fix symbol-alist-fix
  :equiv symbol-alist-equiv
  :define t
  :topic symbol-alist)

(local
 (defthm symbol-alistp-of-pairlis$-of-symbol-listp
   (implies (symbol-listp x)
            (symbol-alistp (pairlis$ x y)))
   :hints (("Goal" :in-theory (enable symbol-alistp pairlis$))))
 )

(defalist symbol-symbol-list-alist
  :key-type symbolp
  :val-type symbol-listp
  :true-listp t
  :pred symbol-symbol-list-alistp)

(defthm assoc-equal-of-symbol-symbol-list-alistp-1
  (implies (symbol-symbol-list-alistp x)
           (symbol-listp (cdr (assoc-equal y x)))))

(defthm assoc-equal-of-symbol-symbol-list-alistp-2
  (implies (and (symbol-symbol-list-alistp x)
                (assoc-equal y x))
           (consp (assoc-equal y x))))

(defalist symbol-integer-alist
  :key-type symbolp
  :val-type integerp
  :true-listp t
  :pred symbol-integer-alistp)

(defthm assoc-equal-of-symbol-integer-alistp
  (implies (and (symbol-integer-alistp x)
                (assoc-equal y x))
           (and (consp (assoc-equal y x))
                (integerp (cdr (assoc-equal y x))))))

(defalist symbol-boolean-alist
  :key-type symbolp
  :val-type booleanp
  :true-listp t
  :pred symbol-boolean-alistp)

(defthm assoc-equal-of-symbol-boolean-alistp
  (implies (and (symbol-boolean-alistp x)
                (assoc-equal y x))
           (and (consp (assoc-equal y x))
                (booleanp (cdr (assoc-equal y x))))))

(defalist integer-integer-list-alist
  :key-type integerp
  :val-type integer-listp
  :true-listp t
  :pred integer-integer-list-alistp)

(defthm assoc-equal-of-integer-integer-alistp-1
  (implies (integer-integer-list-alistp x)
           (and (true-listp (cdr (assoc-equal y x)))
                (integer-listp (cdr (assoc-equal y x))))))

(defthm assoc-equal-of-integer-integer-alistp-2
  (implies (and (integer-integer-list-alistp x)
                (assoc-equal y x))
           (consp (assoc-equal y x))))

(defalist integer-symbol-list-alist
  :key-type integerp
  :val-type symbol-listp
  :true-listp t
  :pred integer-symbol-list-alistp)

(defoption maybe-integer integerp :pred maybe-integerp)

(deflist maybe-integer-list
  :elt-type maybe-integerp
  :pred maybe-integer-listp
  :true-listp t)

(defthm alistp-of-pairlis$
  (alistp (acl2::pairlis$ a b)))
