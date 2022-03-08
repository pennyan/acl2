;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (12th Oct 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)

;; --------------------------------------
;; Returns theorems

(defthm return-of-symbolp
  (booleanp (symbolp x)))

(defthm return-of-booleanp
  (booleanp (booleanp x)))

(defthm return-of-integerp
  (booleanp (integerp x)))

(defthm return-of-rationalp
  (booleanp (rationalp x)))

(defthm return-of-ifix
  (integerp (ifix x)))

(defthm return-of-rfix
  (rationalp (rfix x)))

(defthm return-of-bool-fix
  (booleanp (bool-fix x)))

(defthm return-of-symbol-fix
  (symbolp (symbol-fix x)))

(defthm return-of-not
  (implies (booleanp x)
           (booleanp (not x))))

(defthm return-of-implies
  (implies (and (booleanp x)
                (booleanp y))
           (booleanp (implies x y))))

(defthmd return-of-equal-booleanp
  (implies (and (booleanp x) (booleanp y))
           (booleanp (equal x y))))

(defthmd return-of-equal-integerp
  (implies (and (integerp x) (integerp y))
           (booleanp (equal x y))))

(defthmd return-of-equal-rationalp
  (implies (and (rationalp x) (rationalp y))
           (booleanp (equal x y))))

(defthmd return-of-equal-symbolp
  (implies (and (symbolp x) (symbolp y))
           (booleanp (equal x y))))

(defthm return-of-<-rationalp
  (implies (and (rationalp x) (rationalp y))
           (booleanp (< x y))))

(defthm return-of-<-integerp
  (implies (and (integerp x) (integerp y))
           (booleanp (< x y))))

(defthm return-of-<-integerp-rationalp
  (implies (and (integerp x) (rationalp y))
           (booleanp (< x y))))

(defthm return-of-<-rationalp-integerp
  (implies (and (rationalp x) (integerp y))
           (booleanp (< x y))))

(defthm return-of-unary---integerp
  (implies (integerp x)
           (integerp (unary-- x))))

(defthm return-of-unary---rationalp
  (implies (rationalp x)
           (rationalp (unary-- x))))

(defthm return-of-unary-/-integerp
  (implies (integerp x)
           (rationalp (unary-/ x))))

(defthm return-of-unary-/-rationalp
  (implies (rationalp x)
           (rationalp (unary-/ x))))

(defthm return-of-binary-+-integerp
  (implies (and (integerp x)
                (integerp y))
           (integerp (binary-+ x y))))

(defthm return-of-binary-+-rationalp
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (binary-+ x y))))

(defthm return-of-binary-+-integerp-rationalp
  (implies (and (integerp x)
                (rationalp y))
           (rationalp (binary-+ x y))))

(defthm return-of-binary-+-rationalp-integerp
  (implies (and (rationalp x)
                (integerp y))
           (rationalp (binary-+ x y))))

(defthm return-of-binary-*-integerp
  (implies (and (integerp x)
                (integerp y))
           (integerp (binary-* x y))))

(defthm return-of-binary-*-rationalp
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (binary-* x y))))

(defthm return-of-binary-*-integerp-rationalp
  (implies (and (integerp x)
                (rationalp y))
           (rationalp (binary-* x y))))

(defthm return-of-binary-*-rationalp-integerp
  (implies (and (rationalp x)
                (integerp y))
           (rationalp (binary-* x y))))

;; --------------------------------------
;; Replace theorems

(defthm replace-of-ifix
  (implies (and (integerp x) (integerp (ifix x)))
           (equal (ifix x) x))
  :rule-classes nil)

(defthm replace-of-rfix
  (implies (and (rationalp x) (rationalp (rfix x)))
           (equal (rfix x) x))
  :rule-classes nil)

(defthm replace-of-symbol-fix
  (implies (and (symbolp x) (symbolp (symbol-fix x)))
           (equal (symbol-fix x) x))
  :rule-classes nil)

(defthm replace-of-bool-fix
  (implies (and (booleanp x) (booleanp (bool-fix x)))
           (equal (bool-fix x) x))
  :rule-classes nil)

;; --------------------------------------
;; Supertype theorems

(defthm integerp-is-rationalp
  (implies (integerp x) (rationalp x)))
