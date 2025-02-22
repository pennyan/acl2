;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2


(in-package "SMT")
(include-book "../top")
(include-book "centaur/sv/tutorial/support" :dir :system)
;; def-saved-event is a wrapper that is used by the documentation system,
;; and can be ignored by the reader.
;; Check the book centaur/sv/tutorial/support.lisp for detailed explanation.
;; (include-book "basictypes")

; cert_param: (uses-smtlink)

(value-triple (tshell-ensure))
(add-default-hints '((SMT::SMT-computed-hint clause)))

(defthm test1
  (implies (and (integerp x) (rationalp y))
           (>= (binary-+ (binary-* (ifix x) y) (binary-* x y))
               (binary-* 2 (binary-* x (rfix y)))))
  :hints(("Goal" :smtlink nil)))

(acl2::must-fail
(defthm test2
  (implies (and (symbolp symx) (symbolp symy))
           (or (equal symx 'symx) (equal symx 'sym2)
               (equal symx 'sym3)
               (equal symy 'symx) (equal symy 'sym2)
               (equal symy 'sym3)
               (equal symx symy)))
  :hints(("Goal" :smtlink nil)))
)

(define foo ((a rationalp)
             (b rationalp))
  :returns (r rationalp)
  (b* ((a (rfix a))
       (b (rfix b)))
    (+ (* a a) (* b b)))
  ///
  (more-returns
   (r (>= r 0)
      :name foo->=-0))
  (defthm integerp-of-foo
    (implies (and (integerp a) (integerp b))
             (integerp (foo a b)))
    :hints (("Goal"
             :in-theory (enable foo)))))

(defthm test3
  (implies (and (integerp x)
                (integerp y))
           (> (1+ (foo x y)) 0))
  :hints (("Goal"
           :smtlink
           (:functions ((foo :return ((:thm rationalp-of-foo
                                       :formals (a b)))))
            :hypotheses ((:instance foo->=-0
                                    ((a x) (b y))))))))

(define foo-int-int-rat ((a integerp)
                         (b integerp))
  :returns (r rationalp)
  (foo (ifix a) (ifix b))
  ///
  (more-returns
   (r (implies (and (integerp a) (integerp b) (rationalp (foo a b)))
               (equal (foo a b) r))
      :name replace-of-foo-int-int-rat)))

(define foo-int-int-int ((a integerp)
                         (b integerp))
  :returns (r integerp)
  (foo (ifix a) (ifix b))
  ///
  (more-returns
   (r (implies (and (integerp a) (integerp b) (integerp (foo a b)))
               (equal (foo a b) r))
      :name replace-of-foo-int-int-int)))

(define bar ((x rationalp) (y integerp))
  :returns (r)
  (+ (rfix x) (ifix y))
  ///
  (more-returns
   (r (if (and (>= x 0) (>= y 0)) (>= r 0) 't)
      :name bar->=-0)
   (r (implies (and (rationalp x) (integerp y)) (rationalp r))
      :name rationalp-of-bar)))

(defthm test4
  (implies (and (integerp x) (integerp y))
           (>= (bar (foo x y) (foo x y)) 0))
  :hints (("Goal"
           :smtlink
           (:functions ((foo :return ((:thm rationalp-of-foo
                                       :formals (a b))
                                      (:thm integerp-of-foo
                                       :formals (a b))))
                        (foo-int-int-rat :return ((:thm rationalp-of-foo-int-int-rat
                                                        :formals (a b))))
                        (foo-int-int-int :return ((:thm integerp-of-foo-int-int-int
                                                   :formals (a b))))
                        (bar :return ((:thm rationalp-of-bar
                                       :formals (x y)))))
            :replaces ((:thm replace-of-foo-int-int-rat)
                       (:thm replace-of-foo-int-int-int))
            :hypotheses ((:instance foo->=-0
                                    ((a x) (b y)))
                         (:instance bar->=-0
                                    ((x (foo x y))
                                     (y (foo x y)))))))))

(defprod animal
  ((furry booleanp)
   (size integerp)
   (category symbolp)))

(defthm booleanp-of-animal-p
  (booleanp (animal-p x)))

(defthm replace-of-animal-fix
  (implies (animal-p x)
           (equal (animal-fix x) x)))

(defthm return-of-animal
  (implies (and (booleanp x)
                (integerp y)
                (symbolp z))
           (animal-p (animal x y z))))

(defthm return-of-animal->furry
  (implies (animal-p x)
           (booleanp (animal->furry x))))

(defthm return-of-animal->size
  (implies (animal-p x)
           (integerp (animal->size x))))

(defthm return-of-animal->category
  (implies (animal-p x)
           (symbolp (animal->category x))))

(defthm test5
  (implies (and (animal-p x) (animal-p y)
                (animal->furry x))
           (>= (+ (* (animal->size x) (animal->size x))
                  (* (animal->size y) (animal->size y)))
               0))
  :hints (("Goal"
           :smtlink
           (:functions ((animal-p
                         :return ((:thm booleanp-of-animal-p :formals (x))))
                        (animal-fix$inline
                         :return ((:thm animal-p-of-animal-fix :formals (x))))
                        (animal
                         :return ((:thm return-of-animal :formals (x y z))))
                        (animal->furry$inline
                         :return ((:thm return-of-animal->furry :formals (x))))
                        (animal->size$inline
                         :return ((:thm return-of-animal->size :formals (x))))
                        (animal->category$inline
                         :return ((:thm return-of-animal->category :formals (x)))))
            :acl2types ((animal-p))
            :datatypes (:sumtypes ((animal-p
                                    :recognizer (animal-p :translation "Animal"
                                                          :return-type booleanp)
                                    :sums
                                    ((:constructor (animal :translation "animal"
                                                           :return-type animal-p)
                                      :destructors ((animal->furry$inline
                                                     :translation "furry"
                                                     :return-type booleanp)
                                                    (animal->size$inline
                                                     :translation "size"
                                                     :return-type integerp)
                                                    (animal->category$inline
                                                     :translation "category"
                                                     :return-type symbolp))))
                                    :property-hints
                                    ((uniqueness-of-animal-p-constructor-of-destructors)
                                     (destructors-of-animal)
                                     (type-of-animal-destructors)
                                     (type-of-animal)
                                     (type-of-animal-p)))))
            :replaces ((:thm replace-of-animal-fix))))))

(deflist integer-list
  :elt-type integerp
  :true-listp t)

(defthmd return-of-cons-for-integer-list
  (implies (and (integerp x) (integer-list-p y))
           (integer-list-p (cons x y))))

(defthmd return-of-car-for-integer-list
  (implies (and (integer-list-p x) (not (equal x nil)))
           (integerp (car x))))

(defthmd return-of-cdr-for-integer-list
  (implies (integer-list-p x)
           (integer-list-p (cdr x))))

(define integer-list->cons ((x integerp)
                            (y integer-list-p))
  (cons (ifix x) (integer-list-fix y))
  ///
  (defthmd return-of-integer-list->cons
    (implies (and (integerp x) (integer-list-p y))
             (integer-list-p (integer-list->cons x y))))

  (defthmd replace-of-integer-list->cons
    (implies (and (integerp x) (integer-list-p y))
             (equal (cons x y)
                    (integer-list->cons x y)))))

(define integer-list->nil ()
  nil
  ///
  (defthmd return-of-integer-list->nil
    (integer-list-p (integer-list->nil)))

  (defthm replace-of-integer-list->nil
    (implies (integer-list-p nil)
             (equal nil (integer-list->nil)))
    :rule-classes nil))

(define integer-list->car ((x integer-list-p))
  (if (consp x) (car x) (ifix (car x)))
  ///
  (defthmd return-of-integer-list->car
    (implies (integer-list-p x)
             (integerp (integer-list->car x))))

  ;; It needs to be integer-list->nil
  (defthmd replace-of-integer-list->car
    (implies (and (integer-list-p x)
                  (not (equal x (integer-list->nil))))
             (equal (car x) (integer-list->car x)))))

(define integer-list->cdr ((x integer-list-p))
  (cdr x)
  ///
  (defthmd return-of-integer-list->cdr
    (implies (integer-list-p x)
             (integer-list-p (integer-list->cdr x))))

  (defthmd replace-of-integer-list->cdr
    (implies (integer-list-p x)
             (equal (cdr x)
                    (integer-list->cdr x)))))

(defthmd booleanp-of-integer-list-p
  (booleanp (integer-list-p x)))

(defthmd return-of-equal-for-integer-list
  (implies (and (integer-list-p x)
                (integer-list-p y))
           (booleanp (equal x y))))

(defthm integer-list-cons-car-cdr
  (implies (and (integer-list-p x)
                (not (equal x (integer-list->nil))))
           (equal (integer-list->cons (integer-list->car x)
                                      (integer-list->cdr x))
                  x))
  :hints (("Goal"
           :in-theory (enable integer-list->nil
                              integer-list->cons
                              integer-list->car
                              integer-list->cdr))))

(defthm integer-list-car-cdr-cons
  (implies (and (integerp x) (integer-list-p y))
           (and (equal (integer-list->car (integer-list->cons x y)) x)
                (equal (integer-list->cdr (integer-list->cons x y)) y)))
  :hints (("Goal"
           :in-theory (enable integer-list->cons
                              integer-list->car
                              integer-list->cdr))))

(defthm test6
  (implies (and (integer-list-p x) (integer-list-p y)
                (not (equal x nil)))
           (equal (cons (car x) nil) (cons (car x) nil)))
  :rule-classes nil
  :hints (("Goal"
           :smtlink
           (:functions ((cons
                         :return ((:thm return-of-cons-for-integer-list
                                   :formals (x y))))
                        (car
                         :return ((:thm return-of-car-for-integer-list
                                   :formals (x))))
                        (cdr
                         :return ((:thm return-of-cdr-for-integer-list
                                   :formals (x))))
                        (equal
                         :kind :basic
                         :translation "_SMT_.equal"
                         :return ((:thm return-of-equal-for-integer-list
                                        :formals (x y))))
                        (integer-list-p
                         :return ((:thm booleanp-of-integer-list-p
                                        :formals (x)))))
            :acl2types ((integer-list-p))
            :datatypes (:sumtypes ((integer-list-p
                                    :recognizer (integer-list-p :translation "IntegerList")
                                    :sums
                                    ((:constructor (integer-list->cons
                                                    :translation "cons"
                                                    :return-type integer-list-p)
                                      :destructors ((integer-list->car
                                                     :translation "car"
                                                     :return-type integerp)
                                                    (integer-list->cdr
                                                     :translation "cdr"
                                                     :return-type integer-list-p)))
                                     (:constructor (integer-list->nil
                                                    :fn-to-const t
                                                    :translation "nil"
                                                    :return-type integer-list-p)
                                                   :destructors nil))
                                    :property-hints
                                    ((uniqueness-of-integer-list-p-constructor-of-destructors)
                                     (type-of-integer-list->nil)
                                     (destructors-of-integer-list->cons)
                                     (type-of-integer-list->cons-destructors)
                                     (type-of-integer-list->cons)
                                     (type-of-integer-list-p)))))
            :replaces ((:thm replace-of-integer-list->cons)
                       (:thm replace-of-integer-list->car)
                       (:thm replace-of-integer-list->cdr)
                       (:thm replace-of-integer-list->nil))))))

(defun x^2-y^2 (x y) (- (* x x) (* y y)))

(defthm test61
  (implies (and (integer-list-p x) (rationalp y)
                (not (equal x nil)))
           (implies (and (<= (+ (* (/ 9 8) (car x) (car x)) (* y y)) 1)
                         (<=  (x^2-y^2 (car x) y) 1))
                    (< y (- (* 3 (- (car x) (/ 17 8)) (- (car x) (/ 17 8))) 3))))
  :hints (("Goal"
           :smtlink
           (:functions ((cons
                         :return ((:thm return-of-cons-for-integer-list
                                   :formals (x y))))
                        (car
                         :return ((:thm return-of-car-for-integer-list
                                   :formals (x))))
                        (cdr
                         :return ((:thm return-of-cdr-for-integer-list
                                   :formals (x))))
                        (equal
                         :kind :basic
                         :translation "_SMT_.equal"
                         :return ((:thm return-of-equal-for-integer-list
                                        :formals (x y))))
                        (integer-list-p
                         :return ((:thm booleanp-of-integer-list-p
                                        :formals (x)))))
            :acl2types ((integer-list-p))
            :datatypes (:sumtypes ((integer-list-p
                                    :recognizer (integer-list-p :translation "IntegerList")
                                    :sums
                                    ((:constructor (integer-list->cons
                                                    :translation "cons"
                                                    :return-type integer-list-p)
                                      :destructors ((integer-list->car
                                                     :translation "car"
                                                     :return-type integerp)
                                                    (integer-list->cdr
                                                     :translation "cdr"
                                                     :return-type integer-list-p)))
                                     (:constructor (integer-list->nil
                                                    :fn-to-const t
                                                    :translation "nil"
                                                    :return-type integer-list-p)
                                                   :destructors nil))
                                    :property-hints
                                    ((uniqueness-of-integer-list-p-constructor-of-destructors)
                                     (type-of-integer-list->nil)
                                     (destructors-of-integer-list->cons)
                                     (type-of-integer-list->cons-destructors)
                                     (type-of-integer-list->cons)
                                     (type-of-integer-list-p)))))
            :replaces ((:thm replace-of-integer-list->cons)
                       (:thm replace-of-integer-list->car)
                       (:thm replace-of-integer-list->cdr)
                       (:thm replace-of-integer-list->nil))))))

(defoption maybe-rational rationalp)

(defthmd booleanp-of-maybe-rational-p
  (booleanp (maybe-rational-p x)))

(define maybe-rational-nil ()
  nil
  ///
  (defthmd return-of-maybe-rational-nil
    (maybe-rational-p (maybe-rational-nil)))

  (defthm replace-of-maybe-rational-nil
    (implies (maybe-rational-p nil)
             (equal nil (maybe-rational-nil)))
    :rule-classes nil))

(defthmd return-of-maybe-rational-some
  (implies (rationalp x)
           (maybe-rational-p (maybe-rational-some x))))

(defthmd return-of-maybe-rational-some->val
  (implies (maybe-rational-p x)
           (rationalp (maybe-rational-some->val$inline x))))

(defthmd maybe-rational-p-canbe-rationalp
  (implies (and (maybe-rational-p x) (not (equal x nil)))
           (rationalp x)))

(defthmd maybe-rational-p-canbe-rationalp
  (implies (and (maybe-rational-p x) (not (equal x nil)))
           (rationalp x)))

(defthmd return-of-equal-for-maybe-rational-p
  (implies (and (maybe-rational-p x)
                (maybe-rational-p y))
           (booleanp (equal x y))))

(defthm test7
  (implies (and (maybe-rational-p x) (not (equal x nil)))
           (>= (* (maybe-rational-some->val x)
                  (maybe-rational-some->val x))
               0))
  :hints (("Goal"
           :smtlink
           (:functions ((equal
                         :kind :basic
                         :translation "_SMT_.equal"
                         :return ((:thm return-of-equal-for-maybe-rational-p
                                        :formals (x y))))
                        (maybe-rational-p
                         :return ((:thm booleanp-of-maybe-rational-p
                                        :formals (x))))
                        (maybe-rational-fix$inline
                         :return ((:thm maybe-rational-p-of-maybe-rational-fix
                                        :formals (x))))
                        (maybe-rational-some
                         :return ((:thm return-of-maybe-rational-some
                                        :formals (x))))
                        (maybe-rational-some->val$inline
                         :return ((:thm return-of-maybe-rational-some->val
                                        :formals (x))))
                        (maybe-rational-nil
                         :return ((:thm return-of-maybe-rational-nil))))
            :acl2types ((maybe-rational-p
                         :subtypes ((rationalp
                                     :thm (:thm maybe-rational-p-canbe-rationalp
                                                :formals (x))))))
            :datatypes (:sumtypes ((maybe-rational-p
                                    :recognizer (maybe-rational-p
                                                 :translation "MaybeRational"
                                                 :return-type booleanp)
                                    :sums
                                    ((:constructor (maybe-rational-some
                                                    :translation "some"
                                                    :return-type maybe-rational-p)
                                      :destructors ((maybe-rational-some->val$inline
                                                     :translation "val"
                                                     :return-type rationalp)))
                                     (:constructor (maybe-rational-nil
                                                    :translation "nil"
                                                    :return-type maybe-rational-p
                                                    :fn-to-const t)))
                                    :property-hints
                                    ((uniqueness-of-maybe-rational-p-constructor-of-destructors)
                                     (type-of-maybe-rational-nil)
                                     (destructors-of-maybe-rational-some)
                                     (type-of-maybe-rational-some-destructors)
                                     (type-of-maybe-rational-some)
                                     (type-of-maybe-rational-p)))))
            :replaces ((:thm replace-of-maybe-rational-nil))))))

(deftagsum food
  (:sandwich ((layer integerp)))
  (:dumpling ((flavor symbolp)
              (size integerp))))

(defthmd return-of-equal-for-food-p
  (implies (and (food-p x) (food-p y))
           (booleanp (equal x y))))

(defthmd return-of-equal-for-symbolp
  (implies (and (symbolp x) (symbolp y))
           (booleanp (equal x y))))

(defthmd booleanp-of-food-p
  (booleanp (food-p x)))

(defthmd symbolp-of-food-kind
  (implies (food-p x)
           (symbolp (food-kind$inline x))))

(defthmd return-of-food-sandwich
  (implies (integerp x)
           (food-p (food-sandwich x))))

(defthmd return-of-food-sandwich->layer
  (implies (and (food-p x)
                (equal (food-kind$inline x) :sandwich))
           (integerp (food-sandwich->layer$inline x))))

(defthmd return-of-food-dumpling
  (implies (and (symbolp x)
                (integerp y))
           (food-p (food-dumpling x y))))

(defthmd return-of-food-dumpling->flavor
  (implies (and (food-p x)
                (equal (food-kind$inline x) :dumpling))
           (symbolp (food-dumpling->flavor$inline x))))

(defthmd return-of-food-dumpling->size
  (implies (and (food-p x)
                (equal (food-kind$inline x) :dumpling))
           (integerp (food-dumpling->size$inline x))))

(defthm test8
  (implies (and (food-p x) (food-p y)
                (equal (food-kind x) :sandwich)
                (equal (food-kind y) :dumpling))
           (>= (+ (* (food-sandwich->layer x) (food-sandwich->layer x))
                  (* (food-dumpling->size y) (food-dumpling->size y)))
               0))
  :hints (("Goal"
           :smtlink
           (:functions ((equal
                         :kind :basic
                         :translation "_SMT_.equal"
                         :return ((:thm return-of-equal-for-food-p
                                   :formals (x y))
                                  (:thm return-of-equal-for-symbolp
                                        :formals (x y))))
                        (food-kind$inline
                         :return ((:thm symbolp-of-food-kind :formals (x))))
                        (food-p
                         :return ((:thm booleanp-of-food-p :formals (x))))
                        (food-sandwich
                         :return ((:thm return-of-food-sandwich :formals (x))))
                        (food-sandwich->layer$inline
                         :return ((:thm return-of-food-sandwich->layer
                                        :formals (x))))
                        (food-dumpling
                         :return ((:thm return-of-food-dumpling
                                        :formals (x y))))
                        (food-dumpling->flavor$inline
                         :return ((:thm return-of-food-dumpling->flavor
                                        :formals (x))))
                        (food-dumpling->size$inline
                         :return ((:thm return-of-food-dumpling->size
                                        :formals (x))))
                        (food-fix$inline
                         :return ((:thm food-p-of-food-fix
                                        :formals (x)))))
            :acl2types ((food-p))
            :datatypes (:sumtypes ((food-p
                                    :kind (food-kind$inline :translation "FoodKind"
                                                            :return-type symbolp)
                                    :recognizer (food-p :translation "food"
                                                        :return-type booleanp)
                                    :sums
                                    ((:tag :sandwich
                                      :constructor (food-sandwich :translation "sandwich"
                                                                  :return-type food-p)
                                      :destructors ((food-sandwich->layer$inline
                                                     :translation "layer"
                                                     :return-type integerp)))
                                     (:tag :dumpling
                                      :constructor (food-dumpling :translation "dumpling"
                                                                  :return-type food-p)
                                      :destructors ((food-dumpling->flavor$inline
                                                     :translation "flavor"
                                                     :return-type symbolp)
                                                    (food-dumpling->size$inline
                                                     :translation "size"
                                                     :return-type integerp))))
                                    :property-hints ((type-of-food-p-equal)
                                                     (reflexivity-of-food-p-equal)
                                                     (symmetricity-of-food-p-equal)
                                                     (transitivity-of-food-p-equal)
                                                     (tag-uniqueness-of-food-p)
                                                     (uniqueness-of-food-p-constructor-of-destructors)
                                                     (tag-of-food-dumpling)
                                                     (food-dumpling-of-destructors)
                                                     (destructors-of-food-dumpling)
                                                     (type-of-food-dumpling-destructors)
                                                     (type-of-food-dumpling)
                                                     (tag-of-food-sandwich)
                                                     (food-sandwich-of-destructors)
                                                     (destructors-of-food-sandwich)
                                                     (type-of-food-sandwich-destructors)
                                                     (type-of-food-sandwich)
                                                     (type-of-food-p)))))))))

(defalist-smt symbol-integer-alist-p symbolp symbol-fix integerp ifix)

(defthm crock1
  (implies (symbol-integer-array-p x)
           (symbol-integer-array-equal x x))
  :hints (("Goal"
           :in-theory (enable reflexivity-of-symbol-integer-array-equal))))

(defthm crock2
  (implies (and (symbol-integer-array-p x) (symbol-integer-array-p y)
                (symbol-integer-array-equal x y))
           (symbol-integer-array-equal y x))
  :hints (("Goal"
           :in-theory (enable symmetricity-of-symbol-integer-array-equal))))

(defthm crock3
  (implies (and (symbol-integer-array-p x) (symbol-integer-array-p y)
                (symbol-integer-array-p z) (symbol-integer-array-equal x y)
                (symbol-integer-array-equal y z))
           (symbol-integer-array-equal x z))
  :hints (("Goal"
           :in-theory (enable transitivity-of-symbol-integer-array-equal))))

(defthm test9
  (implies (and (symbol-integer-alist-p x) (symbolp y)
                (not (equal (assoc-equal y x) nil)))
           (>= (* (cdr (assoc-equal y x))
                  (cdr (assoc-equal y x)))
               0))
  :hints (("Goal"
           :smtlink
           (:functions ((assoc-equal
                         :return ((:thm maybe-symbol-integer-consp-of-assoc-equal-of-symbol-integer-alist-p
                                   :formals (k x))))
                        (cdr
                         :return ((:thm integerp-of-cdr-of-symbol-integer-consp
                                        :formals (x))
                                  (:thm integerp-of-cdr-of-maybe-symbol-integer-consp
                                        :formals (x))))
                        (equal
                         :kind :basic
                         :translation "_SMT_.equal"
                         :return ((:thm booleanp-of-equal-of-maybe-symbol-integer-consp
                                        :formals (x y))))
                        (symbol-integer-alist-p
                         :return ((:thm booleanp-of-symbol-integer-alist-p
                                        :formals (x))))
                        (symbol-integer-consp
                         :return ((:thm booleanp-of-symbol-integer-consp
                                        :formals (x))))
                        (maybe-symbol-integer-consp
                         :return ((:thm booleanp-of-maybe-symbol-integer-consp
                                        :formals (x)))))
            :acl2types ((maybe-symbol-integer-consp
                         :subtypes ((symbol-integer-consp
                                     :thm (:thm maybe-symbol-integer-consp-canbe-symbol-integer-consp
                                                :formals (x)))))
                        (symbol-integer-alist-p)
                        (symbol-integer-consp)
                        (symbol-integer-array-equiv-consp)
                        (symbol-integer-array-p))
            :datatypes (:sumtypes ((maybe-symbol-integer-consp
                                    :recognizer
                                    (maybe-symbol-integer-consp :translation "MaybeSymbolIntegerCons")
                                    :sums
                                    ((:constructor (maybe-symbol-integer-cons->cons
                                                    :translation "cons"
                                                    :return-type maybe-symbol-integer-consp)
                                      :destructors ((maybe-symbol-integer-cons->car
                                                     :translation "car"
                                                     :return-type symbolp)
                                                    (maybe-symbol-integer-cons->cdr
                                                     :translation "cdr"
                                                     :return-type integerp)))
                                     (:constructor (maybe-symbol-integer-cons->nil
                                                    :fn-to-const t
                                                    :translation "nil"
                                                    :return-type maybe-symbol-integer-consp)
                                                   :destructors nil))
                                    :property-hints
                                    ((uniqueness-of-maybe-symbol-integer-consp-constructor-of-destructors)
                                     (type-of-maybe-symbol-integer-cons->nil)
                                     (destructors-of-maybe-symbol-integer-cons->cons)
                                     (type-of-maybe-symbol-integer-cons->cons-destructors)
                                     (type-of-maybe-symbol-integer-cons->cons)
                                     (type-of-maybe-symbol-integer-consp))))
                        :arrays ((symbol-integer-array-p
                                  :recognizer (symbol-integer-array-p
                                               :translation "SymbolIntegerArray")
                                  :key-type symbolp
                                  :val-type maybe-symbol-integer-consp
                                  :init (:fn (symbol-integer-array-init
                                              :translation
                                              "symbolIntegerArrayInit")
                                         :val maybe-symbol-integer-cons->nil)
                                  :select (symbol-integer-array-select)
                                  :store (symbol-integer-array-store)
                                  :equal (symbol-integer-array-equal)
                                  :equal-witness
                                  (symbol-integer-array-equal-witness)
                                  :property-hints
                                  ((type-of-symbol-integer-array-p-equal)
                                   (reflexivity-of-symbol-integer-array-p-equal)
                                   (symmetricity-of-symbol-integer-array-p-equal)
                                   (transitivity-of-symbol-integer-array-p-equal)
                                   (symbol-integer-array-p-equal-implies-select-equal
                                    . (:use ((:instance
                                              symbol-integer-array-equal-implies-select-equal))))
                                   (select-of-witness-equal-implies-symbol-integer-array-p-equal
                                    . (:use ((:instance
                                              select-of-witness-equal-implies-symbol-integer-array-equal))))
                                   (type-of-symbol-integer-array-p-store)
                                   (symbol-integer-array-p-select-distinct
                                    . (:in-theory (enable symbol-integer-array-select-of-symbol-integer-array-store)))
                                   (symbol-integer-array-p-select-equal
                                    . (:in-theory (enable
                                                   symbol-integer-array-select-of-symbol-integer-array-store)))
                                   (type-of-symbol-integer-array-p-select)
                                   (type-of-symbol-integer-array-p-init)
                                   (equal-of-symbol-integer-array-p-init
                                    . (:in-theory (enable
                                                   symbol-integer-array-select-of-symbol-integer-array-init)))
                                   (type-of-symbol-integer-array-p)))))
            :replaces ((:thm
                        symbol-integer-array-translation-of-assoc-equal)
                       (:thm symbol-integer-array-translation-of-acons)
                       (:thm symbol-integer-array-translation-of-alist)
                       (:thm symbol-integer-array-translation-of-nil)
                       (:thm
                        replace-of-cdr-of-symbol-integer-consp)
                       (:thm replace-of-maybe-symbol-integer-cons->nil))
            ))))

(defthm test10
  (implies (and (symbolp k) (integerp v) (symbolp x)
                (not (equal (assoc-equal x (acons k v nil)) nil)))
           (>= (* (cdr (assoc-equal x (acons k v nil)))
                  (cdr (assoc-equal x (acons k v nil))))
               0))
  :hints (("Goal"
           :smtlink
           (:functions ((assoc-equal
                         :return ((:thm maybe-symbol-integer-consp-of-assoc-equal-of-symbol-integer-alist-p
                                        :formals (k x))))
                        (acons
                         :return ((:thm symbol-integer-alist-p-of-acons
                                        :formals (k v x))))
                        (cdr
                         :return ((:thm integerp-of-cdr-of-symbol-integer-consp
                                        :formals (x))
                                  (:thm integerp-of-cdr-of-maybe-symbol-integer-consp
                                        :formals (x))))
                        (equal
                         :kind :basic
                         :translation "_SMT_.equal"
                         :return ((:thm booleanp-of-equal-of-maybe-symbol-integer-consp
                                        :formals (x y))))
                        (symbol-integer-alist-p
                         :return ((:thm booleanp-of-symbol-integer-alist-p
                                        :formals (x))))
                        (symbol-integer-consp
                         :return ((:thm booleanp-of-symbol-integer-consp
                                        :formals (x))))
                        (maybe-symbol-integer-consp
                         :return ((:thm booleanp-of-maybe-symbol-integer-consp
                                        :formals (x)))))
            :acl2types ((maybe-symbol-integer-consp
                         :subtypes ((symbol-integer-consp
                                     :thm (:thm maybe-symbol-integer-consp-canbe-symbol-integer-consp
                                                :formals (x)))))
                        (symbol-integer-alist-p)
                        (symbol-integer-consp)
                        (symbol-integer-array-equiv-consp)
                        (symbol-integer-array-p))
            :datatypes (:sumtypes ((maybe-symbol-integer-consp
                                    :recognizer
                                    (maybe-symbol-integer-consp :translation "MaybeSymbolIntegerCons")
                                    :sums
                                    ((:constructor (maybe-symbol-integer-cons->cons
                                                    :translation "cons"
                                                    :return-type maybe-symbol-integer-consp)
                                      :destructors ((maybe-symbol-integer-cons->car
                                                     :translation "car"
                                                     :return-type symbolp)
                                                    (maybe-symbol-integer-cons->cdr
                                                     :translation "cdr"
                                                     :return-type integerp)))
                                     (:constructor (maybe-symbol-integer-cons->nil
                                                    :fn-to-const t
                                                    :translation "nil"
                                                    :return-type maybe-symbol-integer-consp)
                                                   :destructors nil))
                                    :property-hints
                                    ((uniqueness-of-maybe-symbol-integer-consp-constructor-of-destructors)
                                     (type-of-maybe-symbol-integer-cons->nil)
                                     (destructors-of-maybe-symbol-integer-cons->cons)
                                     (type-of-maybe-symbol-integer-cons->cons-destructors)
                                     (type-of-maybe-symbol-integer-cons->cons)
                                     (type-of-maybe-symbol-integer-consp))))
                        :arrays ((symbol-integer-array-p
                                  :recognizer (symbol-integer-array-p
                                               :translation "SymbolIntegerArray")
                                  :key-type symbolp
                                  :val-type maybe-symbol-integer-consp
                                  :init (:fn (symbol-integer-array-init
                                              :translation
                                              "symbolIntegerArrayInit")
                                         :val maybe-symbol-integer-cons->nil)
                                  :select (symbol-integer-array-select)
                                  :store (symbol-integer-array-store)
                                  :equal (symbol-integer-array-equal)
                                  :equal-witness
                                  (symbol-integer-array-equal-witness)
                                  :property-hints
                                  ((type-of-symbol-integer-array-p-equal)
                                   (reflexivity-of-symbol-integer-array-p-equal)
                                   (symmetricity-of-symbol-integer-array-p-equal)
                                   (transitivity-of-symbol-integer-array-p-equal)
                                   (symbol-integer-array-p-equal-implies-select-equal
                                    . (:use ((:instance
                                              symbol-integer-array-equal-implies-select-equal))))
                                   (select-of-witness-equal-implies-symbol-integer-array-p-equal
                                    . (:use ((:instance
                                              select-of-witness-equal-implies-symbol-integer-array-equal))))
                                   (type-of-symbol-integer-array-p-store)
                                   (symbol-integer-array-p-select-distinct
                                    . (:in-theory (enable symbol-integer-array-select-of-symbol-integer-array-store)))
                                   (symbol-integer-array-p-select-equal
                                    . (:in-theory (enable
                                                   symbol-integer-array-select-of-symbol-integer-array-store)))
                                   (type-of-symbol-integer-array-p-select)
                                   (type-of-symbol-integer-array-p-init)
                                   (equal-of-symbol-integer-array-p-init
                                    . (:in-theory (enable
                                                   symbol-integer-array-select-of-symbol-integer-array-init)))
                                   (type-of-symbol-integer-array-p)))))
            :replaces ((:thm
                        symbol-integer-array-translation-of-assoc-equal)
                       (:thm symbol-integer-array-translation-of-acons)
                       (:thm symbol-integer-array-translation-of-alist)
                       (:thm symbol-integer-array-translation-of-nil)
                       (:thm
                        replace-of-cdr-of-symbol-integer-consp)
                       (:thm replace-of-maybe-symbol-integer-cons->nil))
            ))))

(encapsulate
  (((abs-p *) => *))
  (local (defun abs-p (x) (acl2::any-p x)))
  (defthm booleanp-of-abs-p
    (booleanp (abs-p x)))
  (defthm booleanp-of-equal-of-abs-p
    (implies (and (abs-p x) (abs-p y))
             (booleanp (equal x y)))))

(defthm test11
  (implies (abs-p x) (equal x x))
  :hints (("Goal"
           :smtlink
           (:functions ((equal
                         :kind :basic
                         :translation "_SMT_.equal"
                         :return ((:thm booleanp-of-equal-of-abs-p
                                        :formals (x y))))
                        (abs-p
                         :return ((:thm booleanp-of-abs-p
                                        :formals (x)))))
            :acl2types ((abs-p))
            :datatypes (:abstracts ((abs-p
                                     :recognizer (abs-p :translation "AbsType")
                                     :property-hints ((type-of-abs-p-equal)
                                                      (reflexivity-of-abs-p-equal)
                                                      (symmetricity-of-abs-p-equal)
                                                      (transitivity-of-abs-p-equal)
                                                      (type-of-abs-p))))))))
  :rule-classes nil)

;; Example 1
;; (def-saved-event x^2-y^2
;;   (define x^2-y^2 ((x real/rationalp)
;;                    (y real/rationalp))
;;     :returns (f real/rationalp)
;;     (b* ((x (realfix x))
;;          (y (realfix y)))
;;       (- (* x x) (* y y)))))

;; (def-saved-event x^2+y^2
;;   (define x^2+y^2 ((x real/rationalp)
;;                    (y real/rationalp))
;;     :returns (f real/rationalp)
;;     (b* ((x (realfix x))
;;          (y (realfix y)))
;;       (+ (* x x) (* y y)))))

;; (def-saved-event poly-ineq
;;   (defthm poly-ineq-example
;;     (implies (and (real/rationalp x) (real/rationalp y)
;;                   (<= (+ (* (/ 9 8) x x) (* y y)) 1)
;;                   (<=  (x^2-y^2 x y) 1))
;;              (< y (- (* 3 (- x (/ 17 8)) (- x (/ 17 8))) 3)))
;;     :hints(("Goal"
;;             :smtlink
;;             (:functions ((x^2-y^2 :formals (x y)
;;                                   :return (real/rationalp-of-x^2-y^2)
;;                                   :depth 1))))))
;;   )

;; (deftutorial Example-1
;;   :parents (Tutorial)
;;   :short "Example 1: the basics"
;;   :long "<h3>Example 1</h3>
;; <p>Prerequisite read for this tutorial example is @(tsee tutorial).</p>
;; <p>The first example is a basic polynomial inequality.  Let's say we want to
;; prove below theorem:</p>

;; <box>
;; <p>
;; <b><color rgb='#323cbe'>Theorem 1.</color></b>
;; @($\\forall x\\in R$) and @($\\forall y \\in R$), if @($ \\frac{9x^2}{8}+y^2 \\le 1$) and
;; @($ x^2-y^2 \\le 1$), then @($ y < 3(x-\\frac{17}{8})^2 - 3$).
;; </p>
;; </box>

;; <p>Suppose we've defined a function called @('x^2-y^2') like below:</p>

;; @(`(:code ($ x^2-y^2))`)

;; <p>We define our theorem as:</p>

;; @(`(:code ($ poly-ineq))`)

;; <p>Smtlink should just prove this inequality without any problem.</p>
;; <p>Like is shown in the example, @(':smtlink') can be provided as a hint in the
;; standard @(see acl2::hints) in ACL2.  In the most basic cases where Smtlink
;; handles everything, no @(see smt-hint) are required to be provided, Hence
;; @(':smtlink nil').</p>

;; <p>The output of this defthm should look similar to:</p>

;; @({
;; Using clause-processor Smtlink
;; Goal'
;; Goal''
;; SMT-goal-generator=>Expanding ... X^2-Y^2
;; Subgoal 2
;; Subgoal 2.2
;; Subgoal 2.2'
;; Using default SMT-trusted-cp...
;; ; SMT solver: `/usr/bin/env python /tmp/py_file/smtlink.w59zR`: 0.52 sec, 7,904 bytes
;; Proved!
;; Subgoal 2.2''
;; Subgoal 2.1
;; Subgoal 2.1'
;; Subgoal 1
;; Subgoal 1'

;; Summary
;; Form:  ( DEFTHM POLY-INEQ-EXAMPLE ...)
;; Rules: ((:DEFINITION HIDE)
;;         (:DEFINITION HINT-PLEASE)
;;         (:DEFINITION NOT)
;;         (:DEFINITION TYPE-HYP)
;;         (:DEFINITION X^2-Y^2)
;;         (:EXECUTABLE-COUNTERPART BINARY-*)
;;         (:EXECUTABLE-COUNTERPART ACL2::BOOLEAN-LIST-FIX$INLINE)
;;         (:EXECUTABLE-COUNTERPART CAR)
;;         (:EXECUTABLE-COUNTERPART CDR)
;;         (:EXECUTABLE-COUNTERPART CONS)
;;         (:EXECUTABLE-COUNTERPART CONSP)
;;         (:EXECUTABLE-COUNTERPART UNARY--)
;;         (:EXECUTABLE-COUNTERPART UNARY-/)
;;         (:FAKE-RUNE-FOR-TYPE-SET NIL)
;;         (:REWRITE ASSOCIATIVITY-OF-+)
;;         (:REWRITE ACL2::COMMUTATIVITY-2-OF-+)
;;         (:REWRITE COMMUTATIVITY-OF-*)
;;         (:REWRITE COMMUTATIVITY-OF-+)
;;         (:REWRITE DISTRIBUTIVITY)
;;         (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
;; Hint-events: ((:CLAUSE-PROCESSOR ADD-HYPO-CP)
;;               (:CLAUSE-PROCESSOR EXPAND-CP-FN)
;;               (:CLAUSE-PROCESSOR PROCESS-HINT)
;;               (:CLAUSE-PROCESSOR SMT-TRUSTED-CP)
;;               (:CLAUSE-PROCESSOR TYPE-EXTRACT-FN)
;;               (:CLAUSE-PROCESSOR UNINTERPRETED-FN-CP))
;; Time:  0.60 seconds (prove: 0.60, print: 0.00, other: 0.00)
;; Prover steps counted:  1440
;; POLY-INEQ-EXAMPLE

;; })

;; <p>Smtlink is a sequence of clause processors controlled by a computed hint.
;; Calling smtlink from the @(':hints') put the theorem clause though a clause
;; processor looking for syntax errors in the @(see smt-hint).  If nothing wrong,
;; it will generate a term to be recognized by the computed-hint
;; @('SMT::SMT-computed-hint').  The computed-hint then installs the next-to-be
;; clause processor to work on the clause.  The next is the verified clause
;; processor for adding hypotheses. After that is the verified clause processor
;; for function expansion.</p>

;; <p>@('SMT-goal-generator=>Expanding ... X^2-Y^2') shows function expansion is
;; being conducted. </p>

;; <p>In this example, several subgoals are generated as a result of this clause
;; processor.  The first subgoal is the goal to be sent to the trusted clause
;; processor that transliterates the term into the corresponding SMT form and
;; writes it out to a file.  An SMT solver is called upon the file and results are
;; read back into ACL2.  Below are the outputs from this clause processor called
;; @('SMT-trusted-cp').
;; </p>

;; @({
;; Using default SMT-trusted-cp...
;; ; SMT solver: `/usr/bin/env python /tmp/py_file/smtlink.w59zR`: 0.52 sec, 7,904 bytes
;; Proved!
;; })

;; <p>The second line tells the user what command is run to execute the SMT
;; solving.  \"Proved!\" indicates the SMT solver has successfully proved the
;; theorem.  When a theorem failed, a possible counter-example might be
;; provided in the form:</p>
;; @({
;; Possible counter-example found: ((X ...) (Y ...))
;; One can access it through global variable SMT-cex by doing (@ SMT-
;; cex).
;; })

;; <p>Other subgoals are auxiliary clauses generated by the verified
;; clause-processors. They help ensure the soundness of Smtlink.</p>
;; ")

;; (def-saved-event smtconf-expt-tutorial
;;   (defun my-smtlink-expt-config ()
;;     (declare (xargs :guard t))
;;     (change-smtlink-config (default-smt-cnf)
;;                            :smt-module    "RewriteExpt"
;;                            :smt-class     "to_smt_w_expt"
;;                            :smt-cmd       "/usr/bin/env python"
;;                            :pythonpath    "")))

;; (def-saved-event smtconf-expt-defattach-tutorial
;;   (defattach custom-smt-cnf my-smtlink-expt-config))

;; ;; Example 2
;; (def-saved-event poly-of-expt-example
;;   (encapsulate ()
;;     (local (include-book "arithmetic-5/top" :dir :system))

;;     (define expt-rationalp ((r real/rationalp)
;;                             (i integerp))
;;       :returns (ex real/rationalp)
;;       :guard (>= i 0)
;;       (b* ((r (realfix r))
;;            (i (ifix i)))
;;         (expt r i)))

;;     (defthm poly-of-expt-example
;;       (implies (and (real/rationalp x) (real/rationalp y) (real/rationalp z)
;;                     (integerp m) (integerp n)
;;                     (< 0 z) (< z 1) (< 0 m) (< m n))
;;                (<= (* 2 (expt-rationalp z n) x y)
;;                    (* (expt-rationalp z m) (x^2+y^2 x y))))
;;       :hints (("Goal"
;;                :smtlink-custom (:functions ((expt-rationalp
;;                                              :formals ((r real/rationalp)
;;                                                        (i real/rationalp))
;;                                              :returns ((ex real/rationalp
;;                                                            :name
;;                                                            real/rationalp-of-expt-rationalp))
;;                                              :expansion-depth 0)
;;                                             (x^2+y^2 :formals ((x real/rationalp)
;;                                                                (y real/rationalp))
;;                                                      :returns ((f
;;                                                                 real/rationalp
;;                                                                 :name
;;                                                                 real/rationalp-of-x^2+y^2))
;;                                                      :expansion-depth 1))
;;                                            :hypotheses (((< (expt-rationalp z n)
;;                                                             (expt-rationalp z m))
;;                                                          :hints (:in-theory
;;                                                                  (enable
;;                                                                   expt-rationalp))))
;;                                            ;; We can prove this theorem using
;;                                            ;; purely smtlink by enabling below
;;                                            ;; two hypotheses.
;;                                            ;;              ((< 0 (expt-rationalp z m))
;;                                            ;;               :hints (:in-theory
;;                                            ;;                       (enable expt-rationalp)))
;;                                            ;;              ((< 0 (expt-rationalp z n))
;;                                            ;;               :hints (:in-theory
;;                                            ;;                       (enable expt-rationalp))))
;;                                            :int-to-rat t)
;;                )))))

;; (deftutorial Example-2
;;   :parents (Tutorial)
;;   :short "Example 2: something wild"
;;   :long "<h3>Example 2</h3>
;; <p>Prerequisite read for this tutorial example is @(tsee tutorial).</p>
;; <p>Smtlink is extensible, with the user's understanding that the extended part
;; is not verified and therefore is the user's responsibility to ensure its
;; soundness.  A different trust tag is installed if this customized Smtlink is
;; used.  Such ability makes Smtlink very powerful.  Here's an example to show the
;; usage.</p>
;; <p>Let's say we want to prove the theorem:</p>

;; <box>
;; <p>
;; <b><color rgb='#323cbe'>Theorem 2.</color></b>
;; @($\\forall x,y,z\\in R$), and @($\\forall m,n \\in Z$), if @($ 0 \\le z \\le 1$) and
;; @($ 0 \\le m \\le n $), then @($ 2xy\\cdot z^n \\le (x^2+y^2)z^m$).
;; </p>
;; </box>

;; <p>In @('smtlink/z3_interface/'), file @('RewriteExpt.py') is a Python class
;; extending from the default class in ACL2_to_Z3.py.  One could imaging defining
;; one's own file that does magical things in the SMT solver.  What
;; @('RewriteExpt.py') does is that it uses basic rewrite lemmas about @('expt')
;; to help the SMT solver to solve.  In order to make Smtlink uses the custom
;; version instead of the default, one needs to define and attach a new
;; configuration:</p>

;; @(`(:code ($ smtconf-expt-tutorial))`)
;; @(`(:code ($ smtconf-expt-defattach-tutorial))`)

;; <p>Defining the function @('x^2+y^2')</p>
;; @(`(:code ($ ||x^2+y^2||))`)

;; <p>Then define the theorem to prove:</p>
;; @(`(:code ($ poly-of-expt-example))`)

;; <p>Notice the @(':hints') keyword used this time is @(':smtlink-custom').  It
;; allows the customized version of Smtlink to be applied to the current
;; clause.  Take a read in @(see smt-hint) for a detailed description of each
;; keyword.  Here we will only describe what's used in this example.</p>

;; <p>In the hints, @(':function') tells Smtlink to treat @('expt') as an
;; uninterpreted function.  @(':formals') tells us the input argument types of the
;; uninterpreted function and @(':returns') tells us the output argument type.
;; @(':levels') specifies an expansion level of 0, making the function an
;; uninterpreted function.</p>

;; <p>@(':hypotheses') provides a list of hypotheses that the user believes to be
;; true and can help with the proof. The hypotheses will be insert into the
;; hypotheses when generating the SMT problem. They will be proved correctness
;; as part of the returned clauses from the verified clause processor. </p>

;; <p>@(':int-to-rat') tells Smtlink to raise integers to rationals when
;; translating the clause into a SMT problem. This is because of the limitation in
;; Z3. Integers mixed with real numbers are hard for Z3. We prove the given
;; theorem by proving a more general statement in the SMT solver.</p>

;; <p>Another observation is that, we are including the arithmetic-5 book for
;; proving the returned auxiliary clauses, which requires arithmetic
;; reasoning.</p>
;; ")

;; ;; Buggy example
;; (def-saved-event non-theorem-example
;;   (acl2::must-fail
;;    (defthm non-theorem
;;      (implies (and (real/rationalp x)
;;                    (real/rationalp y)
;;                    (integerp (/ x y)))
;;               (not (equal y 0)))
;;      :hints(("Goal"
;;              :smtlink nil))
;;      :rule-classes nil)))

;; (deftutorial Example-3
;;   :parents (Tutorial)
;;   :short "Example 3: defense against evil"
;;   :long "<h3>Example 3</h3>
;; <p>Prerequisite read for this tutorial example is @(tsee tutorial).</p>
;; <p>The third evil example is from one of the reviews we get when we first
;; published our paper in @(see Smtlink). </p>

;; @(`(:code ($ non-theorem-example))`)

;; <p>This is an evil theorem because we know below is a theorem in ACL2:</p>

;; @({
;; (thm (equal (/ x 0) 0))
;; })

;; <p>Therefore if Smtlink falsely prove @('non-theorem'), it will introduce
;; contradiction into ACL2.</p>

;; <p>Smtlink fails to prove the @('non-theorem') with error message:</p>

;; @({
;; HARD ACL2 ERROR in SMT-TRANSLATOR=>TRANSLATE-FUNCTION:  Not a basic
;; SMT function: INTEGERP
;; })

;; <p>This is because ACL2 treats @('integerp')'s as type declarations in Z3.  But
;; here in this theorem, @('(integerp (/ x y))') is a constraint/hypotheses rather
;; than a type declaration. When ACL2 tried to translate it as a constraint, it
;; finds out @('integerp') is not a supported function.</p>
;; ")

;; (define foo ((x real/rationalp))
;;   :returns (rx real/rationalp)
;;   (b* ((x (realfix x)))
;;     (+ (* x x) 1)))

;; (in-theory (disable (:type-prescription foo)))

;; (defthm poly-ineq-example-functions
;;   (implies (and (real/rationalp x))
;;            (< 0 (* 2 (foo x))))
;;   :hints(("Goal"
;;           :smtlink
;;           (:functions ((foo :formals ((x real/rationalp))
;;                             :returns ((rx real/rationalp
;;                                           :name
;;                                           real/rationalp-of-foo))
;;                             :expansion-depth 0))
;;            :hypotheses (((<= 1 (foo x))
;;                          :hints (:in-theory (enable foo))))
;;           ))))

;; (def-saved-event x^2+y^2-integer
;;   (define x^2+y^2-integer ((x integerp)
;;                            (y integerp))
;;     :returns (f integerp)
;;     (b* ((x (ifix x))
;;          (y (ifix y)))
;;       (+ (* x x) (* y y)))))

;; (include-book "centaur/fty/baselists" :dir :system)

;; (local (in-theory (enable acl2::integer-list-fix)))

;; (define integer-list-cons ((x integerp)
;;                            (l integer-listp))
;;   :returns (nl integer-listp)
;;   (b* ((x (ifix x))
;;        (l (acl2::integer-list-fix l)))
;;     (cons x l)))

;; (define integer-list-car ((l integer-listp))
;;   :returns (x integerp)
;;   (b* ((l (acl2::integer-list-fix l)))
;;     (ifix (car l))))

;; (define integer-list-cdr ((l integer-listp))
;;   :returns (nl integer-listp)
;;   (b* ((l (acl2::integer-list-fix l)))
;;     (cdr l)))

;; (define integer-list-nil ()
;;   :returns (nl integer-listp)
;;   (acl2::integer-list-fix nil))

;; (defthm integer-list-fix-when-integer-listp
;;   (implies (integer-listp x)
;;            (equal (acl2::integer-list-fix x) x)))

;; (defsmtlist integer-list
;;   :rec integer-listp
;;   :fix acl2::integer-list-fix
;;   :fix-thm integer-list-fix-when-integer-listp
;;   :cons integer-list-cons
;;   :car integer-list-car
;;   :cdr integer-list-cdr
;;   :nil-fn integer-list-nil
;;   :elt-type integerp
;;   )

;; (deftutorial Example-1
;;   :parents (Tutorial)
;;   :short "Example 1: the basics"
;;   :long "<h3>Example 1</h3>
;; <p>Prerequisite read for this tutorial example is @(tsee tutorial).</p>
;; <p>The first example is a basic polynomial inequality.  Let's say we want to
;; prove below theorem:</p>

;; <box>
;; <p>
;; <b><color rgb='#323cbe'>Theorem 1.</color></b>
;; @($\\forall x\\in R$) and @($\\forall y \\in R$), if @($ \\frac{9x^2}{8}+y^2 \\le 1$) and
;; @($ x^2-y^2 \\le 1$), then @($ y < 3(x-\\frac{17}{8})^2 - 3$).
;; </p>
;; </box>

;; <p>Suppose we've defined a function called @('x^2-y^2') like below:</p>

;; @(`(:code ($ x^2-y^2))`)

;; <p>We define our theorem as:</p>

;; @(`(:code ($ poly-ineq))`)

;; <p>Smtlink should just prove this inequality without any problem.</p>
;; <p>Like is shown in the example, @(':smtlink') can be provided as a hint in the
;; standard @(see acl2::hints) in ACL2.  In the most basic cases where Smtlink
;; handles everything, no @(see smt-hint) are required to be provided, Hence
;; @(':smtlink nil').</p>

;; <p>The output of this defthm should look similar to:</p>

;; @({
;; Using clause-processor Smtlink
;; Goal'
;; Goal''
;; SMT-goal-generator=>Expanding ... X^2-Y^2
;; Subgoal 2
;; Subgoal 2.2
;; Subgoal 2.2'
;; Using default SMT-trusted-cp...
;; ; SMT solver: `python /tmp/py_file/smtlink.w59zR`: 0.52 sec, 7,904 bytes
;; Proved!
;; Subgoal 2.2''
;; Subgoal 2.1
;; Subgoal 2.1'
;; Subgoal 1
;; Subgoal 1'

;; Summary
;; Form:  ( DEFTHM POLY-INEQ-EXAMPLE ...)
;; Rules: ((:DEFINITION HIDE)
;;         (:DEFINITION HINT-PLEASE)
;;         (:DEFINITION NOT)
;;         (:DEFINITION TYPE-HYP)
;;         (:DEFINITION X^2-Y^2)
;;         (:EXECUTABLE-COUNTERPART BINARY-*)
;;         (:EXECUTABLE-COUNTERPART ACL2::BOOLEAN-LIST-FIX$INLINE)
;;         (:EXECUTABLE-COUNTERPART CAR)
;;         (:EXECUTABLE-COUNTERPART CDR)
;;         (:EXECUTABLE-COUNTERPART CONS)
;;         (:EXECUTABLE-COUNTERPART CONSP)
;;         (:EXECUTABLE-COUNTERPART UNARY--)
;;         (:EXECUTABLE-COUNTERPART UNARY-/)
;;         (:FAKE-RUNE-FOR-TYPE-SET NIL)
;;         (:REWRITE ASSOCIATIVITY-OF-+)
;;         (:REWRITE ACL2::COMMUTATIVITY-2-OF-+)
;;         (:REWRITE COMMUTATIVITY-OF-*)
;;         (:REWRITE COMMUTATIVITY-OF-+)
;;         (:REWRITE DISTRIBUTIVITY)
;;         (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
;; Hint-events: ((:CLAUSE-PROCESSOR ADD-HYPO-CP)
;;               (:CLAUSE-PROCESSOR EXPAND-CP-FN)
;;               (:CLAUSE-PROCESSOR PROCESS-HINT)
;;               (:CLAUSE-PROCESSOR SMT-TRUSTED-CP)
;;               (:CLAUSE-PROCESSOR TYPE-EXTRACT-FN)
;;               (:CLAUSE-PROCESSOR UNINTERPRETED-FN-CP))
;; Time:  0.60 seconds (prove: 0.60, print: 0.00, other: 0.00)
;; Prover steps counted:  1440
;; POLY-INEQ-EXAMPLE

;; })

;; <p>Smtlink is a sequence of clause processors controlled by a computed hint.
;; Calling smtlink from the @(':hints') put the theorem clause though a clause
;; processor looking for syntax errors in the @(see smt-hint).  If nothing wrong,
;; it will generate a term to be recognized by the computed-hint
;; @('SMT::SMT-computed-hint').  The computed-hint then installs the next-to-be
;; clause processor to work on the clause.  The next is the verified clause
;; processor for adding hypotheses. After that is the verified clause processor
;; for function expansion.</p>

;; <p>@('SMT-goal-generator=>Expanding ... X^2-Y^2') shows function expansion is
;; being conducted. </p>

;; <p>In this example, several subgoals are generated as a result of this clause
;; processor.  The first subgoal is the goal to be sent to the trusted clause
;; processor that transliterates the term into the corresponding SMT form and
;; writes it out to a file.  An SMT solver is called upon the file and results are
;; read back into ACL2.  Below are the outputs from this clause processor called
;; @('SMT-trusted-cp').
;; </p>

;; @({
;; Using default SMT-trusted-cp...
;; ; SMT solver: `python /tmp/py_file/smtlink.w59zR`: 0.52 sec, 7,904 bytes
;; Proved!
;; })

;; <p>The second line tells the user what command is run to execute the SMT
;; solving.  \"Proved!\" indicates the SMT solver has successfully proved the
;; theorem.  When a theorem failed, a possible counter-example might be
;; provided in the form:</p>
;; @({
;; Possible counter-example found: ((X ...) (Y ...))
;; One can access it through global variable SMT-cex by doing (@ SMT-
;; cex).
;; })

;; <p>Other subgoals are auxiliary clauses generated by the verified
;; clause-processors. They help ensure the soundness of Smtlink.</p>
;; ")

;; (def-saved-event smtconf-expt-tutorial
;;   (defun my-smtlink-expt-config ()
;;     (declare (xargs :guard t))
;;     (change-smtlink-config (default-smt-cnf)
;;                            :smt-module    "RewriteExpt"
;;                            :smt-class     "to_smt_w_expt"
;;                            :smt-cmd       "python"
;;                            :pythonpath    "")))

;; (def-saved-event smtconf-expt-defattach-tutorial
;;   (defattach custom-smt-cnf my-smtlink-expt-config))

;; ;; Example 2
;; (def-saved-event poly-of-expt-example
;;   (encapsulate ()
;;     (local (include-book "arithmetic-5/top" :dir :system))
;;     (defthm poly-of-expt-example
;;       (implies (and (real/rationalp x) (real/rationalp y) (real/rationalp z)
;;                     (integerp m) (integerp n)
;;                     (< 0 z) (< z 1) (< 0 m) (< m n))
;;                (<= (* 2 (expt z n) x y)
;;                    (* (expt z m) (x^2+y^2 x y))))
;;       :hints (("Goal"
;;                :smtlink-custom (:functions ((expt :formals ((r real/rationalp)
;;                                                             (i real/rationalp))
;;                                                   :returns ((ex real/rationalp))
;;                                                   :level 0))
;;                                 :hypotheses (((< (expt z n) (expt z m)))
;;                                              ((< 0 (expt z m)))
;;                                              ((< 0 (expt z n))))
;;                                 :int-to-rat t)
;;       )))))

;; (deftutorial Example-2
;;   :parents (Tutorial)
;;   :short "Example 2: something wild"
;;   :long "<h3>Example 2</h3>
;; <p>Prerequisite read for this tutorial example is @(tsee tutorial).</p>
;; <p>Smtlink is extensible, with the user's understanding that the extended part
;; is not verified and therefore is the user's responsibility to ensure its
;; soundness.  A different trust tag is installed if this customized Smtlink is
;; used.  Such ability makes Smtlink very powerful.  Here's an example to show the
;; usage.</p>
;; <p>Let's say we want to prove the theorem:</p>

;; <box>
;; <p>
;; <b><color rgb='#323cbe'>Theorem 2.</color></b>
;; @($\\forall x,y,z\\in R$), and @($\\forall m,n \\in Z$), if @($ 0 \\le z \\le 1$) and
;; @($ 0 \\le m \\le n $), then @($ 2xy\\cdot z^n \\le (x^2+y^2)z^m$).
;; </p>
;; </box>

;; <p>In @('smtlink/z3_interface/'), file @('RewriteExpt.py') is a Python class
;; extending from the default class in ACL2_to_Z3.py.  One could imaging defining
;; one's own file that does magical things in the SMT solver.  What
;; @('RewriteExpt.py') does is that it uses basic rewrite lemmas about @('expt')
;; to help the SMT solver to solve.  In order to make Smtlink uses the custom
;; version instead of the default, one needs to define and attach a new
;; configuration:</p>

;; @(`(:code ($ smtconf-expt-tutorial))`)
;; @(`(:code ($ smtconf-expt-defattach-tutorial))`)

;; <p>Defining the function @('x^2+y^2')</p>
;; @(`(:code ($ ||x^2+y^2||))`)

;; <p>Then define the theorem to prove:</p>
;; @(`(:code ($ poly-of-expt-example))`)

;; <p>Notice the @(':hints') keyword used this time is @(':smtlink-custom').  It
;; allows the customized version of Smtlink to be applied to the current
;; clause.  Take a read in @(see smt-hint) for a detailed description of each
;; keyword.  Here we will only describe what's used in this example.</p>

;; <p>In the hints, @(':function') tells Smtlink to treat @('expt') as an
;; uninterpreted function.  @(':formals') tells us the input argument types of the
;; uninterpreted function and @(':returns') tells us the output argument type.
;; @(':levels') specifies an expansion level of 0, making the function an
;; uninterpreted function.</p>

;; <p>@(':hypotheses') provides a list of hypotheses that the user believes to be
;; true and can help with the proof. The hypotheses will be insert into the
;; hypotheses when generating the SMT problem. They will be proved correctness
;; as part of the returned clauses from the verified clause processor. </p>

;; <p>@(':int-to-rat') tells Smtlink to raise integers to rationals when
;; translating the clause into a SMT problem. This is because of the limitation in
;; Z3. Integers mixed with real numbers are hard for Z3. We prove the given
;; theorem by proving a more general statement in the SMT solver.</p>

;; <p>Another observation is that, we are including the arithmetic-5 book for
;; proving the returned auxiliary clauses, which requires arithmetic
;; reasoning.</p>
;; ")

;; ;; Buggy example
;; (def-saved-event non-theorem-example
;;   (acl2::must-fail
;;    (defthm non-theorem
;;      (implies (and (real/rationalp x)
;;                    (real/rationalp y)
;;                    (integerp (/ x y)))
;;               (not (equal y 0)))
;;      :hints(("Goal"
;;              :smtlink nil))
;;      :rule-classes nil)))

;; (deftutorial Example-3
;;   :parents (Tutorial)
;;   :short "Example 3: defense against evil"
;;   :long "<h3>Example 3</h3>
;; <p>Prerequisite read for this tutorial example is @(tsee tutorial).</p>
;; <p>The third evil example is from one of the reviews we get when we first
;; published our paper in @(see Smtlink). </p>

;; @(`(:code ($ non-theorem-example))`)

;; <p>This is an evil theorem because we know below is a theorem in ACL2:</p>

;; @({
;; (thm (equal (/ x 0) 0))
;; })

;; <p>Therefore if Smtlink falsely prove @('non-theorem'), it will introduce
;; contradiction into ACL2.</p>

;; <p>Smtlink fails to prove the @('non-theorem') with error message:</p>

;; @({
;; HARD ACL2 ERROR in SMT-TRANSLATOR=>TRANSLATE-FUNCTION:  Not a basic
;; SMT function: INTEGERP
;; })

;; <p>This is because ACL2 treats @('integerp')'s as type declarations in Z3.  But
;; here in this theorem, @('(integerp (/ x y))') is a constraint/hypotheses rather
;; than a type declaration. When ACL2 tried to translate it as a constraint, it
;; finds out @('integerp') is not a supported function.</p>
;; ")

;; (define foo ((x real/rationalp))
;;   :returns (rx real/rationalp)
;;   (b* ((x (realfix x)))
;;     (+ (* x x) 1)))

;; (in-theory (disable (:type-prescription foo)))

;; (defthm poly-ineq-example-functions
;;   (implies (and (real/rationalp x))
;;            (< 0 (* 2 (foo x))))
;;   :hints(("Goal"
;;           :smtlink
;;           (:functions ((foo :formals ((x real/rationalp))
;;                             :returns ((rx real/rationalp))
;;                             :level 0))
;;            :hypotheses (((<= 1 (foo x))
;;                          :hints (:in-theory (enable foo))))
;;           ))))

;; (def-saved-event fty-deflist-theorem-example
;;   (defthm fty-deflist-theorem
;;     (implies (and (integer-listp l)
;;                   (consp (acl2::integer-list-fix l))
;;                   (consp (acl2::integer-list-fix (cdr (acl2::integer-list-fix l)))))
;;              (>= (x^2+y^2 (car (acl2::integer-list-fix l))
;;                           (car (acl2::integer-list-fix
;;                                 (cdr (acl2::integer-list-fix l)))))
;;                  0))
;;     :hints(("Goal"
;;             :smtlink
;;             (:fty (acl2::integer-list))))
;;     :rule-classes nil))

;; ;; should type check
;; (acl2::must-fail
;;  (defthm crazy-list-theorem-1
;;    (implies (and (integer-listp l1)
;;                  (integer-listp l2)
;;                  (equal (cons 1 (cons 2 (cons 3 nil))) l2))
;;             (equal l1 l2))
;;    :hints(("Goal"
;;            :smtlink nil))
;;    :rule-classes nil)
;;  )

;; ;; should type check
;; (acl2::must-fail
;;  (defthm crazy-list-theorem-2
;;    (implies (and (rational-listp l1)
;;                  (rational-listp l2)
;;                  (equal (cons 1/2 (cons 2 (cons 3 nil))) l2))
;;             (equal l1 l2))
;;    :hints(("Goal"
;;            :smtlink nil))
;;    :rule-classes nil)
;;  )

;; ;; should type check
;; (acl2::must-fail
;;  (defthm crazy-list-theorem-3
;;    (implies (and (rational-listp l1)
;;                  (rational-listp l2)
;;                  (equal (cons 1 (cons 1/2 (cons 3 nil))) l2))
;;             (equal l1 l2))
;;    :hints(("Goal"
;;            :smtlink nil))
;;    :rule-classes nil)
;;  )

;; ;; should type check
;; (acl2::must-fail
;;  (defthm crazy-list-theorem-4
;;    (implies (and (rational-listp l1)
;;                  (rational-listp l2)
;;                  (equal (cons 1/2 (cons 1/3 nil)) l2))
;;             (equal l1 l2))
;;    :hints(("Goal"
;;            :smtlink nil))
;;    :rule-classes nil)
;;  )

;; ;; should type check
;; (acl2::must-fail
;;  (defthm crazy-list-theorem-5
;;    (implies (and (rational-listp l1)
;;                  (rational-listp l2)
;;                  (equal (cons 1 (cons 2 (cons 3 l1))) l2))
;;             (equal l1 l2))
;;    :hints(("Goal"
;;            :smtlink nil))
;;    :rule-classes nil)
;;  )

;; ;; should fail type inference. Can't compare two lists with difference sorts --
;; ;; integer-listp and rational-listp.
;; (acl2::must-fail
;;  (defthm crazy-list-theorem-6
;;    (implies (and (integer-listp l1)
;;                  (rational-listp l2)
;;                  (equal (cons 1 (cons 2 (cons 3 l1))) l2))
;;             (equal l1 l2))
;;    :hints(("Goal"
;;            :smtlink nil))
;;    :rule-classes nil)
;;  )

;; ;; tests for acons
;; (defalist rational-rational-alist
;;   :key-type rationalp
;;   :val-type rationalp
;;   :pred rational-rational-alistp
;;   :true-listp t)

;; (defsmtarray rational-rational-alist
;;   :rec rational-rational-alistp
;;   :fix rational-rational-alist-fix
;;   :fix-thm rational-rational-alist-fix-when-rational-rational-alist-p
;;   :k k
;;   :store rational-rational-alist-store
;;   :select rational-rational-alist-select
;;   :key-type rationalp
;;   :val-type rationalp
;;   )

;; (defalist integer-integer-alist
;;   :key-type integerp
;;   :val-type integerp
;;   :pred integer-integer-alistp
;;   :true-listp t)

;; (defsmtarray integer-integer-alist
;;   :rec integer-integer-alistp
;;   :fix integer-integer-alist-fix
;;   :fix-thm integer-integer-alist-fix-when-integer-integer-alist-p
;;   :k k
;;   :store integer-integer-alist-store
;;   :select integer-integer-alist-select
;;   :key-type integerp
;;   :val-type integerp
;;   )

;; (defalist integer-rational-alist
;;   :key-type integerp
;;   :val-type rationalp
;;   :pred integer-rational-alistp
;;   :true-listp t)

;; (defsmtarray integer-rational-alist
;;   :rec integer-rational-alistp
;;   :fix integer-rational-alist-fix
;;   :fix-thm integer-rational-alist-fix-when-integer-rational-alist-p
;;   :k k
;;   :store integer-rational-alist-store
;;   :select integer-rational-alist-select
;;   :key-type integerp
;;   :val-type rationalp
;;   )

;; (defalist rational-integer-alist
;;   :key-type rationalp
;;   :val-type integerp
;;   :pred rational-integer-alistp
;;   :true-listp t)

;; (defsmtarray rational-integer-alist
;;   :rec rational-integer-alistp
;;   :fix rational-integer-alist-fix
;;   :fix-thm rational-integer-alist-fix-when-rational-integer-alist-p
;;   :k k
;;   :store rational-integer-alist-store
;;   :select rational-integer-alist-select
;;   :key-type rationalp
;;   :val-type integerp
;;   )

;; ;; should type check
;; (acl2::must-fail
;; (defthm crazy-alist-theorem
;;   (implies (and (rational-rational-alistp al1)
;;                 (rational-rational-alistp al2))
;;            (equal (acons 1 1/2 al1) al2))
;;   :hints(("Goal"
;;           :smtlink nil))
;;   :rule-classes nil)
;; )

;; ;; should type check
;; (acl2::must-fail
;; (defthm crazy-alist-theorem-1
;;   (implies (and (rational-rational-alistp al1)
;;                 (rational-rational-alistp al2))
;;            (equal (acons 1/2 1 (acons 1 1/2 al1)) al2))
;;   :hints(("Goal"
;;           :smtlink nil))
;;   :rule-classes nil)
;; )

;; ;; should fail type inference
;; (acl2::must-fail
;; (defthm crazy-alist-theorem-2
;;   (implies (and (integer-integer-alistp al1)
;;                 (rational-rational-alistp al2))
;;            (equal (acons 1 1/2 (acons 4 3 al1)) al2))
;;   :hints(("Goal"
;;           :smtlink nil))
;;   :rule-classes nil)
;; )

;; ;; should type check
;; (acl2::must-fail
;; (defthm crazy-alist-theorem-3
;;   (implies (integer-rational-alistp al2)
;;            (equal (acons 1 1/2 (acons 4 3 nil)) al2))
;;   :hints(("Goal"
;;           :smtlink nil))
;;   :rule-classes nil)
;; )

;; ;; should type check
;; (define integer-rational-consp (x)
;;   :guard t
;;   (and (consp x) (integerp (car x)) (rationalp (cdr x))))

;; (define integer-rational-cons-fix ((x integer-rational-consp))
;;   :returns (fixed integer-rational-consp)
;;   (mbe :logic (if (integer-rational-consp x) x `(0 . 0))
;;        :exec x)
;;   ///
;;   (more-returns
;;    (fixed (implies (integer-rational-consp x) (equal fixed x))
;;           :name equal-fixed-and-x-of-integer-rational-consp)))

;; (defthm integer-rational-cons-fix-idempotent-lemma
;;   (equal (integer-rational-cons-fix (integer-rational-cons-fix x))
;;          (integer-rational-cons-fix x))
;;   :hints (("Goal" :in-theory (enable integer-rational-cons-fix))))

;; (deffixtype integer-rational-cons
;;   :fix integer-rational-cons-fix
;;   :pred integer-rational-consp
;;   :equiv integer-rational-cons-equiv
;;   :define t
;;   :forward t
;;   :topic integer-rational-consp)

;; (defoption maybe-integer-rational-consp integer-rational-consp
;;   :pred maybe-integer-rational-consp)

;; (defsmtabstract integer-rational-consp
;;   :rec integer-rational-consp
;;   :fix integer-rational-cons-fix
;;   :fix-thm integer-rational-cons-fix-when-integer-rational-consp
;;   :basicp t)

;; (defsmtoption maybe-integer-rational-consp
;;   :rec maybe-integer-rational-consp
;;   :fix maybe-integer-rational-cons-fix
;;   :fix-thm maybe-integer-rational-cons-fix-when-maybe-integer-rational-consp
;;   :some-constructor maybe-integer-rational-consp-some
;;   :some-destructor maybe-integer-rational-consp-some->val
;;   :none-constructor maybe-integer-rational-consp-none
;;   :some-type integer-rational-consp
;;   )

;; (defoption maybe-rational rationalp
;;   :pred maybe-rationalp)

;; (defsmtoption maybe-rationalp
;;   :rec maybe-rationalp
;;   :fix maybe-rational-fix
;;   :fix-thm maybe-rational-fix-when-maybe-rationalp
;;   :some-constructor maybe-rational-some
;;   :some-destructor maybe-rational-some->val
;;   :none-constructor maybe-rational-none
;;   :some-type rationalp
;;   )

;; (define maybe-integer-rational-cdr ((x maybe-integer-rational-consp))
;;   :returns (y maybe-rationalp)
;;   :guard-hints (("Goal" :in-theory (enable
;;                                     maybe-integer-rational-consp-some->val
;;                                     maybe-integer-rational-consp
;;                                     integer-rational-consp)))
;;   (b* ((x (maybe-integer-rational-consp-fix x)))
;;     (if x
;;         (maybe-rational-some (cdr (maybe-integer-rational-consp-some->val x)))
;;       (maybe-rational-none))))

;; (acl2::must-fail
;; (defthm crazy-alist-theorem-4
;;   (implies (integer-rational-alistp al)
;;            (assoc-equal 1 (acons 1 2 al)))
;;   :hints(("Goal"
;;           :smtlink nil))
;;   :rule-classes nil)
;; )

;; ;; should type check
;; (acl2::must-fail
;;  (defthm crazy-alist-theorem-5
;;    (implies (integer-rational-alistp al)
;;             (b* ((al al))
;;               (assoc-equal 1 (acons 1 2 al))))
;;    :hints(("Goal"
;;            :smtlink nil))
;;    :rule-classes nil)
;;  )

;; ;; should type check
;; (defthm crazy-alist-theorem-1
;;   (implies (and (integer-rational-alistp al)
;;                 (integerp x))
;;            (+
;;            (b* ((y (assoc-equal x al))
;;                 ((if y) (cdr y)))
;;              0)
;;            (b* ((y (assoc-equal x al))
;;                 ((if y) (+ 1 (cdr y))))
;;              0)))
;;   :hints(("Goal"
;;           :smtlink nil)))

;; ;; should type check
;; (defthm crazy-alist-theorem-2
;;   (implies (and (integer-rational-alistp al)
;;                 (integerp x))
;;            (b* ((y (cdr (assoc-equal x al)))
;;                 ((if y) y))
;;              0))
;;   :hints(("Goal"
;;           :smtlink nil)))

;; (defprod lunch
;;   ((main symbolp)
;;    (snack integerp)
;;    (drink rationalp)))

;; (defsmtprod lunch
;;   :rec lunch-p
;;   :fix lunch-fix
;;   :fix-thm lunch-fix-when-lunch-p
;;   :constructor (lunch lunch-p)
;;   :destructors ((main symbolp) (snack integerp) (drink rationalp))
;;   )

;; ;;should type check
;; (acl2::must-fail
;; (defthm crazy-prod-theorem-1
;;   (implies (lunch-p x)
;;            (acons (lunch->snack x) (lunch->drink x) nil))
;;   :hints(("Goal"
;;           :smtlink nil))))

;; (defoption maybe-lunch lunch-p)

;; (defsmtoption maybe-lunch
;;   :rec maybe-lunch-p
;;   :fix maybe-lunch-fix
;;   :fix-thm maybe-lunch-fix-when-maybe-lunch-p
;;   :some-constructor maybe-lunch-some
;;   :some-destructor maybe-lunch-some->val
;;   :none-constructor maybe-lunch-none
;;   :some-type lunchp
;;   )

;; ;; should type check
;; (acl2::must-fail
;; (defthm crazy-option-theorem-1
;;   (implies (maybe-lunch-p x)
;;            (if x
;;                (acons (lunch->snack x) (lunch->drink x) nil)
;;              nil))
;;   :hints(("Goal"
;;           :smtlink nil))
;;   :rule-classes nil)
;; )

;; (deftagsum meal
;;   (:lunch ((main symbolp)
;;            (snack integerp)
;;            (drink rationalp)))
;;   (:dinner ((appetizer symbolp)
;;             (main symbolp)
;;             (desert integerp))))

;; (defsmtsum meal
;;   :rec meal-p
;;   :fix meal-fix
;;   :fix-thm meal-fix-when-meal-p
;;   :kind-function meal-kind
;;   :prods ((:lunch :constructor (meal-lunch meal-p)
;;                   :destructors ((main symbolp)
;;                                 (snack integerp)
;;                                 (drink rationalp)))
;;           (:dinner :contructor (meal-dinner meal-p)
;;                    :destructors ((appetizer symbolp)
;;                                  (main symbolp)
;;                                  (desert integerp)))))

;; ;; should type check
;; (defthm crazy-sum-theorem-1
;;   (implies (meal-p x)
;;            (if (equal (meal-kind x) :lunch)
;;                (equal (meal-lunch->snack x) (meal-lunch->drink x))
;;              (equal (meal-dinner->appetizer x) (meal-dinner->main x))))
;;   :hints(("Goal"
;;           :smtlink nil
;;           :rule-classes ni)))

;; ;; Abstract datatype example
;; (encapsulate
;;   (((abstract-p *) => *))
;;   (local
;;    (defun abstract-p (x)
;;        (acl2::any-p x))))

;; (defthm abstract-example
;;   (implies (abstract-p x)
;;            (equal x x))
;;   :hints(("Goal"
;;           :smtlink (:abstract (abstract-p))))
;;   :rule-classes nil)

;; ;; Thanks to Andrew Walter and Pete Manolios for providing this bug example.
;; ;; In this example, it used to be that unary-/ is translated to be integer
;; ;; division in Z3. Since unary-/ is interpreted as integer division and x >=
;; ;; 10, 1/x is 0, which makes y 0. We fixed this problem by casting the input of
;; ;; unary-/ to be real. Check the reciprocal function in ACL2_to_Z3.py for
;; ;; detail.
;; (acl2::must-fail
;;  (defthm smt-not-integer-division
;;    (implies (and (integerp x)
;;                  (integerp y)
;;                  (integerp z)
;;                  (>= x 10)
;;                  (= y (* (unary-/ x) z)))
;;             (= y 0))
;;    :hints (("goal" :smtlink nil))
;;    :rule-classes nil)
;;  )


;; (defthm fty-deflist-theorem
;;   (implies (and (integer-listp l)
;;                 (not (equal l nil))
;;                 (not (equal (cdr l) nil)))
;;            (>= (x^2+y^2-integer (car l)
;;                                 (cadr l))
;;                0))
;;   :hints(("Goal"
;;           :smtlink
;;           (:functions ((x^2+y^2-integer :formals ((x integerp)
;;                                                   (y integerp))
;;                                         :returns ((f integerp
;;                                                      :name
;;                                                      integerp-of-x^2+y^2-integer))
;;                                         :expansion-depth 1)) )))
;;   :rule-classes nil)


;; (local (in-theory (enable integer-list-fix integer-list-cdr
;;                           integer-list-cons integer-list-car
;;                           integer-list-nil)))

;; (def-saved-event fty-deflist-theorem-example
;;   (defthm fty-deflist-theorem
;;     (implies (and (integer-list-p l)
;;                   (not (equal l (integer-list-nil)))
;;                   (not (equal (integer-list-cdr l) (integer-list-nil))))
;;              (>= (x^2+y^2-integer (integer-list-car l)
;;                                   (integer-list-car (integer-list-cdr l)))
;;                  0))
;;     :hints(("Goal"
;;             :smtlink
;;             (:functions ((x^2+y^2-integer :formals ((x integerp)
;;                                                     (y integerp))
;;                                           :returns ((f integerp
;;                                                        :name
;;                                                        integerp-of-x^2+y^2-integer))
;;                                           :expansion-depth 1)) )))
;;     :rule-classes nil))

;; (acl2::must-fail
;; (defthm fty-deflist-theorem-fail
;;   (implies (and (integer-list-p l)
;;                 (not (equal l (integer-list-nil)))
;;                 (not (equal (integer-list-cdr l) (integer-list-nil))))
;;            (>= (x^2+y^2-integer (integer-list-car l)
;;                                 (integer-list-car (integer-list-cdr l)))
;;                1))
;;   :hints(("Goal"
;;           :smtlink
;;           (:functions ((x^2+y^2-integer :formals ((x integerp)
;;                                                   (y integerp))
;;                                         :returns ((f integerp
;;                                                      :name
;;                                                      integerp-of-x^2+y^2-integer))
;;                                         :expansion-depth 1)) )))
;;   :rule-classes nil)
;; )

;; (def-saved-event sandwich-example
;;   (defprod sandwich
;;     ((bread integerp)
;;      (fillings symbolp)))
;;   )

;; (defsmtprod sandwich
;;   :rec sandwich-p
;;   :fix sandwich-fix
;;   :fix-thm sandwich-fix-when-sandwich-p
;;   :constructor (sandwich sandwich-p)
;;   :destructors ((sandwich->bread$inline integerp)
;;                 (sandwich->fillings$inline symbolp))
;;   )

;; (def-saved-event fty-defprod-theorem-example
;;   (defthm fty-defprod-theorem
;;     (implies (and (sandwich-p s1)
;;                   (sandwich-p s2))
;;              (>= (x^2+y^2-integer
;;                   (sandwich->bread s1)
;;                   (sandwich->bread s2))
;;                  0))
;;     :hints(("Goal"
;;             :smtlink
;;             (:functions ((x^2+y^2-integer :formals ((x integerp)
;;                                                     (y integerp))
;;                                           :returns ((f integerp
;;                                                        :name
;;                                                        integerp-of-x^2+y^2-integer))
;;                                           :expansion-depth 1)))))
;;     :rule-classes nil)
;;   )

;; (acl2::must-fail
;; (defthm fty-defprod-theorem-fail
;;   (implies (and (sandwich-p s1)
;;                 (sandwich-p s2))
;;            (>= (x^2+y^2-integer
;;                 (sandwich->bread s1)
;;                 (sandwich->bread s2))
;;                1))
;;   :hints(("Goal"
;;           :smtlink
;;           (:functions ((x^2+y^2-integer :formals ((x integerp)
;;                                                   (y integerp))
;;                                         :returns ((f integerp
;;                                                      :name
;;                                                      integerp-of-x^2+y^2-integer))
;;                                         :expansion-depth 1)))))
;;   :rule-classes nil)
;; )

;; (defsmtoption maybe-integer
;;   :rec maybe-integer-p
;;   :fix maybe-integer-fix$inline
;;   :fix-thm maybe-integer-fix-when-maybe-integer-p
;;   :some-constructor maybe-integer-some
;;   :some-destructor maybe-integer-some->val$inline
;;   :none-constructor maybe-integer-none
;;   :some-type integerp
;;   )

;; (def-saved-event x^2+y^2-fixed-example
;;   (define x^2+y^2-fixed ((x maybe-integer-p)
;;                          (y maybe-integer-p))
;;     :returns (res maybe-integer-p)
;;     (b* ((x (maybe-integer-fix x))
;;          (y (maybe-integer-fix y))
;;          ((if (equal x (maybe-integer-none)))
;;           (maybe-integer-none))
;;          ((if (equal y (maybe-integer-none)))
;;           (maybe-integer-none)))
;;       (maybe-integer-some
;;        (+ (* (maybe-integer-some->val x)
;;              (maybe-integer-some->val x))
;;           (* (maybe-integer-some->val y)
;;              (maybe-integer-some->val y))))))
;;   )

;; (def-saved-event fty-defoption-theorem-example
;;   (defthm fty-defoption-theorem
;;     (implies (and (maybe-integer-p m1)
;;                   (maybe-integer-p m2)
;;                   (not (equal m1 (maybe-integer-none)))
;;                   (not (equal m2 (maybe-integer-none))))
;;              (>= (maybe-integer-some->val (x^2+y^2-fixed m1 m2))
;;                0))
;;     :hints(("Goal"
;;             :smtlink
;;             (:functions ((x^2+y^2-fixed :formals ((x maybe-integer-p)
;;                                                   (y maybe-integer-p))
;;                                         :returns ((res maybe-integer-p
;;                                                        :name
;;                                                        maybe-integer-p-of-x^2+y^2-fixed))
;;                                         :expansion-depth 1)))))
;;     :rule-classes nil)
;;   )

;; (acl2::must-fail
;; (defthm fty-defoption-theorem-fail
;;   (implies (and (maybe-integer-p m1)
;;                 (maybe-integer-p m2)
;;                 (not (equal m1 (maybe-integer-none)))
;;                 (not (equal m2 (maybe-integer-none))))
;;            (>= (maybe-integer-some->val (x^2+y^2-fixed m1 m2))
;;                1))
;;   :hints(("Goal"
;;           :smtlink
;;           (:functions ((x^2+y^2-fixed :formals ((x maybe-integer-p)
;;                                                 (y maybe-integer-p))
;;                                       :returns ((res maybe-integer-p
;;                                                      :name
;;                                                      maybe-integer-p-of-x^2+y^2-fixed))
;;                                       :expansion-depth 1)))))
;;   :rule-classes nil)
;; )

;; (deftagsum arithtm
;;   (:num ((val integerp)))
;;   (:plus ((left arithtm-p)
;;           (right arithtm-p)))
;;   (:minus ((arg arithtm-p))))

;; (defsmtsum arithtm
;;   :rec arithtm-p
;;   :fix arithtm-fix
;;   :fix-thm arithtm-fix-when-arithtm-p
;;   :kind-function arithtm-kind$inline
;;   :prods ((:num :constructor (arithtm-num arithtm-p return-type-of-arithtm-num)
;;                 :destructors ((arithtm-num->val$inline integerp)))
;;           (:plus :constructor (arithtm-plus arithtm-p return-type-of-arithtm-plus)
;;                  :destructors ((arithtm-plus->left$inline arithtm-p)
;;                                (arithtm-plus->right$inline arithtm-p)))
;;           (:minus :constructor (arithtm-minus arithtm-p)
;;                   :destructors ((arithtm-minus->arg$inline arithtm-p))))
;;   )

;; (defthm fty-deftagsum-theorem
;;   (implies (and (arithtm-p x)
;;                 (equal (arithtm-kind x) :num))
;;            (>= (x^2+y^2-integer (arithtm-num->val x)
;;                                 (arithtm-num->val x))
;;                0))
;;   :hints(("Goal"
;;           :smtlink
;;           (:functions ((x^2+y^2-integer :formals ((x integerp)
;;                                                   (y integerp))
;;                                         :returns ((f integerp
;;                                                      :name
;;                                                      integerp-of-x^2+y^2-integer))
;;                                         :expansion-depth 1)))))
;;   :rule-classes nil)

;; (def-saved-event symbol-integer-example
;;   (defalist symbol-integer-alist
;;     :key-type symbolp
;;     :val-type integerp
;;     :true-listp t)
;;   )

;; (def-saved-event fty-defalist-theorem-example
;;   (defthm fty-defalist-theorem
;;     (implies (and (symbol-integer-alist-p l)
;;                   (symbolp s1)
;;                   (symbolp s2)
;;                   (not (equal (assoc-equal s1 (symbol-integer-alist-fix l))
;;                               (smt::magic-fix 'symbolp_integerp nil)))
;;                   (not (equal (assoc-equal s2 (symbol-integer-alist-fix l))
;;                               (smt::magic-fix 'symbolp_integerp nil))))
;;              (>= (x^2+y^2-integer
;;                   (cdr (smt::magic-fix 'symbolp_integerp
;;                                        (assoc-equal s1 (symbol-integer-alist-fix l))))
;;                   (cdr (smt::magic-fix 'symbolp_integerp
;;                                        (assoc-equal s2 (symbol-integer-alist-fix l)))))
;;                  0))
;;     :hints(("Goal"
;;             :smtlink
;;             (:fty (symbol-integer-alist)
;;                   :functions ((x^2+y^2-integer :formals ((x integerp)
;;                                                          (y integerp))
;;                                                :returns ((f integerp
;;                                                             :meta-extract-thms
;;                                                             (integerp-of-x^2+y^2-integer
;;                                                              ifix-when-integerp)))
;;                                                :level 1)))))
;;     :rule-classes nil)
;;   )

;; (defthm assoc-equal-of-symbol-integer-alist-p
;;   (implies (and (symbol-integer-alist-p l)
;;                 (assoc-equal s l))
;;            (and (consp (assoc-equal s l))
;;                 (integerp (cdr (assoc-equal s l))))))

;; (define x^2+y^2-integer-consp ((s1 symbolp)
;;                                (s2 symbolp)
;;                                (l symbol-integer-alist-p))
;;   :returns (res integerp)
;;   (b* ((l (symbol-integer-alist-fix l))
;;        ((if (equal (assoc-equal s1 (symbol-integer-alist-fix l))
;;                    (smt::magic-fix 'symbolp_integerp nil)))
;;         0)
;;        ((if (equal (assoc-equal s2 (symbol-integer-alist-fix l))
;;                    (smt::magic-fix 'symbolp_integerp nil)))
;;         1)
;;        (x1 (cdr (smt::magic-fix 'symbolp_integerp
;;                                 (assoc-equal s1 (symbol-integer-alist-fix
;;                                                  l)))))
;;        (x2 (cdr (smt::magic-fix 'symbolp_integerp
;;                                 (assoc-equal s2 (symbol-integer-alist-fix
;;                                l))))))
;;     (x^2+y^2-integer x1 x2)))

;; (def-saved-event fty-defalist-theorem-example-consp
;;   (defthm fty-defalist-theorem-consp
;;     (implies (and (symbol-integer-alist-p l)
;;                   (symbolp s1)
;;                   (symbolp s2))
;;              (>= (x^2+y^2-integer-consp s1 s2 l) 0))
;;     :hints(("Goal"
;;             :smtlink
;;             (:fty (symbol-integer-alist)
;;                   :functions ((x^2+y^2-integer :formals ((x integerp)
;;                                                          (y integerp))
;;                                                :returns ((f integerp
;;                                                             :meta-extract-thms
;;                                                             (integerp-of-x^2+y^2-integer
;;                                                              ifix-when-integerp)))
;;                                                :level 1)
;;                               (x^2+y^2-integer-consp :formals ((s1 symbolp)
;;                                                                (s2 symbolp)
;;                                                                (l symbol-integer-alist-p))
;;                                                      :returns ((f integerp
;;                                                                   :meta-extract-thms
;;                                                                   (integerp-of-x^2+y^2-integer-consp
;;                                                                    ifix-when-integerp)))
;;                                                      :level 1)))))
;;     :rule-classes nil)
;;   )


;; (defthm fty-defalist-theorem-acons
;;   (implies (and (symbol-integer-alist-p l)
;;                 (symbolp s1)
;;                 (symbolp s2)
;;                 (not (equal (assoc-equal s1 (symbol-integer-alist-fix
;;                                              (acons 'x 1
;;                                                     (symbol-integer-alist-fix l))))
;;                             (smt::magic-fix 'symbolp_integerp nil)))
;;                 (not (equal (assoc-equal s2 (symbol-integer-alist-fix l))
;;                             (smt::magic-fix 'symbolp_integerp nil))))
;;            (>= (x^2+y^2-integer
;;                 (cdr (smt::magic-fix
;;                       'symbolp_integerp
;;                       (assoc-equal s1 (symbol-integer-alist-fix
;;                                        (acons 'x 1
;;                                               (symbol-integer-alist-fix l))))))
;;                 (cdr (smt::magic-fix 'symbolp_integerp
;;                                      (assoc-equal s2 (symbol-integer-alist-fix l)))))
;;                0))
;;   :hints(("Goal"
;;           :smtlink
;;           (:fty (symbol-integer-alist)
;;                 :functions ((x^2+y^2-integer :formals ((x integerp)
;;                                                        (y integerp))
;;                                              :returns ((f integerp
;;                                                           :meta-extract-thms
;;                                                           (integerp-of-x^2+y^2-integer
;;                                                            ifix-when-integerp)))
;;                                              :level 1)))))
;;   :rule-classes nil)

;; (acl2::must-fail
;; (defthm fty-defalist-theorem-fail
;;   (implies (and (symbol-integer-alist-p l)
;;                 (symbolp s1)
;;                 (symbolp s2)
;;                 (not (equal (assoc-equal s1 (symbol-integer-alist-fix l))
;;                             (smt::magic-fix 'symbolp_integerp nil)))
;;                 (not (equal (assoc-equal s2 (symbol-integer-alist-fix l))
;;                             (smt::magic-fix 'symbolp_integerp nil))))
;;            (>= (x^2+y^2-integer
;;                 (cdr (smt::magic-fix 'symbolp_integerp
;;                                      (assoc-equal s1 (symbol-integer-alist-fix l))))
;;                 (cdr (smt::magic-fix 'symbolp_integerp
;;                                      (assoc-equal s2 (symbol-integer-alist-fix l)))))
;;                1))
;;   :hints(("Goal"
;;           :smtlink
;;           (:fty (symbol-integer-alist)
;;                 :functions ((x^2+y^2-integer :formals ((x integerp)
;;                                                        (y integerp))
;;                                              :returns ((f integerp
;;                                                           :meta-extract-thms
;;                                                           (integerp-of-x^2+y^2-integer
;;                                                            ifix-when-integerp)))
;;                                              :level 1)))))
;;   :rule-classes nil)
;; )

;; (acl2::must-fail
;; (defthm bogus-revised
;;   (implies (and (symbolp symx) (symbolp symy))
;;            (or (equal (symbol-fix symx) 'sym1) (equal (symbol-fix symx) 'sym2)
;;                (equal (symbol-fix symx) 'sym3)
;;                (equal (symbol-fix symy) 'sym1) (equal (symbol-fix symy) 'sym2)
;;                (equal (symbol-fix symy) 'sym3)
;;                (equal (symbol-fix symx)
;;                       (symbol-fix symy))))
;;   :hints (("Goal" :smtlink nil)))
;; )

;; (acl2::must-fail
;; (defthm bogus-revised-still-bogus
;;   (implies (and (symbolp symx) (symbolp symy))
;;            (or (equal symx 'symx) (equal symx 'sym2)
;;                (equal symx 'sym3)
;;                (equal symy 'symx) (equal symy 'sym2)
;;                (equal symy 'sym3)
;;                (equal symx symy)))
;;   :hints (("Goal" :smtlink nil)))
;; )

;; (defprod sym-prod
;;   ((sym symbolp)))

;; (acl2::must-fail
;; (defthm bogus-revised-still-bogus-prod
;;   (implies (and (sym-prod-p x) (sym-prod-p y))
;;            (or (equal (sym-prod->sym x) 'sym1) (equal (sym-prod->sym x) 'sym2)
;;                (equal (sym-prod->sym x) 'sym3)
;;                (equal (sym-prod->sym y) 'sym1) (equal (sym-prod->sym y) 'sym2)
;;                (equal (sym-prod->sym y) 'sym3)
;;                (equal (sym-prod->sym x) (sym-prod->sym y))))
;;   :hints (("Goal" :smtlink (:fty (sym-prod)))))
;; )

;; (acl2::must-fail
;;  (defthm check-guard
;;    (implies (acl2::integer-listp x)
;;             (equal (1+ (1- (car (acl2::integer-list-fix x))))
;;                    (car (acl2::integer-list-fix x))))
;;    :hints (("Goal" :smtlink (:fty (acl2::integer-list)))))
;; )

;; (acl2::must-fail
;;  (defthm check-guard-2
;;    (implies (and (symbol-integer-alist-p l)
;;                  (symbolp x))
;;             (equal (1+ (1- (cdr
;;                             (magic-fix 'symbolp_integerp
;;                                        (assoc-equal x (symbol-integer-alist-fix
;;                                                        l))))))
;;                    (cdr (magic-fix 'symbolp_integerp
;;                                    (assoc-equal x (symbol-integer-alist-fix l))))))
;;    :hints (("Goal" :smtlink (:fty (symbol-integer-alist)))))
;;  )

;; (defthm check-guard-3
;;   (implies (maybe-integer-p x)
;;            (equal (1+ (1- (maybe-integer-some->val
;;                            (maybe-integer-fix x))))
;;                   (maybe-integer-some->val
;;                    (maybe-integer-fix x))))
;;   :hints (("Goal" :smtlink (:fty (maybe-integer))))
;;   )

;; (acl2::must-fail
;;  (defthm check-guard-3-fail
;;    (implies (maybe-integer-p x)
;;             (equal (1+ (1- (maybe-integer-fix x)))
;;                    (maybe-integer-fix x)))
;;    :hints (("Goal" :smtlink (:fty (maybe-integer))))
;;    )
;;  )

;; (acl2::must-fail
;; (defthm check-rational-cex
;;   (implies (rationalp x)
;;            (not (equal x 1/4)))
;;   :hints (("Goal" :smtlink (:fty (maybe-integer))))
;;   )
;; )

;; (acl2::must-fail
;;  (defthm check-boolean-cex
;;    (implies (booleanp x)
;;             (not (equal x nil)))
;;    :hints (("Goal" :smtlink (:fty (maybe-integer))))
;;    )
;;  )

;; (acl2::must-fail
;;  (defthm check-symbol-cex
;;    (implies (symbolp x)
;;             (not (equal x 'arbitrary-sym)))
;;    :hints (("Goal" :smtlink (:fty (maybe-integer))))
;;    )
;;  )

;; ;; algebraic counter-example example by Carl Kwan
;; (acl2::must-fail
;; (defthm poly-sat-7
;;   (implies (and (real/rationalp x)
;;                 (equal (* (+ x -1) (+ x 1) (+ x 2)) 0)
;;                 (< x 0)
;;                 (real/rationalp y)
;;                 (equal (* y y) 2))
;;            (and (equal x -1)
;;                 (< y 0)))
;;   :rule-classes nil
;;   :hints (("Goal"
;; 		       :smtlink nil)))
;; )

;; (deftutorial FTY-examples
;;   :parents (Tutorial)
;;   :short "A list of FTY examples"
;;   :long "<h3>FTY examples</h3>
;; <p>Prerequisite read for this tutorial example is @(tsee tutorial).</p>
;; <p>Smtlink supports types defined by @(tsee acl2::FTY) macros @(tsee defprod), @(tsee
;;   deflist), @(tsee defalist) and @(tsee defoption). We show here an example for
;;   each type.</p>

;; <h4>defprod</h4>
;; <p>Define the function @('x^2+y^2')</p>
;; @(`(:code ($ ||x^2+y^2||))`)

;; <p>Define the defprod @('sandwich')</p>
;; @(`(:code ($ sandwich))`)

;; <p>Then define the theorem to prove:</p>
;; @(`(:code ($ fty-defprod-theorem-example))`)

;; <p>This theorem says, given two @('sandwich-p'), then the square sum of the
;; bread field of the two sandwiches should be non-negative. This example doesn't
;; quite make sense.  Here we use this as an example to show how @('defprod')
;; defined types can be used in a theorem to be discharged by Smtlink.</p>

;; <p>We notice the @(':fty') hint is used to tell Smtlink which set of FTY types
;; we will use in proving this theorem. Here, we use the FTY type
;; @('sandwich'). Smtlink will check @('fty::flextypes-table') for information
;; about this FTY type.</p>

;; <p>Counter-examples for defprods like like:</p>
;; @({
;; Possible counter-example found:
;; ((S2 (SANDWICH 0 (SYM 2))) (S1 (SANDWICH 0 (SYM 1))))
;; })


;; <h4>deflist</h4>
;; <p>Define the theorem to prove:</p>
;; @(`(:code ($ fty-deflist-theorem-example))`)

;; <p>This theorem says, given a list of integers, if there are at least two
;; elements, then the square sum of the two elements should be non-negative.</p>

;; <p>First, Smtlink only allows types defined by deflist that are @(tsee
;; true-listp).  We notice the @(':fty') hint is used to tell Smtlink which set of
;; FTY types we will use in proving this theorem. Here, we use the FTY type
;; @('acl2::integer-list'). Smtlink will check @('fty::flextypes-table') to make
;; sure the given deflist type is a true-listp.</p>

;; <p>Second, we notice extra fixing functions @(tsee acl2::integer-list-fix)
;; functions are added. This is because Z3 lists are typed. The polymorphic
;; functions like @('car') when translated into Z3, also become typed. Therefore
;; we need to inference which @('car') we want to apply here. Currently Smtlink
;; doesn't have type inference ability, therefore it requires the user to add
;; fixing functions for telling it the types.</p>

;; <p>Counter-examples for deflists like like:</p>
;; @({
;; Possible counter-example found: ((L (CONS 0 (CONS 0 NIL))))
;; })

;; <h4>defalist</h4>
;; <p>Define the defalist @('symbol-integer-alist')</p>
;; @(`(:code ($ symbol-integer-example))`)

;; <p>Then define the theorem to prove:</p>
;; @(`(:code ($ fty-defalist-theorem-example))`)

;; <p>This theorem says, given a symbol-integer-alist l, two symbols s1 and s2, if
;; one can find both s1 and s2 in the alist l, then the values satisfy that their
;; square sum is non-negative. I hope the square sum example hasn't bored you yet
;; at this point.</p>

;; <p>Similar to deflists, we notice extra fixing functions
;; @('symbol-integer-alist-fix') functions are added due to similar reasons. In
;; addition, we notice ACL2 doesn't have a type specification for the thing
;; returned by an assoc-equal. To make sure @('cdr') knows what its argument type
;; is, we add a @('magic-fix') function.</p>

;; <p>Counter-examples for defalists like like:</p>
;; @({
;; ((S2 (SYM 2)) (L (K SYMBOL (SOME 0))) (S1 (SYM 1)))
;; })

;; <p>Here, the counter-example for alist l is</p>
;;  @({(K SYMBOL (SOME 0))})
;; <p>This means in Z3 a constant array mapping from symbols to the maybe integer
;;  0. Also, @('SYM') stands for generated symbols for symbol
;;  counter-examples.</p>

;; <h4>defoption</h4>
;; <p>Define the defoption @('maybe-integer')</p>
;; @(`(:code ($ maybe-integer-example))`)

;; <p>Define the fixed version of @('x^2+y^2')</p>
;; @(`(:code ($ x^2+y^2-fixed-example))`)

;; <p>Then define the theorem to prove:</p>
;; @(`(:code ($ fty-defoption-theorem-example))`)

;; <p>This theorem says, given a maybe-integer m1 and a maybe-integer m2, if they
;; are not nils, then the square sum of their values is non-negative.</p>

;; <p>Similar to deflists and defalists, we notice extra fixing functions
;; @('maybe-integer-fix') functions are added due to similar reasons. In addition,
;; we notice in definition of function @('x^2+y^2-fixed'), even when one knows x
;; and y are not nil, they are still maybe-integers. Therefore, field-accessors
;; and constructors are required.</p>

;; <p>Counter-examples for defalists like like:</p>
;; @({
;; Possible counter-example found: ((M2 (SOME 0)) (M1 (SOME 0)))
;; })

;; ")

;; (defthm poly-ineq-example-with-prog2$
;;   (implies (and (real/rationalp x) (real/rationalp y)
;;                 (<= (+ (* (/ 9 8) x x) (* y y)) 1)
;;                 (<= (prog2$ (cw "I'm here!~%")
;;                             (x^2-y^2 x y))
;;                     1))
;;            (< y (- (* 3 (- x (/ 17 8)) (- x (/ 17 8))) 3)))
;;   :hints(("Goal"
;;           :smtlink
;;           (:functions ((x^2-y^2 :formals ((x real/rationalp)
;;                                           (y real/rationalp))
;;                                 :returns ((f real/rationalp
;;                                              :meta-extract-thms
;;                                              (real/rationalp-of-x^2-y^2
;;                                               realfix-when-real/rationalp)))
;;                                 :level 1))))))
