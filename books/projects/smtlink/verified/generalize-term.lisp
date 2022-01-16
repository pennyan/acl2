;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (Feb 3rd 2022)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "typed-term-fns")

;; (define generalize-var-hyp ((hyp pseudo-termp)
;;                             (term pseudo-termp)
;;                             (var symbolp)
;;                             (supertype type-to-types-alist-p))
;;   :returns (new-hyp pseudo-termp)
;;   (b* ((hyp (pseudo-term-fix hyp))
;;        (term (pseudo-term-fix term))
;;        (var (symbol-fix var))
;;        (supertype (type-to-types-alist-fix supertype))
;;        ((if (equal hyp ''t)) hyp)
;;        ((unless (type-predicate-of-term hyp term supertype))
;;         (er hard? 'generalize-term=>generalize-var-hyp
;;             "Hypothesis ~p0 for term ~p1 is not a type-predicate-of-term.~%"
;;             hyp term))
;;        ((mv okp type)
;;         (case-match hyp
;;           ((type !term) (mv t type))
;;           (& (mv nil nil))))
;;        ((unless okp)
;;         (er hard? 'generalize-term=>generalize-var-hyp
;;             "Malformed type hypothesis: ~q0" hyp)))
;;     `(,type ,var)))

(defines generalize-term
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil

  (define generalize-fncall ((term pseudo-termp)
                             (target pseudo-termp)
                             (var symbolp))
    :guard (and (consp term)
                (symbolp (car term))
                (not (equal (car term) 'quote)))
    :returns (new-term pseudo-termp)
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    (b* ((term (pseudo-term-fix term))
         (target (pseudo-term-fix target))
         (var (symbol-fix var))
         ((unless (mbt (and (consp term)
                            (symbolp (car term))
                            (not (equal (car term) 'quote)))))
          term)
         ((cons fn actuals) term)
         (new-actuals (generalize-term-list actuals target var)))
      `(,fn ,@new-actuals)))

  (define generalize-term ((term pseudo-termp)
                           (target pseudo-termp)
                           (var symbolp))
    :returns (new-term pseudo-termp)
    :measure (list (acl2-count (pseudo-term-fix term)) 1)
    (b* ((term (pseudo-term-fix term))
         (target (pseudo-term-fix target))
         (var (symbol-fix var))
         ((if (equal term target)) var)
         ((if (or (acl2::variablep term) (acl2::quotep term))) term)
         ((cons fn &) term)
         ((unless (pseudo-lambdap fn)) (generalize-fncall term target var)))
      (prog2$ (er hard? 'generalize-term=>generalize-term
                  "Found lambda or if in the goal.~%")
              term)))

  (define generalize-term-list ((term-lst pseudo-term-listp)
                                (target pseudo-termp)
                                (var symbolp))
    :returns (new-term-lst pseudo-term-listp)
    :measure (list (acl2-count (pseudo-term-list-fix term-lst)) 1)
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (target (pseudo-term-fix target))
         (var (symbol-fix var))
         ((unless (consp term-lst)) nil)
         ((cons term-hd term-tl) term-lst)
         (first-term (generalize-term term-hd target var))
         (rest-term (generalize-term-list term-tl target var)))
      (cons first-term rest-term)))
  )

(verify-guards generalize-term)
