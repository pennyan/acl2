;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (Oct 7th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "extract-options")
(include-book "extractor")

(define filter-hypo-list ((hypo-lst pseudo-term-listp)
                          (options extract-options-p))
  :returns (new-hypo pseudo-term-listp)
  :measure (len hypo-lst)
  (b* ((hypo-lst (pseudo-term-list-fix hypo-lst))
       (options (extract-options-fix options))
       ((extract-options o) options)
       ((unless (consp hypo-lst)) nil)
       ((cons hypo-hd hypo-tl) hypo-lst)
       ((if (and (type-predicate-p hypo-hd o.acl2type)
                 (not (type-predicate-p hypo-hd o.datatype))))
        (filter-hypo-list hypo-tl o)))
    (cons hypo-hd (filter-hypo-list hypo-tl o))))

(defthm correctness-of-filter-hypo-list
  (implies (and (pseudo-term-listp hypo-lst)
                (alistp a)
                (ev-smtcp (conjoin hypo-lst) a))
           (ev-smtcp (conjoin (filter-hypo-list hypo-lst options)) a))
  :hints (("Goal" :in-theory (enable filter-hypo-list))))

(define type-extract-cp ((cl pseudo-term-listp)
                         (smtlink-hint t))
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* ((cl (pseudo-term-list-fix cl))
       ((unless (smtlink-hint-p smtlink-hint)) (list cl))
       (goal (disjoin cl))
       (options (construct-extract-options smtlink-hint))
       ((extract-options o) options)
       ((mv hypo-lst new-term) (extractor goal o.alltype))
       ((mv okp & term-body)
        (case-match new-term
          (('if judges term-body ''t)
           (mv t judges term-body))
          (('implies judges term-body)
           (mv t judges term-body))
          (& (mv nil nil nil))))
       ((unless okp)
        (prog2$ (er hard? 'type-extract=>type-extract-fn
                    "The input term is of wrong shape.~%")
                (list cl)))
       (new-hypo-lst (filter-hypo-list hypo-lst options))
       (type-hyp-list `(type-hyp ,(conjoin new-hypo-lst) ':type))
       (new-goal `(if ,type-hyp-list ,term-body 't))
       (next-cp (cdr (assoc-equal 'type-extract *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',smtlink-hint state)))
       (hinted-goal `((hint-please ',the-hint) ,new-goal)))
    (list hinted-goal)))

(defthm correctness-of-type-extract-cp-lemma
  (implies (and (pseudo-termp term)
                (symbol-symbol-alistp type-info)
                (alistp a))
           (b* (((mv hypo-lst new-term) (extractor term type-info))
                (new-hypo-lst (filter-hypo-list hypo-lst options)))
             (implies (ev-smtcp `(if (type-hyp ,(conjoin new-hypo-lst) ':type) ,new-term 't) a)
                      (ev-smtcp term a))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (type-hyp) (correctness-of-extractor))
           :use ((:instance correctness-of-extractor)))))

(defthm correctness-of-type-extract-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (type-extract-cp cl hint))
                 a))
           (ev-smtcp (disjoin cl) a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (type-extract-cp)
                           (correctness-of-type-extract-cp-lemma))
           :use ((:instance correctness-of-type-extract-cp-lemma
                            (term (disjoin cl))
                            (options (construct-extract-options hint))
                            (type-info (extract-options->alltype
                                        (construct-extract-options hint)))))))
  :rule-classes :clause-processor)
