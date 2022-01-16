;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (September 22th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "hint-interface")
(include-book "type-options")
(include-book "lambda-substitution")
(include-book "judgement-fns")
(include-book "match-term")

(set-state-ok t)

(defprod replace-options
  ((supertype type-to-types-alist-p)
   (replaces thm-spec-list-p)))

(define find-replaces ((tterm good-typed-term-p)
                       (replaces thm-spec-list-p))
  :returns (lst thm-spec-list-p)
  :measure (len replaces)
  (b* (((unless (mbt (good-typed-term-p tterm))) nil)
       (tterm (typed-term-fix tterm))
       (replaces (thm-spec-list-fix replaces))
       ((unless (consp replaces)) nil)
       ((cons re-hd re-tl) replaces)
       ((thm-spec ts) re-hd)
       (res (match-term tterm ts.lhs nil))
       ((if (equal res :fail)) (find-replaces tterm re-tl)))
    (cons re-hd (find-replaces tterm re-tl))))

(define conjunct-to-list ((judge pseudo-termp)
                          (acc pseudo-term-listp))
  :returns (judge-lst pseudo-term-listp)
  :measure (acl2-count (pseudo-term-fix judge))
  (b* ((judge (pseudo-term-fix judge))
       (acc (pseudo-term-list-fix acc))
       ((if (equal judge ''t)) acc)
       ((unless (is-conjunct? judge)) (cons judge acc))
       ((list* & cond then &) judge))
    (conjunct-to-list then (cons cond acc))))

(local
 (in-theory (disable pseudo-termp pseudo-term-listp
                     consp-of-is-conjunct? assoc-equal symbol-listp
                     pseudo-term-listp-of-symbol-listp)))

(define update-replace ((thm thm-spec-p) state)
  :returns (new-thm thm-spec-p)
  (b* ((thm (thm-spec-fix thm))
       ((thm-spec th) thm)
       (thm-raw (acl2::meta-extract-formula-w th.thm (w state)))
       ((unless (pseudo-termp thm-raw))
        (prog2$ (er hard? 'replace-options=>update-replace
                    "Formula returned by meta-extract ~p0 is not a ~
                     pseudo-termp: ~p1~%" th.thm thm-raw)
                thm))
       (thm-expanded (expand-lambda thm-raw))
       ((mv okp new-thm)
        (case-match thm-expanded
          (('implies hypotheses ('if ('equal lhs rhs)
                                    ('if ('var-term var-term)
                                        ('if ('var-hyp var-hyp)
                                            ('if ('hyp-judge hyp-judge)
                                                judgements
                                              ''nil)
                                          ''nil)
                                      ''nil)
                                  ''nil))
           (mv t (change-thm-spec
                  thm
                  :hypotheses hypotheses
                  :lhs lhs
                  :rhs rhs
                  :judgements
                  (conjunct-to-list judgements nil)
                  :var-term var-term
                  :var-hyp var-hyp
                  :hyp-judge hyp-judge)))
          (('implies hypotheses ('if ('equal lhs rhs) judgements ''nil))
           (mv t (change-thm-spec
                  thm
                  :hypotheses hypotheses
                  :lhs lhs
                  :rhs rhs
                  :judgements
                  (conjunct-to-list judgements nil))))
          (('implies hypotheses ('equal lhs rhs))
           (mv t (change-thm-spec thm
                                  :hypotheses hypotheses
                                  :lhs lhs
                                  :rhs rhs)))
          (& (mv nil thm))))
       ((unless okp)
        (prog2$ (er hard? 'replace-options=>update-replace
                    "Replace theorem is malformed: ~q0" thm-expanded)
                thm)))
    new-thm))

(define update-replace-list ((thms thm-spec-list-p) state)
  :returns (new-thms thm-spec-list-p)
  :measure (len thms)
  (b* ((thms (thm-spec-list-fix thms))
       ((unless (consp thms)) nil)
       ((cons thm-hd thm-tl) thms))
    (cons (update-replace thm-hd state)
          (update-replace-list thm-tl state))))

(define construct-replace-options ((hints smtlink-hint-p) state)
  :returns (type-alst replace-options-p)
  (b* ((hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       ((mv & supertype) (construct-sub/supertype-alist h.acl2types))
       (replace-lst (update-replace-list h.replaces state)))
    (make-replace-options :supertype supertype
                          :replaces replace-lst)))
