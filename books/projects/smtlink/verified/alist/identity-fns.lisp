;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (Feb 8th 2022)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "std/util/top" :dir :system)

;; var-term function
(define var-term ((term))
  (declare (ignore term)
           (xargs :guard t))
  t)

(defthm var-term-forward
  (implies (var-term term) t)
  :rule-classes :forward-chaining)

(in-theory (disable (:d var-term)
                    (:e var-term)
                    (:t var-term)))

;; var-hyp identity function
(define var-hyp ((hyp)) hyp)

(defthm var-hyp-forward
  (implies (var-hyp hyp) hyp)
  :rule-classes :forward-chaining)

(in-theory (disable (:d var-hyp)
                    (:e var-hyp)
                    (:t var-hyp)))

;; hyp-judge identity function
(define hyp-judge ((judge)) judge)

(defthm hyp-judge-forward
  (implies (hyp-judge judge) t)
  :rule-classes :forward-chaining)

(in-theory (disable (:d hyp-judge)
                    (:e hyp-judge)
                    (:t hyp-judge)))
