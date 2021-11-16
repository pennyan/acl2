;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (19th October, 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(define exactly-one-helper ((lst boolean-listp)
                            (count natp))
  :returns (new-count natp)
  :measure (len lst)
  (b* ((lst (acl2::boolean-list-fix lst))
       (count (nfix count))
       ((unless (consp lst)) count)
       ((cons lst-hd lst-tl) lst)
       ((if lst-hd) (exactly-one-helper lst-tl (1+ count))))
    (exactly-one-helper lst-tl count)))

(define exactly-one ((lst boolean-listp))
  :returns (okp booleanp)
  (b* ((lst (acl2::boolean-list-fix lst))
       (count (exactly-one-helper lst 0))
       ((if (equal count 1)) t))
    nil))

(in-theory (enable exactly-one exactly-one-helper))
