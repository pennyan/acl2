;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (March 1st 2022)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "kestrel/std/system/macro-symbolp" :dir :system)

(define define-nonexist-fn (name args w)
  (b* (((unless (and (symbolp name) (plist-worldp w)))
        `(value-triple (cw "INTERNAL: ~p0 is not a symbol or ~p1 is not ~
                        plist-worldp.~%" ',name ',w)))
       ((if (or (function-symbolp name w)
                (acl2::macro-symbolp name w)))
        `(value-triple (cw "Warning: ~p0 function already exists.~%" ',name)))
       (event `(define ,name ,@args)))
    event))

(defmacro define-nonexist (name &rest args)
  `(make-event (define-nonexist-fn ',name ',args (w state))))
