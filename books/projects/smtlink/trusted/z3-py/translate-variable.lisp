;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (11th October, 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "../../verified/hint-interface")
(include-book "datatypes")

(local (in-theory (enable string-or-symbol-p paragraph-p word-p)))

(define translate-variable ((sym string-or-symbol-p))
  :returns (translated paragraph-p)
  (str::downcase-string (lisp-to-python-names sym)))

(define translate-function-name ((fn symbolp)
                                 (trusted-hint trusted-hint-p))
  :returns (mv (translated-fn paragraph-p)
               (to-const? booleanp))
  (b* ((fn (symbol-fix fn))
       (trusted-hint (trusted-hint-fix trusted-hint))
       ((trusted-hint th) trusted-hint)
       (exists? (assoc-equal fn th.user-fns))
       ((unless exists?)
        (prog2$ (er hard? 'translate=>translate-function-name
                    "Unrecognized function ~p0, consider adding it to the ~
                     hint.~%" fn)
                (mv nil nil)))
       ((smt-function f) (cdr exists?))
       ((trans-hint h) f.translation-hint)
       ((if (equal f.kind :basic)) (mv h.translation nil))
       ((if (not (equal h.type "")))
        (mv `(,(translate-variable h.type) "."
              ,(translate-variable h.translation))
            h.fn-to-const)))
    (mv (translate-variable h.translation) nil)))
