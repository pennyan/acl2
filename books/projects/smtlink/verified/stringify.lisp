;; Copyright (C) 2015, University of British Columbia
;; Written by Mark Greenstreet (2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/strings/top" :dir :system)
(include-book "std/util/top" :dir :system)

; perhaps I should use acl2::deflist or fty::deflist to define
; stringable-list-p and stringable-list-list-p, but I don't want to choose
; which package to use for this proof-of-concept example.

; stringable-list-p -- a list of things that are "acceptable" for turning
;   into strings that will be interned into symbols by make-symbol.
(define stringable-list-p (x)
  :returns (ok booleanp)
  (if x
      (and (consp x)
	         (or (stringp (car x))
	             (symbolp (car x))
	             (character-listp (car x)))
	         (stringable-list-p (cdr x)))
    t))

; stringable-list-list-p -- a list of stringable-list-p's
(define stringable-list-list-p (x)
  :returns (ok booleanp)
  (if x
      (and (consp x)
	         (stringable-list-p (car x))
	         (stringable-list-list-p (cdr x)))
    t))


; stringify-list -- convert a list of stringable-p values into a list of strings
(define stringify-list ((x stringable-list-p))
  :returns (s string-listp)
  :verify-guards nil
  (b* (((unless (consp x)) nil)
       ((cons hd0 tl) x)
       (hd (acl2::implode
	          (str::upcase-charlist
	           (if (atom hd0)
		             (explode-atom hd0 10)
		           (str::character-list-fix hd0))))))
    (cons hd (stringify-list tl)))
  ///
  (verify-guards stringify-list
    :hints(("Goal" :in-theory (enable stringable-list-p)))))


; mk-symbol -- I first wrote this as make-symbol, but
;   ACL2 Error in ( DEFUN MAKE-SYMBOL ...):  Symbols in the main Lisp package,
;   such as MAKE-SYMBOL, may not be defined or constrained.
; OTOH, :doc, :pe, and :pf have nothing for make-symbol.
(define mk-symbol ((x stringable-list-p) (sym symbolp))
  :returns (s symbolp)
  (intern-in-package-of-symbol
   (str::join (stringify-list x) "-") sym))

(define mk-symbol-list ((x stringable-list-list-p) (sym symbolp))
  :returns (s symbol-listp)
  :guard-hints(("Goal" :in-theory (enable stringable-list-list-p)))
  (if (consp x)
      (cons (mk-symbol (car x) sym) (mk-symbol-list (cdr x) sym))
    nil))
