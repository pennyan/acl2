(TMP-DEFTYPES-INTEGERP-OF-IFIX)
(TMP-DEFTYPES-IFIX-WHEN-INTEGERP)
(SYNDEF::|positive2-P|
 (361 19 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (352 12 (:REWRITE ALISTP-OF-CDR))
 (217 22 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (190 10 (:REWRITE STRIP-CARS-WHEN-ATOM))
 (181 29 (:REWRITE DEFAULT-CAR))
 (152 22 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (116 46 (:REWRITE SYNTACTIC-EXPLICIT-TRUE-LISTP-FORWARD-TO-CONSP))
 (95 19 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (95 19 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (86 86 (:TYPE-PRESCRIPTION SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P))
 (86 86 (:TYPE-PRESCRIPTION SYNTHETO::TYPE-REF-CONSTRUCTOR-P))
 (86 36 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP))
 (86 36 (:REWRITE SYNTHETO::TYPE-REF-CONSTRUCTOR-P-IMPLIES-CONSP))
 (76 76 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (70 70 (:TYPE-PRESCRIPTION SYNTACTIC-EXPLICIT-TRUE-LISTP))
 (65 29 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (65 29 (:REWRITE SYNTHETO::CONSP-CDR-IF-TYPE-REF-CONSTRUCTOR-P))
 (65 29 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (63 35 (:REWRITE DEFAULT-CDR))
 (57 19 (:REWRITE SYNTHETO::MAPP-WHEN-VARIABLE-SUBSTITUTIONP))
 (57 19 (:REWRITE SYNTHETO::MAPP-WHEN-VARIABLE-CONTEXTP))
 (50 50 (:TYPE-PRESCRIPTION SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (46 46 (:REWRITE APT::CONSP-WHEN-MEMBER-EQUAL-OF-ISODATA-SYMBOL-ISOMAP-ALISTP . 2))
 (46 46 (:REWRITE APT::CONSP-WHEN-MEMBER-EQUAL-OF-ISODATA-SYMBOL-ISOMAP-ALISTP . 1))
 (46 46 (:REWRITE APT::CONSP-WHEN-MEMBER-EQUAL-OF-ISODATA-POS-ISOMAP-ALISTP . 2))
 (46 46 (:REWRITE APT::CONSP-WHEN-MEMBER-EQUAL-OF-ISODATA-POS-ISOMAP-ALISTP . 1))
 (43 43 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (38 38 (:TYPE-PRESCRIPTION SYNTHETO::VARIABLE-SUBSTITUTIONP))
 (38 38 (:TYPE-PRESCRIPTION SYNTHETO::VARIABLE-CONTEXTP))
 (38 38 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (38 38 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (38 19 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (38 19 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (38 19 (:REWRITE ALISTP-WHEN-VAR-UNTRANSLATED-TERM-PAIRSP-CHEAP))
 (38 19 (:REWRITE ALISTP-WHEN-PSEUDO-TERM-ALISTP-CHEAP))
 (38 19 (:REWRITE ALISTP-WHEN-PAIR-LISTP-CHEAP))
 (38 19 (:REWRITE ALIST-WHEN-UNTRANSLATED-TERM-PAIRSP-CHEAP))
 (22 8 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDDR))
 (19 19 (:TYPE-PRESCRIPTION VAR-UNTRANSLATED-TERM-PAIRSP))
 (19 19 (:TYPE-PRESCRIPTION UNTRANSLATED-TERM-PAIRSP))
 (19 19 (:TYPE-PRESCRIPTION PSEUDO-TERM-ALISTP))
 (19 19 (:TYPE-PRESCRIPTION PAIR-LISTP))
 (2 1 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 )
(SYNDEF::|CONSP-WHEN-positive2-P|)
(SYNDEF::|TAG-WHEN-positive2-P|)
(SYNDEF::|positive2-P-WHEN-WRONG-TAG|)
(SYNDEF::|positive2-FIX$INLINE|)
(SYNDEF::|positive2-P-OF-positive2-FIX|
 (6 6 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 )
(SYNDEF::|positive2-FIX-WHEN-positive2-P|
 (2 2 (:DEFINITION STRIP-CARS))
 )
(SYNDEF::|positive2-FIX$INLINE|
 (2 2 (:DEFINITION STRIP-CARS))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(SYNDEF::|positive2-EQUIV$INLINE|)
(SYNDEF::|positive2-EQUIV-IS-AN-EQUIVALENCE|)
(SYNDEF::|positive2-EQUIV-IMPLIES-EQUAL-positive2-FIX-1|)
(SYNDEF::|positive2-FIX-UNDER-positive2-EQUIV|)
(SYNDEF::|EQUAL-OF-positive2-FIX-1-FORWARD-TO-positive2-EQUIV|)
(SYNDEF::|EQUAL-OF-positive2-FIX-2-FORWARD-TO-positive2-EQUIV|)
(SYNDEF::|positive2-EQUIV-OF-positive2-FIX-1-FORWARD|)
(SYNDEF::|positive2-EQUIV-OF-positive2-FIX-2-FORWARD|)
(SYNDEF::|TAG-OF-positive2-FIX|)
(SYNDEF::|positive2->y$INLINE|
 (2 2 (:DEFINITION STRIP-CARS))
 )
(SYNDEF::|INTEGERP-OF-positive2->y|)
(SYNDEF::|positive2->y$INLINE-OF-positive2-FIX-X|
 (9 3 (:REWRITE SYNDEF::|positive2-FIX-WHEN-positive2-P|))
 (6 6 (:TYPE-PRESCRIPTION SYNDEF::|positive2-P|))
 (6 6 (:TYPE-PRESCRIPTION SYNDEF::|positive2-FIX$INLINE|))
 )
(SYNDEF::|positive2->y$INLINE-positive2-EQUIV-CONGRUENCE-ON-X|)
(SYNDEF::|positive2|)
(SYNDEF::|positive2-P-OF-positive2|
 (3 3 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 )
(SYNDEF::|positive2->y-OF-positive2|
 (6 6 (:TYPE-PRESCRIPTION SYNDEF::|positive2|))
 )
(SYNDEF::|positive2-OF-FIELDS|
 (3 1 (:REWRITE SYNDEF::|positive2-FIX-WHEN-positive2-P|))
 (2 2 (:TYPE-PRESCRIPTION SYNDEF::|positive2-P|))
 )
(SYNDEF::|positive2-FIX-WHEN-positive2|
 (3 1 (:REWRITE SYNDEF::|positive2-FIX-WHEN-positive2-P|))
 (2 2 (:TYPE-PRESCRIPTION SYNDEF::|positive2-P|))
 )
(SYNDEF::|EQUAL-OF-positive2|)
(SYNDEF::|positive2-OF-IFIX-y|)
(SYNDEF::|positive2-INT-EQUIV-CONGRUENCE-ON-y|)
(SYNDEF::|positive2-FIX-REDEF|)
(SYNDEF::|TAG-OF-positive2|)
(SYNDEF::|positive3-P|
 (361 19 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (352 12 (:REWRITE ALISTP-OF-CDR))
 (217 22 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (190 10 (:REWRITE STRIP-CARS-WHEN-ATOM))
 (181 29 (:REWRITE DEFAULT-CAR))
 (152 22 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (116 46 (:REWRITE SYNTACTIC-EXPLICIT-TRUE-LISTP-FORWARD-TO-CONSP))
 (95 19 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (95 19 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (86 86 (:TYPE-PRESCRIPTION SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P))
 (86 86 (:TYPE-PRESCRIPTION SYNTHETO::TYPE-REF-CONSTRUCTOR-P))
 (86 36 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP))
 (86 36 (:REWRITE SYNTHETO::TYPE-REF-CONSTRUCTOR-P-IMPLIES-CONSP))
 (76 76 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (70 70 (:TYPE-PRESCRIPTION SYNTACTIC-EXPLICIT-TRUE-LISTP))
 (65 29 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (65 29 (:REWRITE SYNTHETO::CONSP-CDR-IF-TYPE-REF-CONSTRUCTOR-P))
 (65 29 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (63 35 (:REWRITE DEFAULT-CDR))
 (57 19 (:REWRITE SYNTHETO::MAPP-WHEN-VARIABLE-SUBSTITUTIONP))
 (57 19 (:REWRITE SYNTHETO::MAPP-WHEN-VARIABLE-CONTEXTP))
 (50 50 (:TYPE-PRESCRIPTION SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (46 46 (:REWRITE APT::CONSP-WHEN-MEMBER-EQUAL-OF-ISODATA-SYMBOL-ISOMAP-ALISTP . 2))
 (46 46 (:REWRITE APT::CONSP-WHEN-MEMBER-EQUAL-OF-ISODATA-SYMBOL-ISOMAP-ALISTP . 1))
 (46 46 (:REWRITE APT::CONSP-WHEN-MEMBER-EQUAL-OF-ISODATA-POS-ISOMAP-ALISTP . 2))
 (46 46 (:REWRITE APT::CONSP-WHEN-MEMBER-EQUAL-OF-ISODATA-POS-ISOMAP-ALISTP . 1))
 (43 43 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (38 38 (:TYPE-PRESCRIPTION SYNTHETO::VARIABLE-SUBSTITUTIONP))
 (38 38 (:TYPE-PRESCRIPTION SYNTHETO::VARIABLE-CONTEXTP))
 (38 38 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (38 38 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (38 19 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (38 19 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (38 19 (:REWRITE ALISTP-WHEN-VAR-UNTRANSLATED-TERM-PAIRSP-CHEAP))
 (38 19 (:REWRITE ALISTP-WHEN-PSEUDO-TERM-ALISTP-CHEAP))
 (38 19 (:REWRITE ALISTP-WHEN-PAIR-LISTP-CHEAP))
 (38 19 (:REWRITE ALIST-WHEN-UNTRANSLATED-TERM-PAIRSP-CHEAP))
 (22 8 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDDR))
 (19 19 (:TYPE-PRESCRIPTION VAR-UNTRANSLATED-TERM-PAIRSP))
 (19 19 (:TYPE-PRESCRIPTION UNTRANSLATED-TERM-PAIRSP))
 (19 19 (:TYPE-PRESCRIPTION PSEUDO-TERM-ALISTP))
 (19 19 (:TYPE-PRESCRIPTION PAIR-LISTP))
 (2 1 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 )
(SYNDEF::|CONSP-WHEN-positive3-P|)
(SYNDEF::|TAG-WHEN-positive3-P|)
(SYNDEF::|positive3-P-WHEN-WRONG-TAG|)
(SYNDEF::|positive3-FIX$INLINE|)
(SYNDEF::|positive3-P-OF-positive3-FIX|
 (18 6 (:REWRITE SYNDEF::|positive2-FIX-WHEN-positive2-P|))
 (12 12 (:TYPE-PRESCRIPTION SYNDEF::|positive2-P|))
 )
(SYNDEF::|positive3-FIX-WHEN-positive3-P|
 (2 2 (:DEFINITION STRIP-CARS))
 )
(SYNDEF::|positive3-FIX$INLINE|
 (2 2 (:DEFINITION STRIP-CARS))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(SYNDEF::|positive3-EQUIV$INLINE|)
(SYNDEF::|positive3-EQUIV-IS-AN-EQUIVALENCE|)
(SYNDEF::|positive3-EQUIV-IMPLIES-EQUAL-positive3-FIX-1|)
(SYNDEF::|positive3-FIX-UNDER-positive3-EQUIV|)
(SYNDEF::|EQUAL-OF-positive3-FIX-1-FORWARD-TO-positive3-EQUIV|)
(SYNDEF::|EQUAL-OF-positive3-FIX-2-FORWARD-TO-positive3-EQUIV|)
(SYNDEF::|positive3-EQUIV-OF-positive3-FIX-1-FORWARD|)
(SYNDEF::|positive3-EQUIV-OF-positive3-FIX-2-FORWARD|)
(SYNDEF::|TAG-OF-positive3-FIX|)
(SYNDEF::|positive3->z$INLINE|
 (2 2 (:DEFINITION STRIP-CARS))
 )
(SYNDEF::|positive2-P-OF-positive3->z|)
(SYNDEF::|positive3->z$INLINE-OF-positive3-FIX-X|
 (9 3 (:REWRITE SYNDEF::|positive3-FIX-WHEN-positive3-P|))
 (6 6 (:TYPE-PRESCRIPTION SYNDEF::|positive3-P|))
 )
(SYNDEF::|positive3->z$INLINE-positive3-EQUIV-CONGRUENCE-ON-X|)
(SYNDEF::|positive3|)
(SYNDEF::|positive3-P-OF-positive3|
 (9 3 (:REWRITE SYNDEF::|positive2-FIX-WHEN-positive2-P|))
 (6 6 (:TYPE-PRESCRIPTION SYNDEF::|positive2-P|))
 )
(SYNDEF::|positive3->z-OF-positive3|)
(SYNDEF::|positive3-OF-FIELDS|
 (3 1 (:REWRITE SYNDEF::|positive3-FIX-WHEN-positive3-P|))
 (2 2 (:TYPE-PRESCRIPTION SYNDEF::|positive3-P|))
 )
(SYNDEF::|positive3-FIX-WHEN-positive3|
 (3 1 (:REWRITE SYNDEF::|positive3-FIX-WHEN-positive3-P|))
 (2 2 (:TYPE-PRESCRIPTION SYNDEF::|positive3-P|))
 )
(SYNDEF::|EQUAL-OF-positive3|)
(SYNDEF::|positive3-OF-positive2-FIX-z|)
(SYNDEF::|positive3-positive2-EQUIV-CONGRUENCE-ON-z|)
(SYNDEF::|positive3-FIX-REDEF|)
(SYNDEF::|TAG-OF-positive3|)
