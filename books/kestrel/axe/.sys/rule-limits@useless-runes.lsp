(ALL-INTEGERP-OF-STRIP-CDRS-OF-ACONS-UNIQUE
 (69 28 (:REWRITE DEFAULT-CDR))
 (45 28 (:REWRITE DEFAULT-CAR))
 (36 18 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (33 17 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (18 18 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (16 16 (:TYPE-PRESCRIPTION STRIP-CDRS))
 )
(RULE-LIMITSP)
(RULE-LIMITSP-FORWARD-TO-ALISTP)
(INTEGERP-OF-CDR-OF-ASSOC-EQUAL-WHEN-RULE-LIMITSP
 (90 24 (:REWRITE DEFAULT-CDR))
 (88 72 (:REWRITE DEFAULT-CAR))
 (58 2 (:REWRITE CONSP-OF-ASSOC-EQUAL))
 (43 3 (:REWRITE RULE-LIMITSP-FORWARD-TO-ALISTP))
 (42 21 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (36 1 (:DEFINITION ALISTP))
 (35 35 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (28 14 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (22 11 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (14 14 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (13 13 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (6 3 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 )
(INTEGERP-OF-CDR-OF-ASSOC-EQUAL-WHEN-RULE-LIMITSP-TYPE
 (90 24 (:REWRITE DEFAULT-CDR))
 (88 72 (:REWRITE DEFAULT-CAR))
 (58 2 (:REWRITE CONSP-OF-ASSOC-EQUAL))
 (43 3 (:REWRITE RULE-LIMITSP-FORWARD-TO-ALISTP))
 (42 21 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (36 1 (:DEFINITION ALISTP))
 (35 35 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (28 14 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (22 11 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (14 14 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (13 13 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (6 3 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 )
(RULE-LIMITSP-OF-ACONS-UNIQUE
 (18 2 (:DEFINITION STRIP-CDRS))
 (15 7 (:REWRITE DEFAULT-CDR))
 (10 7 (:REWRITE DEFAULT-CAR))
 (9 1 (:DEFINITION SYMBOL-ALISTP))
 (8 4 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (7 1 (:DEFINITION ACONS-UNIQUE))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (6 6 (:TYPE-PRESCRIPTION ACONS-UNIQUE))
 (4 2 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (2 1 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION STRIP-CDRS))
 )
(LIMIT-REACHEDP
 (682 7 (:DEFINITION PSEUDO-TERMP))
 (289 7 (:REWRITE PSEUDO-TERMP-OF-STORED-RULE-RHS))
 (198 7 (:REWRITE PSEUDO-TERM-LISTP-OF-STORED-RULE-LHS-ARGS))
 (189 21 (:DEFINITION LENGTH))
 (188 7 (:REWRITE BOUND-VARS-SUITABLE-FOR-HYPSP-OF-VAR-IN-TERMS-OF-STORED-RULE-LHS-ARGS-AND-STORED-RULE-HYPS))
 (185 7 (:REWRITE AXE-RULE-HYP-LISTP-OF-STORED-RULE-HYPS))
 (184 34 (:DEFINITION LEN))
 (174 2 (:REWRITE SYMBOLP-OF-STORED-RULE-SYMBOL))
 (158 146 (:REWRITE DEFAULT-CAR))
 (144 138 (:REWRITE DEFAULT-CDR))
 (138 6 (:DEFINITION SUBSETP-EQUAL))
 (78 14 (:DEFINITION TRUE-LISTP))
 (77 6 (:DEFINITION MEMBER-EQUAL))
 (72 7 (:DEFINITION PSEUDO-TERM-LISTP))
 (68 34 (:REWRITE DEFAULT-+-2))
 (59 48 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (54 27 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (53 7 (:DEFINITION SYMBOL-LISTP))
 (48 48 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (44 22 (:TYPE-PRESCRIPTION BOUND-VARS-AFTER-HYPS))
 (34 34 (:REWRITE DEFAULT-+-1))
 (31 31 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (31 7 (:REWRITE BOUND-VARS-SUITABLE-FOR-HYPSP-WHEN-FREE-VARS))
 (27 27 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (26 26 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (22 22 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERMS))
 (21 21 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (21 21 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (19 7 (:REWRITE BOUND-VARS-SUITABLE-FOR-HYPSP-WHEN-NORMAL))
 (19 7 (:REWRITE BOUND-VARS-SUITABLE-FOR-HYPSP-WHEN-AXE-SYTAXP-CAR))
 (17 17 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (7 7 (:REWRITE DEFAULT-COERCE-2))
 (7 7 (:REWRITE DEFAULT-COERCE-1))
 (6 6 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:REWRITE USE-ALL-STORED-AXE-RULEP-2))
 (5 5 (:REWRITE USE-ALL-STORED-AXE-RULEP))
 (3 3 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (3 2 (:REWRITE DEFAULT-<-2))
 (3 2 (:REWRITE DEFAULT-<-1))
 )
(DECREMENT-RULE-LIMIT
 (7502 77 (:DEFINITION PSEUDO-TERMP))
 (3179 77 (:REWRITE PSEUDO-TERMP-OF-STORED-RULE-RHS))
 (2178 77 (:REWRITE PSEUDO-TERM-LISTP-OF-STORED-RULE-LHS-ARGS))
 (2079 231 (:DEFINITION LENGTH))
 (2068 77 (:REWRITE BOUND-VARS-SUITABLE-FOR-HYPSP-OF-VAR-IN-TERMS-OF-STORED-RULE-LHS-ARGS-AND-STORED-RULE-HYPS))
 (2035 77 (:REWRITE AXE-RULE-HYP-LISTP-OF-STORED-RULE-HYPS))
 (2024 374 (:DEFINITION LEN))
 (1914 22 (:REWRITE SYMBOLP-OF-STORED-RULE-SYMBOL))
 (1875 1611 (:REWRITE DEFAULT-CDR))
 (1855 1723 (:REWRITE DEFAULT-CAR))
 (1518 66 (:DEFINITION SUBSETP-EQUAL))
 (858 154 (:DEFINITION TRUE-LISTP))
 (847 66 (:DEFINITION MEMBER-EQUAL))
 (792 77 (:DEFINITION PSEUDO-TERM-LISTP))
 (748 374 (:REWRITE DEFAULT-+-2))
 (668 334 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (583 77 (:DEFINITION SYMBOL-LISTP))
 (528 528 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (484 242 (:TYPE-PRESCRIPTION BOUND-VARS-AFTER-HYPS))
 (374 374 (:REWRITE DEFAULT-+-1))
 (372 372 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (341 341 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (341 77 (:REWRITE BOUND-VARS-SUITABLE-FOR-HYPSP-WHEN-FREE-VARS))
 (286 286 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (252 10 (:REWRITE CONSP-OF-ASSOC-EQUAL))
 (242 242 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERMS))
 (231 231 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (231 231 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (209 77 (:REWRITE BOUND-VARS-SUITABLE-FOR-HYPSP-WHEN-NORMAL))
 (209 77 (:REWRITE BOUND-VARS-SUITABLE-FOR-HYPSP-WHEN-AXE-SYTAXP-CAR))
 (187 187 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (77 77 (:REWRITE DEFAULT-COERCE-2))
 (77 77 (:REWRITE DEFAULT-COERCE-1))
 (76 38 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (66 66 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (64 32 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (55 55 (:REWRITE USE-ALL-STORED-AXE-RULEP-2))
 (55 55 (:REWRITE USE-ALL-STORED-AXE-RULEP))
 (53 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (37 37 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (36 1 (:DEFINITION ALISTP))
 (32 32 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (22 11 (:REWRITE DEFAULT-<-1))
 (11 11 (:REWRITE DEFAULT-<-2))
 )
(RULE-LIMITSP-OF-DECREMENT-RULE-LIMIT
 (36 18 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (16 2 (:REWRITE DEFAULT-CDR))
 (12 2 (:REWRITE CONSP-OF-ASSOC-EQUAL))
 (6 2 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE USE-ALL-STORED-AXE-RULEP-2))
 (2 2 (:REWRITE USE-ALL-STORED-AXE-RULEP))
 (2 2 (:REWRITE RULE-LIMITSP-FORWARD-TO-ALISTP))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
