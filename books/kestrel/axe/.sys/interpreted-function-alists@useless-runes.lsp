(ADD-TO-INTERPRETED-FUNCTION-ALIST
 (222 3 (:DEFINITION PSEUDO-TERMP))
 (81 9 (:DEFINITION LENGTH))
 (66 12 (:DEFINITION LEN))
 (55 55 (:REWRITE DEFAULT-CDR))
 (51 51 (:REWRITE DEFAULT-CAR))
 (27 27 (:TYPE-PRESCRIPTION LEN))
 (26 13 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (24 12 (:REWRITE DEFAULT-+-2))
 (24 4 (:DEFINITION SYMBOL-LISTP))
 (22 22 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (18 6 (:DEFINITION TRUE-LISTP))
 (17 1 (:DEFINITION SYMBOL-ALISTP))
 (14 1 (:DEFINITION PLIST-WORLDP))
 (12 12 (:REWRITE DEFAULT-+-1))
 (10 5 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (9 3 (:REWRITE PSEUDO-TERMP-OF-LOOKUP-EQUAL-WHEN-SYMBOL-TERM-ALISTP))
 (8 4 (:REWRITE ALISTP-WHEN-PSEUDO-TERM-ALISTP-CHEAP))
 (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 3 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (6 3 (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
 (6 1 (:REWRITE SYMBOL-ALISTP-OF-CDR))
 (4 4 (:TYPE-PRESCRIPTION PSEUDO-TERM-ALISTP))
 (3 3 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (3 3 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (3 3 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 )
(INTERPRETED-FUNCTION-ALISTP-OF-ADD-TO-INTERPRETED-FUNCTION-ALIST
 (148 2 (:DEFINITION PSEUDO-TERMP))
 (54 6 (:DEFINITION LENGTH))
 (38 38 (:REWRITE DEFAULT-CDR))
 (31 31 (:REWRITE DEFAULT-CAR))
 (19 19 (:TYPE-PRESCRIPTION LEN))
 (18 9 (:REWRITE DEFAULT-+-2))
 (12 6 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (12 4 (:DEFINITION TRUE-LISTP))
 (10 10 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (10 10 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (10 10 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (9 9 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE PSEUDO-TERMP-OF-LOOKUP-EQUAL-WHEN-SYMBOL-TERM-ALISTP))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (4 2 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (4 2 (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
 (1 1 (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP))
 )
(ADD-FNS-TO-INTERPRETED-FUNCTION-ALIST
 (33 33 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE DEFAULT-CDR))
 (12 6 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (7 7 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (6 6 (:TYPE-PRESCRIPTION ADD-TO-INTERPRETED-FUNCTION-ALIST))
 (2 1 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 )
(INTERPRETED-FUNCTION-ALISTP-OF-ADD-FNS-TO-INTERPRETED-FUNCTION-ALIST
 (13 13 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(MAKE-INTERPRETED-FUNCTION-ALIST)
(INTERPRETED-FUNCTION-ALISTP-OF-MAKE-INTERPRETED-FUNCTION-ALIST)
(INTERPRETED-FUNCTION-ALIST-COMPLETEP-AUX
 (331 247 (:REWRITE DEFAULT-CDR))
 (213 211 (:REWRITE DEFAULT-CAR))
 (164 82 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (133 133 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (124 17 (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP))
 (102 51 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (58 29 (:REWRITE DEFAULT-+-2))
 (56 56 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (54 27 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (45 5 (:DEFINITION SUBSETP-EQUAL))
 (34 17 (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP-CHEAP))
 (29 29 (:REWRITE DEFAULT-+-1))
 (18 9 (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
 (18 6 (:DEFINITION MEMBER-EQUAL))
 (11 1 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (10 10 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 6 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 6 (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
 (6 6 (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP))
 (5 5 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (5 5 (:REWRITE DEFAULT-COERCE-1))
 )
(INTERPRETED-FUNCTION-ALIST-COMPLETEP
 (142 88 (:REWRITE DEFAULT-CAR))
 (98 70 (:REWRITE DEFAULT-CDR))
 (78 13 (:DEFINITION STRIP-CARS))
 (26 13 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (13 13 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 )
(MAKE-COMPLETE-INTERPRETED-FUNCTION-ALIST)
