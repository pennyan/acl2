(PFIELD::PSEUDO-TERM-LISTP-OF-APPEND
 (72 1 (:DEFINITION PSEUDO-TERMP))
 (38 36 (:REWRITE DEFAULT-CDR))
 (36 34 (:REWRITE DEFAULT-CAR))
 (33 33 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (27 3 (:DEFINITION LENGTH))
 (22 4 (:DEFINITION LEN))
 (19 19 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (9 9 (:TYPE-PRESCRIPTION LEN))
 (8 4 (:REWRITE DEFAULT-+-2))
 (8 4 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (6 2 (:DEFINITION TRUE-LISTP))
 (5 1 (:DEFINITION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (4 4 (:REWRITE DEFAULT-+-1))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 )
(PFIELD::PSEUDO-TERM-LISTP-OF-CDR
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(PFIELD::PSEUDO-TERMP-OF-CAR
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1 1 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(PFIELD::GET-NEGATED-ADDENDS
 (224 224 (:REWRITE DEFAULT-CDR))
 (220 40 (:DEFINITION LEN))
 (206 206 (:REWRITE DEFAULT-CAR))
 (175 15 (:REWRITE PFIELD::PSEUDO-TERMP-OF-CAR))
 (108 54 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (80 40 (:REWRITE DEFAULT-+-2))
 (74 74 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (60 20 (:DEFINITION TRUE-LISTP))
 (54 54 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (40 40 (:REWRITE DEFAULT-+-1))
 (29 29 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (24 8 (:DEFINITION MEMBER-EQUAL))
 (10 10 (:REWRITE DEFAULT-COERCE-2))
 (10 10 (:REWRITE DEFAULT-COERCE-1))
 )
(PFIELD::PSEUDO-TERM-LISTP-OF-GET-NEGATED-ADDENDS
 (470 466 (:REWRITE DEFAULT-CDR))
 (398 394 (:REWRITE DEFAULT-CAR))
 (260 260 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (202 18 (:DEFINITION LENGTH))
 (168 28 (:DEFINITION LEN))
 (120 60 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (92 92 (:TYPE-PRESCRIPTION LEN))
 (62 62 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (60 60 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (60 30 (:REWRITE DEFAULT-+-2))
 (36 6 (:DEFINITION SYMBOL-LISTP))
 (30 30 (:REWRITE DEFAULT-+-1))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (14 14 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (8 8 (:REWRITE DEFAULT-COERCE-2))
 (8 8 (:REWRITE DEFAULT-COERCE-1))
 )
(PFIELD::BIND-SUM-OF-NEGATED-TERMS
 (1716 20 (:DEFINITION PFIELD::GET-NEGATED-ADDENDS))
 (1403 1303 (:REWRITE DEFAULT-CDR))
 (1230 1050 (:REWRITE DEFAULT-CAR))
 (1156 100 (:DEFINITION MEMBER-EQUAL))
 (270 15 (:DEFINITION PSEUDO-TERM-LISTP))
 (213 213 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (200 100 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (193 97 (:REWRITE DEFAULT-+-2))
 (109 109 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (100 100 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (100 20 (:DEFINITION SYMBOL-LISTP))
 (97 97 (:REWRITE DEFAULT-+-1))
 (50 10 (:DEFINITION BINARY-APPEND))
 (24 24 (:REWRITE DEFAULT-COERCE-2))
 (24 24 (:REWRITE DEFAULT-COERCE-1))
 )
(PFIELD::SYMBOL-TERM-ALISTP-OF-BIND-SUM-OF-NEGATED-TERMS
 (4938 58 (:DEFINITION PFIELD::GET-NEGATED-ADDENDS))
 (3314 290 (:DEFINITION MEMBER-EQUAL))
 (2617 2095 (:REWRITE DEFAULT-CAR))
 (2331 2041 (:REWRITE DEFAULT-CDR))
 (1044 1044 (:TYPE-PRESCRIPTION PFIELD::GET-ADDENDS))
 (276 138 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (189 21 (:DEFINITION LENGTH))
 (154 28 (:DEFINITION LEN))
 (133 1 (:DEFINITION SYMBOL-TERM-ALISTP))
 (100 20 (:DEFINITION BINARY-APPEND))
 (63 63 (:TYPE-PRESCRIPTION LEN))
 (63 63 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (56 28 (:REWRITE DEFAULT-+-2))
 (55 11 (:DEFINITION PFIELD::MAKE-ADD-NEST))
 (35 7 (:DEFINITION SYMBOL-LISTP))
 (30 30 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (28 28 (:REWRITE DEFAULT-+-1))
 (7 7 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (7 7 (:REWRITE DEFAULT-COERCE-2))
 (7 7 (:REWRITE DEFAULT-COERCE-1))
 (4 1 (:REWRITE SYMBOL-TERM-ALISTP-OF-CDR))
 (4 1 (:REWRITE PSEUDO-TERMP-OF-CDR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
 )
(PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE
 (508 84 (:REWRITE COMMUTATIVITY-OF-*))
 (449 32 (:REWRITE MOD-WHEN-MULTIPLE))
 (449 32 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (356 14 (:REWRITE MOD-OF-+-SUBST-CONSTANT))
 (328 28 (:REWRITE DISTRIBUTIVITY))
 (202 202 (:REWRITE DEFAULT-*-2))
 (202 202 (:REWRITE DEFAULT-*-1))
 (146 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (140 32 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (126 126 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (82 10 (:REWRITE PFIELD::MOD-WHEN-FEP))
 (75 15 (:REWRITE PFIELD::FEP-HOLDS))
 (64 64 (:REWRITE DEFAULT-+-2))
 (64 64 (:REWRITE DEFAULT-+-1))
 (62 62 (:REWRITE DEFAULT-UNARY-/))
 (50 32 (:REWRITE MOD-WHEN-<-OF-0))
 (45 15 (:DEFINITION NATP))
 (35 35 (:REWRITE DEFAULT-<-2))
 (35 35 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (15 15 (:TYPE-PRESCRIPTION NATP))
 (15 15 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (10 10 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (10 10 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (10 10 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (10 10 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (4 4 (:REWRITE IFIX-WHEN-NOT-INTEGERP-UNLIMITED))
 (2 2 (:REWRITE EQUAL-OF-MOD-OF-+-WHEN-CONSTANTS))
 )
(PFIELD::FIND-NEGATED-ADDEND
 (596 273 (:REWRITE DEFAULT-+-2))
 (370 273 (:REWRITE DEFAULT-+-1))
 (224 56 (:REWRITE COMMUTATIVITY-OF-+))
 (224 56 (:DEFINITION INTEGER-ABS))
 (224 28 (:DEFINITION LENGTH))
 (140 28 (:DEFINITION LEN))
 (87 68 (:REWRITE DEFAULT-<-2))
 (77 68 (:REWRITE DEFAULT-<-1))
 (56 56 (:REWRITE DEFAULT-UNARY-MINUS))
 (48 2 (:DEFINITION PFIELD::FIND-NEGATED-ADDEND))
 (28 28 (:TYPE-PRESCRIPTION LEN))
 (28 28 (:REWRITE DEFAULT-REALPART))
 (28 28 (:REWRITE DEFAULT-NUMERATOR))
 (28 28 (:REWRITE DEFAULT-IMAGPART))
 (28 28 (:REWRITE DEFAULT-DENOMINATOR))
 (28 28 (:REWRITE DEFAULT-COERCE-2))
 (28 28 (:REWRITE DEFAULT-COERCE-1))
 (20 10 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (15 15 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (12 12 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (10 10 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (4 2 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 )
(PFIELD::BIND-A-NEGATED-ADDEND
 (74 74 (:REWRITE DEFAULT-CDR))
 (29 29 (:REWRITE DEFAULT-CAR))
 (26 8 (:REWRITE PFIELD::PSEUDO-TERM-LISTP-OF-CDR))
 (14 14 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (7 7 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 2 (:DEFINITION MEMBER-EQUAL))
 )
(PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2A
 (24 2 (:REWRITE MOD-WHEN-MULTIPLE))
 (24 2 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (20 4 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (12 4 (:REWRITE COMMUTATIVITY-OF-*))
 (10 2 (:REWRITE PFIELD::FEP-HOLDS))
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 (6 2 (:DEFINITION NATP))
 (4 4 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (4 4 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (4 4 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (4 4 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (4 4 (:REWRITE DEFAULT-UNARY-/))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (2 2 (:REWRITE MOD-WHEN-<-OF-0))
 (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP-UNLIMITED))
 (2 2 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (2 2 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG2))
 (2 2 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG1))
 (2 2 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
 (2 2 (:REWRITE PFIELD::ADD-COMMUTATIVE))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS-ALT))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS))
 )
(PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2B
 (25 2 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (24 2 (:REWRITE MOD-WHEN-MULTIPLE))
 (20 4 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (12 4 (:REWRITE COMMUTATIVITY-OF-*))
 (10 2 (:REWRITE PFIELD::FEP-HOLDS))
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 (6 2 (:DEFINITION NATP))
 (5 4 (:REWRITE DEFAULT-UNARY-/))
 (4 4 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (4 4 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (4 4 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (4 4 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (4 4 (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2A))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (2 2 (:REWRITE MOD-WHEN-<-OF-0))
 (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP-UNLIMITED))
 (2 2 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (2 2 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (2 2 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG2))
 (2 2 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG1))
 (2 2 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
 (2 2 (:REWRITE PFIELD::ADD-COMMUTATIVE))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS-ALT))
 (1 1 (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS))
 )
(PFIELD::ADD-OF-NEG-SAME-ARG2-GEN-WITH-BIND-FREE-ID)
(PFIELD::ADD-OF-ADD-OF-NEG-SAME-WITH-BIND-FREE-ID
 (46 4 (:REWRITE PFIELD::MOD-WHEN-FEP))
 (40 4 (:REWRITE MOD-WHEN-MULTIPLE))
 (40 4 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (33 3 (:REWRITE PFIELD::FEP-HOLDS))
 (30 4 (:REWRITE MOD-WHEN-<))
 (23 3 (:DEFINITION NATP))
 (20 4 (:REWRITE MOD-WHEN-<-OF-0))
 (18 11 (:REWRITE DEFAULT-<-1))
 (14 6 (:REWRITE DEFAULT-UNARY-/))
 (13 11 (:REWRITE DEFAULT-<-2))
 (12 8 (:REWRITE DEFAULT-*-2))
 (12 8 (:REWRITE DEFAULT-*-1))
 (9 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (8 4 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (8 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (6 6 (:TYPE-PRESCRIPTION PFIELD::FEP))
 (6 4 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (6 4 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (6 4 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (6 2 (:REWRITE COMMUTATIVITY-OF-*))
 (4 4 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP-UNLIMITED))
 (2 2 (:REWRITE IFIX-WHEN-INTEGERP))
 (2 2 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG2))
 (2 2 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG1))
 (2 1 (:REWRITE DEFAULT-+-2))
 (2 1 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION PFIELD::NATP-OF-NEG))
 (1 1 (:REWRITE PFIELD::NEG-WHEN-NOT-POSP-ARG2-CHEAP))
 (1 1 (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (1 1 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
 (1 1 (:REWRITE PFIELD::ADD-COMMUTATIVE-WHEN-CONSTANT))
 (1 1 (:REWRITE PFIELD::ADD-COMMUTATIVE))
 )
