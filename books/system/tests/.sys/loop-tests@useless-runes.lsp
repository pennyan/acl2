(RSQ
 (5 5 (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
 )
(APPLY$-WARRANT-RSQ)
(APPLY$-WARRANT-RSQ-DEFINITION)
(APPLY$-WARRANT-RSQ-NECC)
(APPLY$-RSQ
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(ISQ
 (5 5 (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
 )
(APPLY$-WARRANT-ISQ)
(APPLY$-WARRANT-ISQ-DEFINITION)
(APPLY$-WARRANT-ISQ-NECC)
(APPLY$-ISQ
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(SYMP)
(APPLY$-WARRANT-SYMP)
(APPLY$-WARRANT-SYMP-DEFINITION)
(APPLY$-WARRANT-SYMP-NECC)
(APPLY$-SYMP
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(SSQ)
(APPLY$-WARRANT-SSQ)
(APPLY$-WARRANT-SSQ-DEFINITION)
(APPLY$-WARRANT-SSQ-NECC)
(APPLY$-SSQ
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(FOO
 (801 3 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-2))
 (789 9 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (783 3 (:DEFINITION APPLY$-BADGEP))
 (717 624 (:REWRITE DEFAULT-CAR))
 (714 663 (:REWRITE DEFAULT-CDR))
 (534 44 (:DEFINITION MEMBER-EQUAL))
 (531 3 (:DEFINITION SUBSETP-EQUAL))
 (306 21 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (259 7 (:DEFINITION LOOP$-AS))
 (246 246 (:TYPE-PRESCRIPTION EV$-LIST))
 (125 49 (:REWRITE DEFAULT-+-2))
 (105 42 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (102 18 (:DEFINITION RATIONAL-LISTP))
 (95 17 (:REWRITE DEFAULT-*-2))
 (91 14 (:DEFINITION CDR-LOOP$-AS-TUPLE))
 (91 14 (:DEFINITION CAR-LOOP$-AS-TUPLE))
 (87 49 (:REWRITE DEFAULT-+-1))
 (70 14 (:DEFINITION EMPTY-LOOP$-AS-TUPLEP))
 (63 63 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (63 17 (:REWRITE DEFAULT-*-1))
 (63 6 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-LISTP-2))
 (60 6 (:DEFINITION NATP))
 (58 6 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-LISTP-1))
 (54 54 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (42 42 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (42 42 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (40 4 (:REWRITE NOT-MEMBER-LOOP$-AS-TRUE-LIST-2))
 (36 36 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (36 6 (:REWRITE NOT-MEMBER-LOOP$-AS-IDENTITY-2))
 (36 4 (:REWRITE NOT-MEMBER-LOOP$-AS-TRUE-LIST-1))
 (36 2 (:DEFINITION ALWAYS$))
 (32 8 (:DEFINITION INTEGER-LISTP))
 (32 4 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (31 6 (:REWRITE NOT-MEMBER-LOOP$-AS-IDENTITY-1))
 (27 11 (:REWRITE DEFAULT-SYMBOL-NAME))
 (24 12 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (23 4 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-2))
 (21 21 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (21 21 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (20 4 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-1))
 (20 2 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (18 9 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (18 3 (:DEFINITION ALL-NILS))
 (16 4 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-2))
 (15 15 (:TYPE-PRESCRIPTION ALL-NILS))
 (12 12 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (12 4 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-1))
 (12 3 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (11 11 (:REWRITE DEFAULT-COERCE-2))
 (11 11 (:REWRITE DEFAULT-COERCE-1))
 (10 10 (:TYPE-PRESCRIPTION ALWAYS$))
 (9 3 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-1))
 (8 8 (:REWRITE APPLY$-WARRANT-SSQ-NECC))
 (8 8 (:REWRITE APPLY$-WARRANT-RSQ-NECC))
 (8 8 (:REWRITE APPLY$-WARRANT-ISQ-NECC))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 3 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (6 3 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (4 4 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE NOT-MEMBER-LOOP$-AS-GENERAL))
 (2 2 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-2))
 (2 2 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-1))
 (2 2 (:REWRITE APPLY$-CONSP-ARITY-1))
 (2 2 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (2 2 (:DEFINITION IDENTITY))
 )
(TRUE-LISTP-MAKE-LIST-AC
 (13 11 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(INTEGER-LISTP-MAKE-LIST-AC
 (13 13 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (12 10 (:REWRITE DEFAULT-CDR))
 (12 10 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(ACL2-NUMBER-LISTP-MAKE-LIST-AC
 (32 13 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (13 13 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (13 13 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (12 10 (:REWRITE DEFAULT-CDR))
 (12 10 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(RATIONAL-LISTP-MAKE-LIST-AC
 (14 10 (:REWRITE DEFAULT-CDR))
 (14 10 (:REWRITE DEFAULT-CAR))
 (13 13 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (5 5 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(TEST)
(TEST
 (19901 86 (:DEFINITION APPLY$-BADGEP))
 (17465 15417 (:REWRITE DEFAULT-CDR))
 (17073 14038 (:REWRITE DEFAULT-CAR))
 (16287 61 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-2))
 (16136 228 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (13489 74 (:DEFINITION SUBSETP-EQUAL))
 (10968 6 (:DEFINITION WHEN$+))
 (10133 46 (:DEFINITION UNTIL$+))
 (7809 518 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (5174 1313 (:DEFINITION MAKE-LIST-AC))
 (4404 233 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (3906 651 (:DEFINITION TAILS))
 (3544 2497 (:REWRITE DEFAULT-+-2))
 (2865 261 (:DEFINITION FROM-TO-BY-DOWN-OPENER))
 (2790 2497 (:REWRITE DEFAULT-+-1))
 (1963 15 (:DEFINITION UNTIL$))
 (1859 30 (:REWRITE APPLY$-CONSP-ARITY-1))
 (1554 1554 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (1533 1079 (:REWRITE DEFAULT-<-2))
 (1346 1079 (:REWRITE DEFAULT-<-1))
 (1243 1219 (:REWRITE ZP-OPEN))
 (1036 1036 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (965 343 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (909 909 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (807 144 (:REWRITE DEFAULT-COERCE-2))
 (764 764 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (590 294 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (552 18 (:DEFINITION ALWAYS$))
 (464 136 (:REWRITE DEFAULT-SYMBOL-NAME))
 (444 74 (:DEFINITION ALL-NILS))
 (413 70 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-2))
 (370 370 (:TYPE-PRESCRIPTION ALL-NILS))
 (348 86 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (323 17 (:REWRITE NOT-MEMBER-TAILS-TRUE-LIST-LISTP))
 (299 299 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (296 296 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (286 15 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (255 17 (:REWRITE NOT-MEMBER-TAILS-ACL2-NUMBER-LISTP))
 (238 17 (:REWRITE NOT-MEMBER-TAILS-SYMBOL-LISTP))
 (224 224 (:TYPE-PRESCRIPTION LOOP$-AS))
 (221 17 (:REWRITE NOT-MEMBER-TAILS-RATIONAL-LISTP))
 (221 17 (:REWRITE NOT-MEMBER-TAILS-INTEGER-LISTP))
 (210 70 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-1))
 (187 17 (:DEFINITION SYMBOL-LISTP))
 (183 61 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-1))
 (172 172 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (161 80 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (161 80 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (153 17 (:DEFINITION ACL2-NUMBER-LISTP))
 (143 143 (:REWRITE DEFAULT-COERCE-1))
 (110 110 (:META RELINK-FANCY-SCION-CORRECT))
 (48 48 (:REWRITE DEFAULT-*-2))
 (48 48 (:REWRITE DEFAULT-*-1))
 (45 45 (:REWRITE NOT-MEMBER-LOOP$-AS-GENERAL))
 (45 45 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-2))
 (45 45 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-1))
 (42 42 (:TYPE-PRESCRIPTION UNTIL$+))
 (38 14 (:DEFINITION IDENTITY))
 (34 34 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (16 16 (:REWRITE FOLD-CONSTS-IN-+))
 (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 2 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 )
(BOOHOO
 (3859 1 (:DEFINITION WHEN$+))
 (1959 6 (:DEFINITION APPLY$-BADGEP))
 (1554 1395 (:REWRITE DEFAULT-CDR))
 (1522 91 (:DEFINITION MEMBER-EQUAL))
 (1453 6 (:DEFINITION SUBSETP-EQUAL))
 (1367 7 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-2))
 (1358 1142 (:REWRITE DEFAULT-CAR))
 (1324 18 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (1122 187 (:DEFINITION TAILS))
 (873 42 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (748 187 (:DEFINITION MAKE-LIST-AC))
 (688 17 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (678 15 (:REWRITE DEFAULT-COERCE-2))
 (361 274 (:REWRITE DEFAULT-+-2))
 (274 274 (:REWRITE DEFAULT-+-1))
 (187 187 (:REWRITE ZP-OPEN))
 (142 57 (:REWRITE DEFAULT-<-2))
 (126 126 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (112 14 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (104 9 (:REWRITE NOT-MEMBER-LOOP$-AS-TRUE-LIST-2))
 (93 57 (:REWRITE DEFAULT-<-1))
 (90 33 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (84 84 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (77 77 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (69 69 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (66 7 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-2))
 (52 7 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-2))
 (52 7 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-2))
 (47 47 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (46 22 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (37 7 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-1))
 (36 6 (:DEFINITION ALL-NILS))
 (33 33 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (31 16 (:REWRITE NOT-MEMBER-LOOP$-AS-IDENTITY-1))
 (30 30 (:TYPE-PRESCRIPTION ALL-NILS))
 (30 1 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (28 6 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (24 24 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (23 7 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-1))
 (23 7 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-1))
 (23 7 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-1))
 (22 2 (:DEFINITION ACL2-NUMBER-LISTP))
 (18 2 (:DEFINITION SYMBOL-LISTP))
 (18 2 (:DEFINITION INTEGER-LISTP))
 (14 14 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (14 14 (:REWRITE DEFAULT-COERCE-1))
 (14 14 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (13 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (13 6 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (10 10 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (10 10 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (10 10 (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
 (8 2 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7 (:REWRITE NOT-MEMBER-LOOP$-AS-GENERAL))
 (7 7 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-2))
 (7 7 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-1))
 (3 3 (:META RELINK-FANCY-SCION-CORRECT))
 (1 1 (:REWRITE APPLY$-CONSP-ARITY-1))
 (1 1 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 )
(BOOHOO-LEMMA
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(BOOHOO
 (3859 1 (:DEFINITION WHEN$+))
 (1437 4 (:DEFINITION APPLY$-BADGEP))
 (1249 1096 (:REWRITE DEFAULT-CDR))
 (1215 999 (:REWRITE DEFAULT-CAR))
 (1110 59 (:DEFINITION MEMBER-EQUAL))
 (1099 4 (:DEFINITION SUBSETP-EQUAL))
 (1056 176 (:DEFINITION TAILS))
 (801 3 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-2))
 (798 12 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (704 176 (:DEFINITION MAKE-LIST-AC))
 (678 15 (:REWRITE DEFAULT-COERCE-2))
 (676 11 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (669 28 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (302 239 (:REWRITE DEFAULT-+-2))
 (239 239 (:REWRITE DEFAULT-+-1))
 (176 176 (:REWRITE ZP-OPEN))
 (110 41 (:REWRITE DEFAULT-<-2))
 (84 84 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (77 41 (:REWRITE DEFAULT-<-1))
 (66 21 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (56 56 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (48 6 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (47 47 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (45 45 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (31 31 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (30 14 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (30 1 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (28 14 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (24 4 (:DEFINITION ALL-NILS))
 (21 21 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (20 20 (:TYPE-PRESCRIPTION ALL-NILS))
 (20 12 (:REWRITE NOT-MEMBER-LOOP$-AS-IDENTITY-1))
 (20 4 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (18 3 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-2))
 (16 16 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (15 3 (:REWRITE NOT-MEMBER-LOOP$-AS-ACL2-NUMBER-1))
 (14 14 (:REWRITE DEFAULT-COERCE-1))
 (12 3 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-2))
 (12 3 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-2))
 (9 4 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (9 4 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (9 3 (:REWRITE NOT-MEMBER-LOOP$-AS-SYMBOL-1))
 (9 3 (:REWRITE NOT-MEMBER-LOOP$-AS-RATIONAL-1))
 (9 3 (:REWRITE NOT-MEMBER-LOOP$-AS-INTEGER-1))
 (6 6 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (6 6 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (3 3 (:REWRITE NOT-MEMBER-LOOP$-AS-GENERAL))
 (3 3 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-2))
 (3 3 (:REWRITE NOT-MEMBER-LOOP$-AS-ALWAYS$-1))
 (3 3 (:META RELINK-FANCY-SCION-CORRECT))
 (1 1 (:REWRITE APPLY$-CONSP-ARITY-1))
 (1 1 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 )
(MY-MV)
(APPLY$-WARRANT-MY-MV)
(APPLY$-WARRANT-MY-MV-DEFINITION)
(APPLY$-WARRANT-MY-MV-NECC)
(APPLY$-MY-MV
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(LOOP-WITH-MY-MV-TARGET
 (4 3 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (3 3 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(BELOW-3P)
(BUG1
 (40 11 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (12 2 (:DEFINITION TRUE-LISTP))
 (11 11 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (11 11 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:REWRITE BOOHOO-LEMMA))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(BUG2
 (108 9 (:DEFINITION TRUE-LIST-LISTP))
 (84 4 (:DEFINITION MEMBER-EQUAL))
 (81 8 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX))
 (75 5 (:REWRITE NOT-MEMBER-TAILS-TRUE-LIST-LISTP))
 (51 10 (:DEFINITION TRUE-LISTP))
 (50 5 (:REWRITE NOT-MEMBER-TAILS-SYMBOL-LISTP))
 (49 49 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (46 46 (:REWRITE DEFAULT-CDR))
 (41 41 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (35 35 (:REWRITE DEFAULT-CAR))
 (35 5 (:DEFINITION SYMBOL-LISTP))
 (30 5 (:REWRITE NOT-MEMBER-TAILS-ACL2-NUMBER-LISTP))
 (26 5 (:REWRITE NOT-MEMBER-TAILS-RATIONAL-LISTP))
 (25 25 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (18 2 (:DEFINITION ACL2-NUMBER-LISTP))
 (14 2 (:DEFINITION RATIONAL-LISTP))
 (11 11 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (10 5 (:DEFINITION TAILS))
 (8 8 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT-COROLLARY))
 (5 5 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (4 4 (:REWRITE TRUE-LIST-LISTP-TAILS))
 (4 4 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (4 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE BOOHOO-LEMMA))
 (2 2 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 )
(BELOW-11P)
(BUG3)
(LOOP-TEST-1-USING-MY-MV)
(LOOP-TEST-2-USING-MY-MV)
