(IF-AND-NOT-EVAL-OF-MAKE-IF-TERM-GEN
 (141 75 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (138 138 (:REWRITE DEFAULT-CAR))
 (107 75 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (75 75 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (75 75 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (65 65 (:REWRITE DEFAULT-CDR))
 (45 45 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 )
(IF-AND-NOT-EVAL-WHEN-TERM-IS-DISJUNCTIONP
 (44 44 (:REWRITE DEFAULT-CAR))
 (34 34 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (16 15 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (10 2 (:DEFINITION PAIRLIS$))
 (10 2 (:DEFINITION ASSOC-EQUAL))
 (5 5 (:REWRITE IF-AND-NOT-EVAL-LIST-OF-ATOM))
 (4 1 (:DEFINITION KWOTE-LST))
 (2 2 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (1 1 (:DEFINITION KWOTE))
 )
(IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP)
(COMPLEMENTARY-TERMSP
 (25 3 (:DEFINITION LENGTH))
 (20 4 (:DEFINITION LEN))
 (18 18 (:REWRITE DEFAULT-CDR))
 (15 15 (:REWRITE DEFAULT-CAR))
 (9 9 (:TYPE-PRESCRIPTION LEN))
 (8 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 1 (:DEFINITION SYMBOL-LISTP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 )
(NOT-COMPLEMENTARY-TERMSP-SELF
 (9 9 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(COMPLEMENTARY-TERMSP-SYMMETRIC
 (12 12 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE DEFAULT-CDR))
 )
(IF-AND-NOT-EVAL-WHEN-COMPLEMENTARY-TERMSP
 (27 9 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-DISJUNCTIONP))
 (27 9 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP))
 (18 18 (:TYPE-PRESCRIPTION TERM-IS-DISJUNCTIONP))
 (18 18 (:TYPE-PRESCRIPTION TERM-IS-CONJUNCTIONP))
 (15 15 (:REWRITE DEFAULT-CAR))
 (15 9 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (9 9 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (9 9 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (6 6 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 (6 6 (:REWRITE IF-AND-NOT-EVAL-OF-QUOTE))
 (6 6 (:REWRITE IF-AND-NOT-EVAL-OF-IF-CALL))
 (6 6 (:REWRITE DEFAULT-CDR))
 )
(COMBINABLE-DISJUNCTIONSP
 (1436 719 (:REWRITE DEFAULT-+-2))
 (751 719 (:REWRITE DEFAULT-+-1))
 (522 11 (:DEFINITION ACL2-COUNT))
 (354 118 (:DEFINITION SYMBOL-LISTP))
 (260 260 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (151 151 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (150 150 (:REWRITE DEFAULT-COERCE-2))
 (150 150 (:REWRITE DEFAULT-COERCE-1))
 (80 20 (:REWRITE COMMUTATIVITY-OF-+))
 (80 20 (:DEFINITION INTEGER-ABS))
 (22 21 (:REWRITE DEFAULT-<-2))
 (22 21 (:REWRITE DEFAULT-<-1))
 (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 10 (:REWRITE DEFAULT-REALPART))
 (10 10 (:REWRITE DEFAULT-NUMERATOR))
 (10 10 (:REWRITE DEFAULT-IMAGPART))
 (10 10 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:LINEAR <-OF-0-AND-ACL2-COUNT-WHEN-CONSP-LINEAR))
 )
(COMBINABLE-DISJUNCTIONSP-SYMMETRIC
 (176 176 (:REWRITE DEFAULT-CDR))
 (104 104 (:REWRITE DEFAULT-CAR))
 )
(CONJOIN-COMBINABLE-DISJUNCTIONS
 (2323 1162 (:REWRITE DEFAULT-+-2))
 (1194 1162 (:REWRITE DEFAULT-+-1))
 (591 197 (:DEFINITION SYMBOL-LISTP))
 (522 11 (:DEFINITION ACL2-COUNT))
 (420 420 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (256 256 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (239 239 (:REWRITE DEFAULT-COERCE-2))
 (239 239 (:REWRITE DEFAULT-COERCE-1))
 (80 20 (:REWRITE COMMUTATIVITY-OF-+))
 (80 20 (:DEFINITION INTEGER-ABS))
 (22 21 (:REWRITE DEFAULT-<-2))
 (22 21 (:REWRITE DEFAULT-<-1))
 (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 10 (:REWRITE DEFAULT-REALPART))
 (10 10 (:REWRITE DEFAULT-NUMERATOR))
 (10 10 (:REWRITE DEFAULT-IMAGPART))
 (10 10 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:LINEAR <-OF-0-AND-ACL2-COUNT-WHEN-CONSP-LINEAR))
 )
(PSEUDO-TERMP-OF-CONJOIN-COMBINABLE-DISJUNCTIONS
 (1480 740 (:REWRITE DEFAULT-+-2))
 (740 740 (:REWRITE DEFAULT-+-1))
 (378 126 (:DEFINITION SYMBOL-LISTP))
 (277 277 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (180 180 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (163 163 (:REWRITE DEFAULT-COERCE-2))
 (163 163 (:REWRITE DEFAULT-COERCE-1))
 )
(IF-AND-NOT-EVAL-OF-CONJOIN-COMBINABLE-DISJUNCTIONS
 (455 159 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP))
 (296 296 (:TYPE-PRESCRIPTION TERM-IS-CONJUNCTIONP))
 (272 140 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (140 140 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (140 140 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (122 116 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 )
(FIND-COMBINABLE-CONJUNCT
 (381 9 (:DEFINITION ACL2-COUNT))
 (282 282 (:REWRITE DEFAULT-CDR))
 (240 6 (:DEFINITION COMBINABLE-DISJUNCTIONSP))
 (175 86 (:REWRITE DEFAULT-+-2))
 (168 168 (:REWRITE DEFAULT-CAR))
 (155 31 (:DEFINITION LEN))
 (110 86 (:REWRITE DEFAULT-+-1))
 (56 14 (:REWRITE COMMUTATIVITY-OF-+))
 (56 14 (:DEFINITION INTEGER-ABS))
 (18 6 (:DEFINITION SYMBOL-LISTP))
 (17 17 (:REWRITE FOLD-CONSTS-IN-+))
 (16 15 (:REWRITE DEFAULT-<-2))
 (16 15 (:REWRITE DEFAULT-<-1))
 (15 15 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (14 14 (:REWRITE DEFAULT-UNARY-MINUS))
 (13 13 (:REWRITE DEFAULT-COERCE-2))
 (13 13 (:REWRITE DEFAULT-COERCE-1))
 (12 12 (:TYPE-PRESCRIPTION TERM-IS-DISJUNCTIONP))
 (7 7 (:REWRITE DEFAULT-REALPART))
 (7 7 (:REWRITE DEFAULT-NUMERATOR))
 (7 7 (:REWRITE DEFAULT-IMAGPART))
 (7 7 (:REWRITE DEFAULT-DENOMINATOR))
 (6 6 (:TYPE-PRESCRIPTION COMPLEMENTARY-TERMSP))
 (6 6 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (3 3 (:LINEAR <-OF-0-AND-ACL2-COUNT-WHEN-CONSP-LINEAR))
 )
(PSEUDO-TERMP-OF-FIND-COMBINABLE-CONJUNCT
 (504 504 (:REWRITE DEFAULT-CDR))
 (308 308 (:REWRITE DEFAULT-CAR))
 (256 50 (:DEFINITION LEN))
 (102 51 (:REWRITE DEFAULT-+-2))
 (60 27 (:DEFINITION TRUE-LISTP))
 (51 51 (:REWRITE DEFAULT-+-1))
 (36 12 (:DEFINITION SYMBOL-LISTP))
 (24 24 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (13 13 (:REWRITE DEFAULT-COERCE-2))
 (13 13 (:REWRITE DEFAULT-COERCE-1))
 (12 12 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 )
(COMBINABLE-DISJUNCTIONSP-OF-FIND-COMBINABLE-CONJUNCT
 (668 668 (:REWRITE DEFAULT-CDR))
 (340 340 (:REWRITE DEFAULT-CAR))
 )
(COMBINABLE-DISJUNCTIONSP-OF-FIND-COMBINABLE-CONJUNCT-ALT
 (180 2 (:DEFINITION FIND-COMBINABLE-CONJUNCT))
 (160 4 (:DEFINITION COMBINABLE-DISJUNCTIONSP))
 (102 102 (:REWRITE DEFAULT-CDR))
 (52 52 (:REWRITE DEFAULT-CAR))
 (8 8 (:TYPE-PRESCRIPTION TERM-IS-DISJUNCTIONP))
 (4 4 (:TYPE-PRESCRIPTION COMPLEMENTARY-TERMSP))
 (2 2 (:TYPE-PRESCRIPTION TERM-IS-CONJUNCTIONP))
 )
(NOT-IF-AND-NOT-EVAL-WHEN-FIND-COMBINABLE-CONJUNCT-AND-FALSE
 (605 605 (:REWRITE DEFAULT-CDR))
 (324 324 (:REWRITE DEFAULT-CAR))
 (39 13 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-DISJUNCTIONP))
 (26 13 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (15 15 (:REWRITE IF-AND-NOT-EVAL-WHEN-COMPLEMENTARY-TERMSP))
 (13 13 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (13 13 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (13 13 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 (13 13 (:REWRITE IF-AND-NOT-EVAL-OF-QUOTE))
 (13 13 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (13 13 (:REWRITE IF-AND-NOT-EVAL-OF-IF-CALL))
 )
(REMOVE-CONJUNCT
 (381 9 (:DEFINITION ACL2-COUNT))
 (127 62 (:REWRITE DEFAULT-+-2))
 (86 62 (:REWRITE DEFAULT-+-1))
 (56 14 (:REWRITE COMMUTATIVITY-OF-+))
 (56 14 (:DEFINITION INTEGER-ABS))
 (56 7 (:DEFINITION LENGTH))
 (35 7 (:DEFINITION LEN))
 (21 21 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE FOLD-CONSTS-IN-+))
 (16 15 (:REWRITE DEFAULT-<-2))
 (16 15 (:REWRITE DEFAULT-<-1))
 (14 14 (:REWRITE DEFAULT-UNARY-MINUS))
 (13 13 (:REWRITE DEFAULT-CAR))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (7 7 (:REWRITE DEFAULT-REALPART))
 (7 7 (:REWRITE DEFAULT-NUMERATOR))
 (7 7 (:REWRITE DEFAULT-IMAGPART))
 (7 7 (:REWRITE DEFAULT-DENOMINATOR))
 (7 7 (:REWRITE DEFAULT-COERCE-2))
 (7 7 (:REWRITE DEFAULT-COERCE-1))
 (3 3 (:LINEAR <-OF-0-AND-ACL2-COUNT-WHEN-CONSP-LINEAR))
 )
(<=-OF-ACL2-COUNT-OF-REMOVE-CONJUNCT
 (54861 23232 (:REWRITE DEFAULT-+-2))
 (29179 23232 (:REWRITE DEFAULT-+-1))
 (16134 21 (:REWRITE ACL2-COUNT-CAR-CHAINING))
 (8068 8068 (:REWRITE DEFAULT-CDR))
 (6150 5975 (:REWRITE DEFAULT-<-2))
 (6096 5975 (:REWRITE DEFAULT-<-1))
 (5993 5993 (:REWRITE FOLD-CONSTS-IN-+))
 (5850 5850 (:REWRITE DEFAULT-UNARY-MINUS))
 (5495 21 (:REWRITE ACL2-COUNT-HACK))
 (4731 4731 (:REWRITE DEFAULT-CAR))
 (2925 2925 (:REWRITE DEFAULT-NUMERATOR))
 (2925 2925 (:REWRITE DEFAULT-DENOMINATOR))
 (2257 2257 (:REWRITE DEFAULT-REALPART))
 (2257 2257 (:REWRITE DEFAULT-IMAGPART))
 (2257 2257 (:REWRITE DEFAULT-COERCE-2))
 (2257 2257 (:REWRITE DEFAULT-COERCE-1))
 (34 34 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (30 30 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (15 15 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (12 12 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (11 11 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 )
(PSEUDO-TERMP-OF-REMOVE-CONJUNCT
 (236 46 (:DEFINITION LEN))
 (206 206 (:REWRITE DEFAULT-CDR))
 (154 154 (:REWRITE DEFAULT-CAR))
 (94 47 (:REWRITE DEFAULT-+-2))
 (56 25 (:DEFINITION TRUE-LISTP))
 (47 47 (:REWRITE DEFAULT-+-1))
 (33 11 (:DEFINITION SYMBOL-LISTP))
 (22 22 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (12 12 (:REWRITE DEFAULT-COERCE-2))
 (12 12 (:REWRITE DEFAULT-COERCE-1))
 (11 11 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 )
(REMOVE-CONJUNCT
 (109 109 (:REWRITE DEFAULT-CDR))
 (100 20 (:DEFINITION LEN))
 (71 71 (:REWRITE DEFAULT-CAR))
 (40 20 (:REWRITE DEFAULT-+-2))
 (20 20 (:REWRITE DEFAULT-+-1))
 (15 5 (:DEFINITION SYMBOL-LISTP))
 (13 13 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (5 5 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (5 5 (:REWRITE DEFAULT-COERCE-1))
 )
(IF-AND-NOT-EVAL-OF-REMOVE-CONJUNCT-WHEN-TRUE
 (139 48 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-DISJUNCTIONP))
 (91 91 (:TYPE-PRESCRIPTION TERM-IS-DISJUNCTIONP))
 (88 46 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (75 75 (:REWRITE DEFAULT-CAR))
 (53 53 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-FIND-COMBINABLE-CONJUNCT-AND-FALSE))
 (53 53 (:REWRITE IF-AND-NOT-EVAL-WHEN-COMPLEMENTARY-TERMSP))
 (50 50 (:REWRITE DEFAULT-CDR))
 (46 46 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (46 46 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (46 46 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (46 46 (:REWRITE IF-AND-NOT-EVAL-OF-IF-CALL))
 (43 43 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 )
(NOT-IF-AND-NOT-EVAL-WHEN-NOT-IF-AND-NOT-EVAL-OF-REMOVE-CONJUNCT-WHEN-TRUE
 (81 28 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-DISJUNCTIONP))
 (75 5 (:REWRITE IF-AND-NOT-EVAL-OF-REMOVE-CONJUNCT-WHEN-TRUE))
 (53 53 (:TYPE-PRESCRIPTION TERM-IS-DISJUNCTIONP))
 (49 26 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (43 43 (:REWRITE DEFAULT-CAR))
 (32 32 (:REWRITE IF-AND-NOT-EVAL-WHEN-COMPLEMENTARY-TERMSP))
 (28 28 (:REWRITE DEFAULT-CDR))
 (27 27 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-FIND-COMBINABLE-CONJUNCT-AND-FALSE))
 (26 26 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (26 26 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (26 26 (:REWRITE IF-AND-NOT-EVAL-OF-IF-CALL))
 (23 23 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 (21 21 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 )
(IF-AND-NOT-EVAL-WHEN-EQUAL-OF-T-AND-REMOVE-CONJUNCT
 (73 25 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-DISJUNCTIONP))
 (56 56 (:REWRITE DEFAULT-CAR))
 (48 48 (:TYPE-PRESCRIPTION TERM-IS-DISJUNCTIONP))
 (45 25 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (44 44 (:REWRITE DEFAULT-CDR))
 (31 31 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-NOT-IF-AND-NOT-EVAL-OF-REMOVE-CONJUNCT-WHEN-TRUE))
 (31 31 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-FIND-COMBINABLE-CONJUNCT-AND-FALSE))
 (31 31 (:REWRITE IF-AND-NOT-EVAL-WHEN-COMPLEMENTARY-TERMSP))
 (25 25 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (25 25 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (25 25 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (25 25 (:REWRITE IF-AND-NOT-EVAL-OF-IF-CALL))
 (22 22 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 )
(STRENGTHEN-CONJUNCTS-AUX
 (900 20 (:DEFINITION ACL2-COUNT))
 (286 140 (:REWRITE DEFAULT-+-2))
 (194 140 (:REWRITE DEFAULT-+-1))
 (128 32 (:REWRITE COMMUTATIVITY-OF-+))
 (128 32 (:DEFINITION INTEGER-ABS))
 (128 16 (:DEFINITION LENGTH))
 (80 16 (:DEFINITION LEN))
 (58 58 (:REWRITE DEFAULT-CDR))
 (38 38 (:REWRITE FOLD-CONSTS-IN-+))
 (38 38 (:REWRITE +-COMBINE-CONSTANTS))
 (36 34 (:REWRITE DEFAULT-<-2))
 (36 34 (:REWRITE DEFAULT-<-1))
 (35 35 (:REWRITE DEFAULT-CAR))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 16 (:TYPE-PRESCRIPTION LEN))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 (7 7 (:LINEAR <-OF-0-AND-ACL2-COUNT-WHEN-CONSP-LINEAR))
 )
(PSEUDO-TERMP-OF-STRENGTHEN-CONJUNCTS-AUX
 (275 275 (:REWRITE DEFAULT-CDR))
 (268 50 (:DEFINITION LEN))
 (184 184 (:REWRITE DEFAULT-CAR))
 (106 53 (:REWRITE DEFAULT-+-2))
 (71 28 (:DEFINITION TRUE-LISTP))
 (53 53 (:REWRITE DEFAULT-+-1))
 (33 11 (:DEFINITION SYMBOL-LISTP))
 (25 25 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (16 16 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (14 14 (:REWRITE DEFAULT-COERCE-2))
 (14 14 (:REWRITE DEFAULT-COERCE-1))
 )
(STRENGTHEN-CONJUNCTS-AUX
 (137 137 (:REWRITE DEFAULT-CDR))
 (120 24 (:DEFINITION LEN))
 (87 87 (:REWRITE DEFAULT-CAR))
 (48 24 (:REWRITE DEFAULT-+-2))
 (24 24 (:REWRITE DEFAULT-+-1))
 (18 6 (:DEFINITION SYMBOL-LISTP))
 (15 15 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 6 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (6 6 (:REWRITE DEFAULT-COERCE-2))
 (6 6 (:REWRITE DEFAULT-COERCE-1))
 )
(IF-AND-NOT-EVAL-OF-STRENGTHEN-CONJUNCTS-AUX
 (193 193 (:REWRITE DEFAULT-CDR))
 (188 66 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-DISJUNCTIONP))
 (176 176 (:REWRITE DEFAULT-CAR))
 (123 64 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (122 122 (:TYPE-PRESCRIPTION TERM-IS-DISJUNCTIONP))
 (74 74 (:REWRITE IF-AND-NOT-EVAL-WHEN-COMPLEMENTARY-TERMSP))
 (68 64 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (64 64 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (61 61 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (58 58 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 )
