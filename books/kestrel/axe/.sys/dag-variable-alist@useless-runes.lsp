(<-OF-LOOKUP-EQUAL-WHEN-ALL-<-OF-STRIP-CDRS
 (126 17 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (84 30 (:REWRITE USE-ALL-<))
 (56 30 (:REWRITE DEFAULT-<-2))
 (54 54 (:TYPE-PRESCRIPTION MEMBERP))
 (54 27 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (52 52 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (40 40 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (40 40 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (34 17 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (30 30 (:REWRITE USE-ALL-<-2))
 (27 27 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (17 17 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (17 17 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (17 17 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (17 17 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (17 17 (:REWRITE ALL-<-TRANSITIVE))
 )
(DAG-VARIABLE-ALISTP)
(DAG-VARIABLE-ALISTP-FORWARD-TO-ALIST)
(DAG-VARIABLE-ALISTP-FORWARD-TO-NAT-LISTP-OF-STRIP-CDRS)
(DAG-VARIABLE-ALISTP-FORWARD-SYMBOL-ALISTP)
(INTEGERP-OF-LOOKUP-EQUAL-WHEN-DAG-VARIABLE-ALISTP
 (96 93 (:REWRITE DEFAULT-CAR))
 (96 12 (:REWRITE USE-ALL-<-FOR-CAR))
 (94 73 (:REWRITE DEFAULT-CDR))
 (52 26 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (48 48 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (44 22 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (36 36 (:TYPE-PRESCRIPTION ALL-<))
 (33 33 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (33 33 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (24 12 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (23 23 (:REWRITE USE-ALL-<-2))
 (23 23 (:REWRITE USE-ALL-<))
 (23 23 (:REWRITE DEFAULT-<-2))
 (23 23 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (12 12 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (12 12 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (12 12 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (12 12 (:REWRITE ALL-<-TRANSITIVE))
 )
(NONNEG-OF-LOOKUP-EQUAL-WHEN-DAG-VARIABLE-ALISTP
 (205 9 (:REWRITE <-OF-LOOKUP-EQUAL-WHEN-ALL-<-OF-STRIP-CDRS))
 (111 75 (:REWRITE DEFAULT-CDR))
 (72 70 (:REWRITE DEFAULT-CAR))
 (69 16 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (56 7 (:REWRITE USE-ALL-<-FOR-CAR))
 (54 27 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (40 40 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (36 36 (:TYPE-PRESCRIPTION ALL-<))
 (36 26 (:REWRITE DEFAULT-<-1))
 (26 26 (:REWRITE USE-ALL-<-2))
 (26 26 (:REWRITE USE-ALL-<))
 (26 26 (:REWRITE DEFAULT-<-2))
 (26 13 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (25 16 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (16 16 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (16 16 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (16 16 (:REWRITE ALL-<-TRANSITIVE))
 (15 3 (:REWRITE ALL-<-OF-CONS))
 (14 7 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (11 11 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (11 11 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (10 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(DAG-VARIABLE-ALISTP-OF-CONS-OF-CONS
 (21 14 (:REWRITE DEFAULT-CDR))
 (17 16 (:REWRITE DEFAULT-CAR))
 (16 2 (:REWRITE USE-ALL-<-FOR-CAR))
 (12 6 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (11 11 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (10 5 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (6 6 (:TYPE-PRESCRIPTION ALL-<))
 (5 5 (:REWRITE USE-ALL-<-2))
 (5 5 (:REWRITE USE-ALL-<))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (2 2 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (2 2 (:REWRITE ALL-<-TRANSITIVE))
 )
(ALL-<-OF-STRIP-CDRS-OF-0-WHEN-DAG-VARIABLE-ALISTP
 (36 22 (:REWRITE DEFAULT-CDR))
 (32 32 (:REWRITE DEFAULT-CAR))
 (28 14 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (26 26 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (24 12 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (11 2 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (8 1 (:REWRITE USE-ALL-<-FOR-CAR))
 (3 2 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (2 2 (:REWRITE ALL-<-TRANSITIVE))
 (1 1 (:REWRITE USE-ALL-<-2))
 (1 1 (:REWRITE USE-ALL-<))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(NATP-OF-LOOKUP-EQUAL-WHEN-DAG-VARIABLE-ALISTP
 (255 10 (:REWRITE USE-ALL-<-FOR-CAR))
 (175 10 (:REWRITE ALL-<-OF-STRIP-CDRS-OF-0-WHEN-DAG-VARIABLE-ALISTP))
 (173 149 (:REWRITE DEFAULT-CAR))
 (121 89 (:REWRITE DEFAULT-CDR))
 (92 46 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (86 86 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (68 34 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (30 30 (:TYPE-PRESCRIPTION ALL-<))
 (20 20 (:REWRITE USE-ALL-<-2))
 (20 20 (:REWRITE USE-ALL-<))
 (20 20 (:REWRITE DEFAULT-<-2))
 (20 20 (:REWRITE DEFAULT-<-1))
 (20 10 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (16 16 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (12 6 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (10 10 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (10 10 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (10 10 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (10 10 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (10 10 (:REWRITE ALL-<-TRANSITIVE))
 )
(NATP-OF-CDR-OF-ASSOC-EQUAL-WHEN-DAG-VARIABLE-ALISTP
 (474 15 (:REWRITE USE-ALL-<-FOR-CAR))
 (354 15 (:REWRITE ALL-<-OF-STRIP-CDRS-OF-0-WHEN-DAG-VARIABLE-ALISTP))
 (295 260 (:REWRITE DEFAULT-CAR))
 (260 175 (:REWRITE DEFAULT-CDR))
 (190 95 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (187 187 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (156 78 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (45 45 (:TYPE-PRESCRIPTION ALL-<))
 (33 28 (:REWRITE DEFAULT-<-1))
 (30 15 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (28 28 (:REWRITE USE-ALL-<-2))
 (28 28 (:REWRITE USE-ALL-<))
 (28 28 (:REWRITE DEFAULT-<-2))
 (28 14 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (15 15 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (15 15 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (15 15 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (15 15 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (15 15 (:REWRITE ALL-<-TRANSITIVE))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(BOUNDED-DAG-VARIABLE-ALISTP)
(BOUNDED-DAG-VARIABLE-ALISTP-FORWARD-TO-DAG-VARIABLE-ALISTP)
(BOUNDED-DAG-VARIABLE-ALISTP-MONOTONE
 (18 3 (:DEFINITION STRIP-CDRS))
 (12 6 (:REWRITE DEFAULT-CDR))
 (10 1 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (6 3 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (3 3 (:REWRITE DEFAULT-CAR))
 (3 1 (:REWRITE USE-ALL-<))
 (2 2 (:TYPE-PRESCRIPTION MEMBERP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE USE-ALL-<-2))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 )
(BOUNDED-DAG-VARIABLE-ALISTP-OF-NIL)
(<-OF-LOOKUP-EQUAL-WHEN-BOUNDED-DAG-VARIABLE-ALISTP
 (56 1 (:DEFINITION NAT-LISTP))
 (51 1 (:DEFINITION NATP))
 (44 1 (:REWRITE USE-ALL-<-FOR-CAR))
 (25 1 (:REWRITE ALL-<-OF-STRIP-CDRS-OF-0-WHEN-DAG-VARIABLE-ALISTP))
 (24 4 (:DEFINITION STRIP-CDRS))
 (21 2 (:DEFINITION SYMBOL-ALISTP))
 (19 11 (:REWRITE DEFAULT-CDR))
 (12 6 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (11 11 (:REWRITE DEFAULT-CAR))
 (11 2 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (10 10 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (9 2 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (8 4 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (6 2 (:REWRITE ALL-<-TRANSITIVE))
 (5 3 (:REWRITE USE-ALL-<))
 (4 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE USE-ALL-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 2 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION MEMBERP))
 (2 2 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (2 1 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 )
(<-OF-CDR-OF-ASSOC-EQUAL-WHEN-BOUNDED-DAG-VARIABLE-ALISTP
 (159 7 (:REWRITE USE-ALL-<-FOR-CAR))
 (133 110 (:REWRITE DEFAULT-CAR))
 (81 60 (:REWRITE DEFAULT-CDR))
 (81 7 (:REWRITE ALL-<-OF-STRIP-CDRS-OF-0-WHEN-DAG-VARIABLE-ALISTP))
 (56 28 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (55 18 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (46 46 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (43 29 (:REWRITE USE-ALL-<))
 (38 29 (:REWRITE DEFAULT-<-2))
 (33 29 (:REWRITE DEFAULT-<-1))
 (33 19 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (30 15 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (29 29 (:REWRITE USE-ALL-<-2))
 (29 18 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (27 19 (:REWRITE ALL-<-TRANSITIVE))
 (19 19 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (14 14 (:TYPE-PRESCRIPTION MEMBERP))
 (14 7 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (13 13 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 12 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (12 12 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (6 3 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 )
(BOUNDED-DAG-VARIABLE-ALISTP-OF-CONS-OF-CONS
 (22 3 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (18 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (8 4 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (6 4 (:REWRITE DEFAULT-<-2))
 (6 3 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:REWRITE DEFAULT-CAR))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (4 4 (:REWRITE USE-ALL-<-2))
 (4 4 (:REWRITE USE-ALL-<))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (3 3 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (3 3 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (3 3 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (3 3 (:REWRITE ALL-<-TRANSITIVE))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE BOUNDED-DAG-VARIABLE-ALISTP-MONOTONE))
 )
