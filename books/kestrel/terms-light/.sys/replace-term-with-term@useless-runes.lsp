(REPLACE-TERM-WITH-TERM
 (508 213 (:REWRITE DEFAULT-+-2))
 (305 213 (:REWRITE DEFAULT-+-1))
 (156 12 (:DEFINITION INTERSECTION-EQUAL))
 (152 38 (:DEFINITION INTEGER-ABS))
 (152 19 (:DEFINITION LENGTH))
 (95 19 (:DEFINITION LEN))
 (62 44 (:REWRITE DEFAULT-<-2))
 (60 12 (:DEFINITION MEMBER-EQUAL))
 (48 44 (:REWRITE DEFAULT-<-1))
 (38 38 (:REWRITE DEFAULT-UNARY-MINUS))
 (19 19 (:TYPE-PRESCRIPTION LEN))
 (19 19 (:REWRITE DEFAULT-REALPART))
 (19 19 (:REWRITE DEFAULT-NUMERATOR))
 (19 19 (:REWRITE DEFAULT-IMAGPART))
 (19 19 (:REWRITE DEFAULT-DENOMINATOR))
 (19 19 (:REWRITE DEFAULT-COERCE-2))
 (19 19 (:REWRITE DEFAULT-COERCE-1))
 (12 12 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (12 12 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 )
(LEN-OF-REPLACE-TERM-WITH-TERM-LST
 (48 24 (:REWRITE DEFAULT-+-2))
 (38 37 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE DEFAULT-+-1))
 (11 11 (:REWRITE DEFAULT-CAR))
 )
(FLAG-REPLACE-TERM-WITH-TERM
 (861 383 (:REWRITE DEFAULT-+-2))
 (542 383 (:REWRITE DEFAULT-+-1))
 (296 74 (:DEFINITION INTEGER-ABS))
 (296 37 (:DEFINITION LENGTH))
 (185 37 (:DEFINITION LEN))
 (156 12 (:DEFINITION INTERSECTION-EQUAL))
 (121 90 (:REWRITE DEFAULT-<-2))
 (104 90 (:REWRITE DEFAULT-<-1))
 (74 74 (:REWRITE DEFAULT-UNARY-MINUS))
 (60 12 (:DEFINITION MEMBER-EQUAL))
 (37 37 (:TYPE-PRESCRIPTION LEN))
 (37 37 (:REWRITE DEFAULT-REALPART))
 (37 37 (:REWRITE DEFAULT-NUMERATOR))
 (37 37 (:REWRITE DEFAULT-IMAGPART))
 (37 37 (:REWRITE DEFAULT-DENOMINATOR))
 (37 37 (:REWRITE DEFAULT-COERCE-2))
 (37 37 (:REWRITE DEFAULT-COERCE-1))
 (32 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (12 12 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (12 12 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-REPLACE-TERM-WITH-TERM-EQUIVALENCES)
(FLAG-LEMMA-FOR-PSEUDO-TERMP-OF-REPLACE-TERM-WITH-TERM
 (1496 1476 (:REWRITE DEFAULT-CDR))
 (674 337 (:REWRITE DEFAULT-+-2))
 (337 337 (:REWRITE DEFAULT-+-1))
 (190 38 (:DEFINITION MEMBER-EQUAL))
 (179 179 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (149 149 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (63 63 (:REWRITE DEFAULT-COERCE-2))
 (63 63 (:REWRITE DEFAULT-COERCE-1))
 (38 38 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION MAKE-LAMBDA-APPLICATION-SIMPLE))
 )
(PSEUDO-TERMP-OF-REPLACE-TERM-WITH-TERM)
(PSEUDO-TERM-LISTP-OF-REPLACE-TERM-WITH-TERM-LST)
(REPLACE-TERM-WITH-TERM
 (759 759 (:REWRITE DEFAULT-CDR))
 (631 631 (:REWRITE DEFAULT-CAR))
 (494 38 (:DEFINITION INTERSECTION-EQUAL))
 (322 161 (:REWRITE DEFAULT-+-2))
 (190 38 (:DEFINITION MEMBER-EQUAL))
 (161 161 (:REWRITE DEFAULT-+-1))
 (76 76 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (51 51 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (40 40 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (38 38 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (32 32 (:REWRITE DEFAULT-COERCE-2))
 (32 32 (:REWRITE DEFAULT-COERCE-1))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
