(BV-TERM-SIZE
 (809 373 (:REWRITE DEFAULT-+-2))
 (690 84 (:DEFINITION LENGTH))
 (510 102 (:DEFINITION LEN))
 (480 373 (:REWRITE DEFAULT-+-1))
 (272 272 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (240 60 (:REWRITE COMMUTATIVITY-OF-+))
 (240 60 (:DEFINITION INTEGER-ABS))
 (208 208 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (192 192 (:TYPE-PRESCRIPTION LEN))
 (192 170 (:REWRITE DEFAULT-<-2))
 (178 170 (:REWRITE DEFAULT-<-1))
 (62 62 (:REWRITE DEFAULT-UNARY-MINUS))
 (54 18 (:DEFINITION SYMBOL-LISTP))
 (48 48 (:REWRITE DEFAULT-COERCE-2))
 (48 48 (:REWRITE DEFAULT-COERCE-1))
 (30 30 (:REWRITE DEFAULT-REALPART))
 (30 30 (:REWRITE DEFAULT-NUMERATOR))
 (30 30 (:REWRITE DEFAULT-IMAGPART))
 (30 30 (:REWRITE DEFAULT-DENOMINATOR))
 (18 18 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 )
(BIND-VAR-TO-BV-TERM-SIZE)
(BIND-VAR-TO-BV-TERM-SIZE-IF-TRIMMABLE)
(TERM-SHOULD-BE-TRIMMED-HELPER
 (50 6 (:DEFINITION LENGTH))
 (40 8 (:DEFINITION LEN))
 (34 34 (:REWRITE DEFAULT-CDR))
 (32 32 (:REWRITE DEFAULT-CAR))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (16 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (8 4 (:DEFINITION TRUE-LISTP))
 (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(TERM-SHOULD-BE-TRIMMED)
