(C::VALUE-ARRAY->LENGTH)
(C::POSP-OF-VALUE-ARRAY->LENGTH)
(C::VALUE-ARRAY->LENGTH-OF-VALUE-FIX-ARRAY)
(C::VALUE-ARRAY->LENGTH-VALUE-EQUIV-CONGRUENCE-ON-ARRAY)
(C::VALUE-ARRAY-READ)
(C::VALUE-RESULTP-OF-VALUE-ARRAY-READ
 (88 14 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (77 11 (:DEFINITION LEN))
 (70 7 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (46 14 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (28 28 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (28 14 (:REWRITE DEFAULT-CDR))
 (26 26 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (25 17 (:REWRITE DEFAULT-<-2))
 (25 14 (:REWRITE DEFAULT-+-2))
 (20 17 (:REWRITE DEFAULT-<-1))
 (14 14 (:REWRITE DEFAULT-+-1))
 (14 7 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(C::VALUE-ARRAY-READ-OF-NFIX-INDEX)
(C::VALUE-ARRAY-READ-NAT-EQUIV-CONGRUENCE-ON-INDEX)
(C::VALUE-ARRAY-READ-OF-VALUE-FIX-ARRAY
 (68 12 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (32 12 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (24 24 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (22 14 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (16 8 (:REWRITE DEFAULT-CAR))
 (15 14 (:REWRITE DEFAULT-<-1))
 (10 4 (:REWRITE ZP-OPEN))
 (8 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(C::VALUE-ARRAY-READ-VALUE-EQUIV-CONGRUENCE-ON-ARRAY)
(C::VALUE-ARRAY-WRITE
 (119 17 (:DEFINITION LEN))
 (78 39 (:REWRITE DEFAULT-CDR))
 (42 21 (:REWRITE DEFAULT-CAR))
 (35 21 (:REWRITE DEFAULT-<-2))
 (35 18 (:REWRITE DEFAULT-+-2))
 (21 21 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE DEFAULT-+-1))
 (10 1 (:DEFINITION UPDATE-NTH))
 (8 8 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (1 1 (:REWRITE ZP-OPEN))
 )
(C::VALUE-RESULTP-OF-VALUE-ARRAY-WRITE)
(C::VALUE-KIND-OF-VALUE-ARRAY-WRITE
 (90 9 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (45 9 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (28 14 (:REWRITE DEFAULT-CDR))
 (27 27 (:TYPE-PRESCRIPTION C::VALUEP))
 (20 15 (:REWRITE DEFAULT-<-2))
 (20 10 (:REWRITE DEFAULT-CAR))
 (18 18 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (18 18 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (18 9 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (16 15 (:REWRITE DEFAULT-<-1))
 (8 8 (:TYPE-PRESCRIPTION C::VALUE-ARRAY->ELEMENTS$INLINE))
 (5 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(C::VALUE-ARRAY-WRITE-OF-NFIX-INDEX)
(C::VALUE-ARRAY-WRITE-NAT-EQUIV-CONGRUENCE-ON-INDEX)
(C::VALUE-ARRAY-WRITE-OF-VALUE-FIX-ELEM
 (108 20 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (76 30 (:REWRITE DEFAULT-CDR))
 (60 22 (:REWRITE DEFAULT-CAR))
 (48 20 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (40 40 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (32 32 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (22 14 (:REWRITE DEFAULT-<-2))
 (16 16 (:TYPE-PRESCRIPTION C::VALUE-ARRAY->ELEMENTS$INLINE))
 (15 14 (:REWRITE DEFAULT-<-1))
 (10 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(C::VALUE-ARRAY-WRITE-VALUE-EQUIV-CONGRUENCE-ON-ELEM)
(C::VALUE-ARRAY-WRITE-OF-VALUE-FIX-ARRAY
 (108 20 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (76 30 (:REWRITE DEFAULT-CDR))
 (60 22 (:REWRITE DEFAULT-CAR))
 (48 20 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (40 40 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (32 32 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (22 14 (:REWRITE DEFAULT-<-2))
 (16 16 (:TYPE-PRESCRIPTION C::VALUE-ARRAY->ELEMENTS$INLINE))
 (15 14 (:REWRITE DEFAULT-<-1))
 (10 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(C::VALUE-ARRAY-WRITE-VALUE-EQUIV-CONGRUENCE-ON-ARRAY)
