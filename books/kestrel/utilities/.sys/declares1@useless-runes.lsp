(SUBSTITUTE-MEASURE-IN-XARGS)
(SUBSTITUTE-MEASURE-IN-DECLARE-ARGS)
(SUBSTITUTE-MEASURE-IN-DECLARES)
(SUBSTITUTE-VARS-IN-MEASURE-IN-XARGS)
(SUBSTITUTE-VARS-IN-MEASURE-IN-DECLARE-ARGS)
(SUBSTITUTE-VARS-IN-MEASURE-IN-DECLARES)
(UNTRANSLATED-NILP)
(GET-CONJUNCTS-OF-UNTRANSLATED-TERM
 (963 481 (:REWRITE DEFAULT-+-2))
 (611 481 (:REWRITE DEFAULT-+-1))
 (352 88 (:REWRITE COMMUTATIVITY-OF-+))
 (352 88 (:DEFINITION INTEGER-ABS))
 (352 44 (:DEFINITION LENGTH))
 (303 303 (:REWRITE DEFAULT-CDR))
 (117 117 (:REWRITE DEFAULT-CAR))
 (106 96 (:REWRITE DEFAULT-<-2))
 (104 96 (:REWRITE DEFAULT-<-1))
 (88 88 (:REWRITE DEFAULT-UNARY-MINUS))
 (56 28 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (44 44 (:REWRITE DEFAULT-REALPART))
 (44 44 (:REWRITE DEFAULT-NUMERATOR))
 (44 44 (:REWRITE DEFAULT-IMAGPART))
 (44 44 (:REWRITE DEFAULT-DENOMINATOR))
 (44 44 (:REWRITE DEFAULT-COERCE-2))
 (44 44 (:REWRITE DEFAULT-COERCE-1))
 (30 30 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (4 2 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(DROP-UNTRANSLATED-TERMS-THAT-MENTION-VARS)
(DROP-GUARD-CONJUNCTS-THAT-MENTION-VARS)
(DROP-GUARD-CONJUNCTS-THAT-MENTION-VARS-IN-XARGS
 (115 54 (:REWRITE DEFAULT-+-2))
 (76 54 (:REWRITE DEFAULT-+-1))
 (40 10 (:REWRITE COMMUTATIVITY-OF-+))
 (40 10 (:DEFINITION INTEGER-ABS))
 (40 5 (:DEFINITION LENGTH))
 (25 5 (:DEFINITION LEN))
 (24 24 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:REWRITE DEFAULT-CAR))
 (12 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:TYPE-PRESCRIPTION LEN))
 (5 5 (:REWRITE DEFAULT-REALPART))
 (5 5 (:REWRITE DEFAULT-NUMERATOR))
 (5 5 (:REWRITE DEFAULT-IMAGPART))
 (5 5 (:REWRITE DEFAULT-DENOMINATOR))
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (5 5 (:REWRITE DEFAULT-COERCE-1))
 (3 1 (:DEFINITION SYMBOL-LISTP))
 )
(DROP-GUARD-CONJUNCTS-THAT-MENTION-VARS-IN-DECLARE-ARGS
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(DROP-GUARD-CONJUNCTS-THAT-MENTION-VARS-IN-DECLARES)
