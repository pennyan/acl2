(S-ALL)
(S-ALL-OF-S-DIFF
 (150 75 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (146 73 (:REWRITE G-WHEN-NOT-IN-RKEYS-CHEAP))
 (75 75 (:TYPE-PRESCRIPTION BOOLEANP))
 (75 75 (:REWRITE CLR-DIFFERENTIAL))
 (58 14 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (42 2 (:DEFINITION SUBSETP-EQUAL))
 (28 28 (:REWRITE DEFAULT-CAR))
 (28 14 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (28 2 (:REWRITE MEMBER-EQUAL-BECOMES-MEMBERP))
 (26 2 (:REWRITE CLR-WHEN-NOT-IN-RKEYS))
 (21 21 (:REWRITE DEFAULT-CDR))
 (14 14 (:TYPE-PRESCRIPTION LEN))
 (14 14 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (14 14 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (14 14 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (14 14 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (12 12 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (9 9 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (6 2 (:REWRITE SET::NEVER-IN-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (4 4 (:REWRITE SET::SUBSET-IN-2))
 (4 4 (:REWRITE SET::SUBSET-IN))
 (4 2 (:REWRITE SET::IN-TAIL))
 (4 1 (:REWRITE EQUAL-S-RECORD-EQUALITY))
 (2 2 (:REWRITE SET::SUBSET-IN-2-ALT))
 )
(ADD-TO-ALL)
(LEADERS-AFTER-BRANCH-OR-RETURN)
(SUCCESSORS-OF-INSTRUCTION)
(FIND-LEADER-PCS-AUX
 (12 6 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(FIND-LEADER-PCS)
(FIND-BASIC-BLOCKS-AUX)
(FIND-BASIC-BLOCKS)
(GET-PC-AFTER-PC)
(PAIR-BLOCKS-WITH-SUCCESSORS-AUX
 (6 6 (:TYPE-PRESCRIPTION LAST))
 )
(PAIR-BLOCKS-WITH-SUCCESSORS)
(ADD-VALUE-FOR-KEYS)
(PAIR-BLOCKS-WITH-PREDECESSORS-AUX)
(PAIR-BLOCKS-WITH-PREDECESSORS)
(FIND-COMMON-DOMS)
(REMOVE-SOME-DOMINATORS)
(DOMINATOR-MAP-AUX
 (242 1 (:DEFINITION REMOVE-SOME-DOMINATORS))
 (182 3 (:DEFINITION UNION-EQUAL))
 (120 4 (:DEFINITION FIND-COMMON-DOMS))
 (84 4 (:DEFINITION INTERSECTION-EQUAL))
 (75 5 (:REWRITE MEMBER-EQUAL-BECOMES-MEMBERP))
 (56 36 (:REWRITE DEFAULT-CAR))
 (56 4 (:DEFINITION ASSOC-EQUAL))
 (28 28 (:REWRITE DEFAULT-CDR))
 (23 23 (:TYPE-PRESCRIPTION MEMBERP))
 (18 9 (:REWRITE G-WHEN-NOT-IN-RKEYS-CHEAP))
 (13 6 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (12 4 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (11 1 (:REWRITE S-SAME-G-STRONG))
 (9 9 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (8 8 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (8 4 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (6 6 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (6 6 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (6 6 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (6 6 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (6 6 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (6 6 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (6 6 (:REWRITE CLR-DIFFERENTIAL))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (4 4 (:REWRITE WFR-HACK5))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CDR-CONS))
 (2 2 (:REWRITE CAR-CONS))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(DOMINATOR-MAP)
(MAKE-EDGES)
(SPLIT-PAIRS)
(FIND-BACK-EDGES)
(FIND-NATURAL-LOOP-AUX
 (8 4 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(FIND-NATURAL-LOOP)
(FIND-NATURAL-LOOPS)
(GET-PCS-FOR-LOOP
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(GET-PCS-FOR-LOOPS)
(GROUP-LOOPS-AUX)
(GROUP-LOOPS)
(DECOMPOSE-INTO-LOOPS)
