(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(SYMBOL-LISTP-OF-CONS)
(SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP)
(SYMBOL-LISTP-WHEN-NOT-CONSP)
(SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP)
(TRUE-LISTP-WHEN-SYMBOL-LISTP)
(SYMBOL-LISTP-OF-LIST-FIX)
(SYMBOL-LISTP-OF-SFIX)
(SYMBOL-LISTP-OF-INSERT)
(SYMBOL-LISTP-OF-DELETE)
(SYMBOL-LISTP-OF-MERGESORT)
(SYMBOL-LISTP-OF-UNION)
(SYMBOL-LISTP-OF-INTERSECT-1)
(SYMBOL-LISTP-OF-INTERSECT-2)
(SYMBOL-LISTP-OF-DIFFERENCE)
(SYMBOL-LISTP-OF-DUPLICATED-MEMBERS)
(SYMBOL-LISTP-OF-REV)
(SYMBOL-LISTP-OF-APPEND)
(SYMBOL-LISTP-OF-RCONS)
(SYMBOLP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LISTP)
(SYMBOL-LISTP-WHEN-SUBSETP-EQUAL)
(SYMBOL-LISTP-OF-SET-DIFFERENCE-EQUAL)
(SYMBOL-LISTP-OF-INTERSECTION-EQUAL-1)
(SYMBOL-LISTP-OF-INTERSECTION-EQUAL-2)
(SYMBOL-LISTP-OF-UNION-EQUAL)
(SYMBOL-LISTP-OF-TAKE)
(SYMBOL-LISTP-OF-REPEAT)
(SYMBOLP-OF-NTH-WHEN-SYMBOL-LISTP)
(SYMBOL-LISTP-OF-UPDATE-NTH)
(SYMBOL-LISTP-OF-BUTLAST)
(SYMBOL-LISTP-OF-NTHCDR)
(SYMBOL-LISTP-OF-LAST)
(SYMBOL-LISTP-OF-REMOVE)
(SYMBOL-LISTP-OF-REVAPPEND)
(TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE)
(SYMBOL-LISTP-OF-REMOVE-EQUAL)
(SYMBOL-LISTP-OF-REMOVE1-EQUAL
 (42 2 (:REWRITE SUBSETP-OF-CONS))
 (15 1 (:DEFINITION MEMBER-EQUAL))
 (14 14 (:REWRITE SUBSETP-TRANS2))
 (14 14 (:REWRITE SUBSETP-TRANS))
 (11 11 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (8 8 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (7 7 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE SUBSETP-MEMBER . 2))
 (2 2 (:REWRITE SUBSETP-MEMBER . 1))
 )
(SYMBOL-LISTP-OF-MAKE-LIST-AC
 (17 17 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (17 1 (:DEFINITION BINARY-APPEND))
 (16 4 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LISTP))
 (12 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (10 4 (:REWRITE CONSP-OF-REPEAT))
 (8 1 (:DEFINITION MEMBER-EQUAL))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (5 2 (:REWRITE DEFAULT-CDR))
 (5 2 (:REWRITE DEFAULT-CAR))
 (4 4 (:TYPE-PRESCRIPTION MAKE-LIST-AC))
 (4 1 (:REWRITE REPEAT-WHEN-ZP))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SUBSETP-MEMBER . 2))
 (2 2 (:REWRITE SUBSETP-MEMBER . 1))
 )
(EQLABLE-LISTP-WHEN-SYMBOL-LISTP)
