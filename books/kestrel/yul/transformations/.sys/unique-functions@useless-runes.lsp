(YUL::STATEMENT-UNIQUE-FUNS
 (48 16 (:REWRITE DEFAULT-<-2))
 (48 16 (:REWRITE DEFAULT-<-1))
 (48 12 (:REWRITE FTY::RESULTERRP-WHEN-RESULTERR-OPTIONP))
 (30 6 (:REWRITE FTY::RESULTERR-OPTIONP-WHEN-RESULTERRP))
 (19 8 (:TYPE-PRESCRIPTION SET::INSERT))
 (18 18 (:TYPE-PRESCRIPTION FTY::RESULTERR-OPTIONP))
 (18 2 (:REWRITE SET::IN-TAIL))
 (11 1 (:REWRITE SET::TAIL-WHEN-EMPTY))
 (9 2 (:REWRITE YUL::EMPTY-IDENTIFIER-SET-FIX))
 (7 7 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (6 6 (:REWRITE DEFAULT-CAR))
 (5 5 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-SETP))
 (4 4 (:REWRITE SET::IN-WHEN-MEMBER-EQUAL-OF-LIST-IN))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (3 1 (:REWRITE YUL::IDENTIFIER-SET-FIX-WHEN-IDENTIFIER-SETP))
 )
(YUL::STATEMENTS/BLOCKS/CASES/FUNDEFS-UNIQUE-FUNS-FLAG
 (122 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (72 72 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-SET-FIX))
 (48 16 (:REWRITE DEFAULT-<-2))
 (48 16 (:REWRITE DEFAULT-<-1))
 (48 12 (:REWRITE FTY::RESULTERRP-WHEN-RESULTERR-OPTIONP))
 (30 6 (:REWRITE FTY::RESULTERR-OPTIONP-WHEN-RESULTERRP))
 (18 18 (:TYPE-PRESCRIPTION FTY::RESULTERR-OPTIONP))
 (18 2 (:REWRITE SET::IN-TAIL))
 (12 6 (:TYPE-PRESCRIPTION SET::INSERT))
 (11 1 (:REWRITE SET::TAIL-WHEN-EMPTY))
 (9 2 (:REWRITE YUL::EMPTY-IDENTIFIER-SET-FIX))
 (7 7 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (6 6 (:REWRITE DEFAULT-CAR))
 (5 5 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-SETP))
 (4 4 (:REWRITE SET::IN-WHEN-MEMBER-EQUAL-OF-LIST-IN))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (3 1 (:REWRITE YUL::IDENTIFIER-SET-FIX-WHEN-IDENTIFIER-SETP))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(YUL::STATEMENTS/BLOCKS/CASES/FUNDEFS-UNIQUE-FUNS-FLAG-EQUIVALENCES)
(YUL::FLAG-LEMMA-FOR-RETURN-TYPE-OF-STATEMENT-UNIQUE-FUNS.NEW-FUNS
 (180 20 (:REWRITE SET::IN-TAIL))
 (123 25 (:REWRITE YUL::EMPTY-IDENTIFIER-SET-FIX))
 (110 10 (:REWRITE SET::TAIL-WHEN-EMPTY))
 (92 92 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (76 26 (:REWRITE YUL::IDENTIFIER-SET-FIX-WHEN-IDENTIFIER-SETP))
 (74 74 (:REWRITE DEFAULT-CAR))
 (48 5 (:REWRITE SET::INSERT-WHEN-EMPTY))
 (44 44 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-SET-FIX))
 (40 40 (:REWRITE SET::IN-WHEN-MEMBER-EQUAL-OF-LIST-IN))
 (40 10 (:REWRITE SET::NEVER-IN-EMPTY))
 (30 30 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE SET::INSERT-IDENTITY))
 )
(YUL::RETURN-TYPE-OF-STATEMENT-UNIQUE-FUNS.NEW-FUNS)
(YUL::RETURN-TYPE-OF-STATEMENT-LIST-UNIQUE-FUNS.NEW-FUNS)
(YUL::RETURN-TYPE-OF-BLOCK-UNIQUE-FUNS.NEW-FUNS)
(YUL::RETURN-TYPE-OF-BLOCK-OPTION-UNIQUE-FUNS.NEW-FUNS)
(YUL::RETURN-TYPE-OF-SWCASE-UNIQUE-FUNS.NEW-FUNS)
(YUL::RETURN-TYPE-OF-SWCASE-LIST-UNIQUE-FUNS.NEW-FUNS)
(YUL::RETURN-TYPE-OF-FUNDEF-UNIQUE-FUNS.NEW-FUNS)
(YUL::STATEMENT-UNIQUE-FUNS
 (96 24 (:REWRITE FTY::RESULTERRP-WHEN-RESULTERR-OPTIONP))
 (73 1 (:DEFINITION YUL::STATEMENT-UNIQUE-FUNS))
 (60 12 (:REWRITE FTY::RESULTERR-OPTIONP-WHEN-RESULTERRP))
 (36 36 (:TYPE-PRESCRIPTION FTY::RESULTERR-OPTIONP))
 (24 24 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (22 1 (:DEFINITION YUL::SWCASE-LIST-UNIQUE-FUNS))
 (19 19 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-SET-FIX))
 (12 4 (:REWRITE SET::IN-TAIL))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (8 8 (:REWRITE SET::IN-WHEN-MEMBER-EQUAL-OF-LIST-IN))
 (8 8 (:REWRITE YUL::FUNDEFP-WHEN-MEMBER-EQUAL-OF-FUNDEF-LISTP))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 3 (:REWRITE SET::NEVER-IN-EMPTY))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTY))
 (3 1 (:REWRITE SET::SFIX-WHEN-EMPTY))
 (3 1 (:REWRITE SET::INSERT-WHEN-EMPTY))
 (2 2 (:DEFINITION YUL::BLOCK-UNIQUE-FUNS))
 (1 1 (:REWRITE YUL::SWCASE-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE YUL::STATEMENT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SET::INSERT-IDENTITY))
 (1 1 (:DEFINITION YUL::SWCASE-UNIQUE-FUNS))
 )
(YUL::FLAG-LEMMA-FOR-STATEMENT-UNIQUE-FUNS-OF-STATEMENT-FIX-STMT
 (1560 129 (:REWRITE YUL::STATEMENT-FIX-WHEN-STATEMENTP))
 (1236 924 (:REWRITE DEFAULT-CAR))
 (645 129 (:REWRITE YUL::STATEMENTP-WHEN-STATEMENT-OPTIONP))
 (635 73 (:REWRITE YUL::SWCASE-FIX-WHEN-SWCASEP))
 (520 394 (:REWRITE DEFAULT-CDR))
 (387 387 (:TYPE-PRESCRIPTION YUL::STATEMENTP))
 (362 362 (:REWRITE YUL::SWCASE-LISTP-WHEN-SUBSETP-EQUAL))
 (362 362 (:REWRITE YUL::STATEMENT-LISTP-WHEN-SUBSETP-EQUAL))
 (328 40 (:REWRITE SET::IN-TAIL))
 (270 45 (:REWRITE YUL::SWCASEP-OF-CAR-WHEN-SWCASE-LISTP))
 (270 45 (:REWRITE YUL::STATEMENTP-OF-CAR-WHEN-STATEMENT-LISTP))
 (258 258 (:TYPE-PRESCRIPTION YUL::STATEMENT-OPTIONP))
 (258 258 (:REWRITE YUL::STATEMENTP-WHEN-MEMBER-EQUAL-OF-STATEMENT-LISTP))
 (258 129 (:REWRITE YUL::STATEMENT-OPTIONP-WHEN-STATEMENTP))
 (198 18 (:REWRITE SET::TAIL-WHEN-EMPTY))
 (185 181 (:REWRITE YUL::SWCASE-LISTP-WHEN-NOT-CONSP))
 (185 181 (:REWRITE YUL::STATEMENT-LISTP-WHEN-NOT-CONSP))
 (181 41 (:REWRITE YUL::EMPTY-IDENTIFIER-SET-FIX))
 (180 30 (:REWRITE YUL::SWCASE-LISTP-OF-CDR-WHEN-SWCASE-LISTP))
 (180 30 (:REWRITE YUL::STATEMENT-LISTP-OF-CDR-WHEN-STATEMENT-LISTP))
 (146 146 (:TYPE-PRESCRIPTION YUL::SWCASEP))
 (146 146 (:REWRITE YUL::SWCASEP-WHEN-MEMBER-EQUAL-OF-SWCASE-LISTP))
 (142 142 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (80 80 (:REWRITE SET::IN-WHEN-MEMBER-EQUAL-OF-LIST-IN))
 (76 22 (:REWRITE SET::NEVER-IN-EMPTY))
 (34 8 (:REWRITE SET::INSERT-WHEN-EMPTY))
 (28 8 (:REWRITE YUL::BLOCKP-WHEN-BLOCK-OPTIONP))
 (28 8 (:REWRITE YUL::BLOCK-OPTIONP-WHEN-BLOCKP))
 (18 18 (:REWRITE YUL::FUNDEFP-WHEN-MEMBER-EQUAL-OF-FUNDEF-LISTP))
 (8 8 (:REWRITE SET::INSERT-IDENTITY))
 (8 6 (:REWRITE YUL::BLOCK-OPTION-FIX-WHEN-NONE))
 (4 1 (:REWRITE SET::SFIX-WHEN-EMPTY))
 (3 3 (:TYPE-PRESCRIPTION YUL::IDENTIFIER-SET-FIX))
 (2 2 (:TYPE-PRESCRIPTION YUL::STATEMENT-SWITCH->DEFAULT$INLINE))
 )
(YUL::STATEMENT-UNIQUE-FUNS-OF-STATEMENT-FIX-STMT)
(YUL::STATEMENT-UNIQUE-FUNS-OF-IDENTIFIER-SET-FIX-FUNS)
(YUL::STATEMENT-LIST-UNIQUE-FUNS-OF-STATEMENT-LIST-FIX-STMTS)
(YUL::STATEMENT-LIST-UNIQUE-FUNS-OF-IDENTIFIER-SET-FIX-FUNS)
(YUL::BLOCK-UNIQUE-FUNS-OF-BLOCK-FIX-BLOCK)
(YUL::BLOCK-UNIQUE-FUNS-OF-IDENTIFIER-SET-FIX-FUNS)
(YUL::BLOCK-OPTION-UNIQUE-FUNS-OF-BLOCK-OPTION-FIX-BLOCK?)
(YUL::BLOCK-OPTION-UNIQUE-FUNS-OF-IDENTIFIER-SET-FIX-FUNS)
(YUL::SWCASE-UNIQUE-FUNS-OF-SWCASE-FIX-CASE)
(YUL::SWCASE-UNIQUE-FUNS-OF-IDENTIFIER-SET-FIX-FUNS)
(YUL::SWCASE-LIST-UNIQUE-FUNS-OF-SWCASE-LIST-FIX-CASES)
(YUL::SWCASE-LIST-UNIQUE-FUNS-OF-IDENTIFIER-SET-FIX-FUNS)
(YUL::FUNDEF-UNIQUE-FUNS-OF-FUNDEF-FIX-FUNDEF)
(YUL::FUNDEF-UNIQUE-FUNS-OF-IDENTIFIER-SET-FIX-FUNS)
(YUL::STATEMENT-UNIQUE-FUNS-STATEMENT-EQUIV-CONGRUENCE-ON-STMT)
(YUL::STATEMENT-UNIQUE-FUNS-IDENTIFIER-SET-EQUIV-CONGRUENCE-ON-FUNS)
(YUL::STATEMENT-LIST-UNIQUE-FUNS-STATEMENT-LIST-EQUIV-CONGRUENCE-ON-STMTS)
(YUL::STATEMENT-LIST-UNIQUE-FUNS-IDENTIFIER-SET-EQUIV-CONGRUENCE-ON-FUNS)
(YUL::BLOCK-UNIQUE-FUNS-BLOCK-EQUIV-CONGRUENCE-ON-BLOCK)
(YUL::BLOCK-UNIQUE-FUNS-IDENTIFIER-SET-EQUIV-CONGRUENCE-ON-FUNS)
(YUL::BLOCK-OPTION-UNIQUE-FUNS-BLOCK-OPTION-EQUIV-CONGRUENCE-ON-BLOCK?)
(YUL::BLOCK-OPTION-UNIQUE-FUNS-IDENTIFIER-SET-EQUIV-CONGRUENCE-ON-FUNS)
(YUL::SWCASE-UNIQUE-FUNS-SWCASE-EQUIV-CONGRUENCE-ON-CASE)
(YUL::SWCASE-UNIQUE-FUNS-IDENTIFIER-SET-EQUIV-CONGRUENCE-ON-FUNS)
(YUL::SWCASE-LIST-UNIQUE-FUNS-SWCASE-LIST-EQUIV-CONGRUENCE-ON-CASES)
(YUL::SWCASE-LIST-UNIQUE-FUNS-IDENTIFIER-SET-EQUIV-CONGRUENCE-ON-FUNS)
(YUL::FUNDEF-UNIQUE-FUNS-FUNDEF-EQUIV-CONGRUENCE-ON-FUNDEF)
(YUL::FUNDEF-UNIQUE-FUNS-IDENTIFIER-SET-EQUIV-CONGRUENCE-ON-FUNS)
