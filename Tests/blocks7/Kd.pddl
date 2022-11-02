(define (domain Kblocksworld)
(:requirements :strips :typing)
;;BestCase
(:types)
(:constants
 b1 - OBJ
 b2 - OBJ
 b3 - OBJ
 b4 - OBJ
 b5 - OBJ
 b6 - OBJ
 b7 - OBJ
)

(:predicates
(Kclear ?x - OBJ)
(KNclear ?x - OBJ)
(NotKclear ?x - OBJ)
(Kon-table ?x - OBJ)
(KNon-table ?x - OBJ)
(NotKon-table ?x - OBJ)
(Kon ?x - OBJ ?y - OBJ)
(KNon ?x - OBJ ?y - OBJ)
(NotKon ?x - OBJ ?y - OBJ)
)

(:action senseONT
 :parameters (?b1 - OBJ ?b2 - OBJ )
 :precondition 
(and (NotKon ?b1 ?b2))
 :effect 
(and (Kon ?b1 ?b2) (not (NotKon ?b1 ?b2)))
)
(:action senseONF
 :parameters (?b1 - OBJ ?b2 - OBJ )
 :precondition 
(and (NotKon ?b1 ?b2))
 :effect 
(and (KNon ?b1 ?b2) (not (NotKon ?b1 ?b2)))
)
(:action senseCLEART
 :parameters (?b1 - OBJ )
 :precondition 
(and (NotKclear ?b1))
 :effect 
(and (Kclear ?b1) (not (NotKclear ?b1)))
)
(:action senseCLEARF
 :parameters (?b1 - OBJ )
 :precondition 
(and (NotKclear ?b1))
 :effect 
(and (KNclear ?b1) (not (NotKclear ?b1)))
)
(:action senseONTABLET
 :parameters (?b1 - OBJ )
 :precondition 
(and (NotKon-table ?b1))
 :effect 
(and (Kon-table ?b1) (not (NotKon-table ?b1)))
)
(:action senseONTABLEF
 :parameters (?b1 - OBJ )
 :precondition 
(and (NotKon-table ?b1))
 :effect 
(and (KNon-table ?b1) (not (NotKon-table ?b1)))
)
(:action move-b-to-b
 :parameters (?bm - OBJ ?bf - OBJ ?bt - OBJ )
 :precondition 
(and (Kclear ?bm) (Kclear ?bt) (Kon ?bm ?bf))
 :effect 
(and (KNclear ?bt) (KNon ?bm ?bf) (Kon ?bm ?bt) (Kclear ?bf))
)
(:action move-to-t
 :parameters (?b - OBJ ?bf - OBJ )
 :precondition 
(and (Kclear ?b) (Kon ?b ?bf))
 :effect 
(and (Kon-table ?b) (KNon ?b ?bf) (Kclear ?bf))
)
(:action move-t-to-b
 :parameters (?bm - OBJ ?bt - OBJ )
 :precondition 
(and (Kclear ?bm) (Kclear ?bt) (Kon-table ?bm))
 :effect 
(and (KNclear ?bt) (KNon-table ?bm) (Kon ?bm ?bt))
)
(:action R0
:precondition (and(Kon b5 b2))
:effect (and(KNon b2 b5)(not (NotKon b2 b5)))
)
(:action R1
:precondition (and(Kon b2 b5))
:effect (and(KNon b5 b2)(not (NotKon b5 b2)))
)
(:action R2
:precondition (and(Kon b2 b5))
:effect (and(KNon b5 b2)(not (NotKon b5 b2)))
)
(:action R3
:precondition (and(Kon b5 b2))
:effect (and(KNon b2 b5)(not (NotKon b2 b5)))
)
(:action R4
:precondition (and(Kclear b2))
:effect (and(KNclear b5)(not (NotKclear b5)))
)
(:action R5
:precondition (and(KNclear b5))
:effect (and(Kclear b2)(not (NotKclear b2)))
)
(:action R6
:precondition (and(Kclear b5))
:effect (and(KNclear b2)(not (NotKclear b2)))
)
(:action R7
:precondition (and(KNclear b2))
:effect (and(Kclear b5)(not (NotKclear b5)))
)
(:action R8
:precondition (and(Kon-table b2))
:effect (and(KNon-table b5)(not (NotKon-table b5)))
)
(:action R9
:precondition (and(KNon-table b5))
:effect (and(Kon-table b2)(not (NotKon-table b2)))
)
(:action R10
:precondition (and(Kon-table b5))
:effect (and(KNon-table b2)(not (NotKon-table b2)))
)
(:action R11
:precondition (and(KNon-table b2))
:effect (and(Kon-table b5)(not (NotKon-table b5)))
)
(:action R12
:precondition (and(Kon-table b2))
:effect (and(KNon b2 b5)(not (NotKon b2 b5)))
)
(:action R13
:precondition (and(KNon b2 b5))
:effect (and(Kon-table b2)(not (NotKon-table b2)))
)
(:action R14
:precondition (and(Kon b2 b5))
:effect (and(KNon-table b2)(not (NotKon-table b2)))
)
(:action R15
:precondition (and(KNon-table b2))
:effect (and(Kon b2 b5)(not (NotKon b2 b5)))
)
(:action R16
:precondition (and(Kon-table b5))
:effect (and(KNon b5 b2)(not (NotKon b5 b2)))
)
(:action R17
:precondition (and(KNon b5 b2))
:effect (and(Kon-table b5)(not (NotKon-table b5)))
)
(:action R18
:precondition (and(Kon b5 b2))
:effect (and(KNon-table b5)(not (NotKon-table b5)))
)
(:action R19
:precondition (and(KNon-table b5))
:effect (and(Kon b5 b2)(not (NotKon b5 b2)))
)
(:action R20
:precondition (and(Kclear b2))
:effect (and(KNon b5 b2)(not (NotKon b5 b2)))
)
(:action R21
:precondition (and(KNon b5 b2))
:effect (and(Kclear b2)(not (NotKclear b2)))
)
(:action R22
:precondition (and(Kon b5 b2))
:effect (and(KNclear b2)(not (NotKclear b2)))
)
(:action R23
:precondition (and(KNclear b2))
:effect (and(Kon b5 b2)(not (NotKon b5 b2)))
)
(:action R24
:precondition (and(Kclear b5))
:effect (and(KNon b2 b5)(not (NotKon b2 b5)))
)
(:action R25
:precondition (and(KNon b2 b5))
:effect (and(Kclear b5)(not (NotKclear b5)))
)
(:action R26
:precondition (and(Kon b2 b5))
:effect (and(KNclear b5)(not (NotKclear b5)))
)
(:action R27
:precondition (and(KNclear b5))
:effect (and(Kon b2 b5)(not (NotKon b2 b5)))
)
(:action R28
:precondition (and(Kon b6 b1))
:effect (and(KNon b1 b6)(not (NotKon b1 b6)))
)
(:action R29
:precondition (and(Kon b1 b6))
:effect (and(KNon b6 b1)(not (NotKon b6 b1)))
)
(:action R30
:precondition (and(Kon b1 b6))
:effect (and(KNon b6 b1)(not (NotKon b6 b1)))
)
(:action R31
:precondition (and(Kon b6 b1))
:effect (and(KNon b1 b6)(not (NotKon b1 b6)))
)
(:action R32
:precondition (and(Kclear b1))
:effect (and(KNclear b6)(not (NotKclear b6)))
)
(:action R33
:precondition (and(KNclear b6))
:effect (and(Kclear b1)(not (NotKclear b1)))
)
(:action R34
:precondition (and(Kclear b6))
:effect (and(KNclear b1)(not (NotKclear b1)))
)
(:action R35
:precondition (and(KNclear b1))
:effect (and(Kclear b6)(not (NotKclear b6)))
)
(:action R36
:precondition (and(Kon b1 b3))
:effect (and(KNon b6 b3)(not (NotKon b6 b3)))
)
(:action R37
:precondition (and(KNon b6 b3))
:effect (and(Kon b1 b3)(not (NotKon b1 b3)))
)
(:action R38
:precondition (and(Kon b6 b3))
:effect (and(KNon b1 b3)(not (NotKon b1 b3)))
)
(:action R39
:precondition (and(KNon b1 b3))
:effect (and(Kon b6 b3)(not (NotKon b6 b3)))
)
(:action R40
:precondition (and(Kon b1 b3))
:effect (and(KNon b1 b6)(not (NotKon b1 b6)))
)
(:action R41
:precondition (and(KNon b1 b6))
:effect (and(Kon b1 b3)(not (NotKon b1 b3)))
)
(:action R42
:precondition (and(Kon b1 b6))
:effect (and(KNon b1 b3)(not (NotKon b1 b3)))
)
(:action R43
:precondition (and(KNon b1 b3))
:effect (and(Kon b1 b6)(not (NotKon b1 b6)))
)
(:action R44
:precondition (and(Kon b6 b3))
:effect (and(KNon b6 b1)(not (NotKon b6 b1)))
)
(:action R45
:precondition (and(KNon b6 b1))
:effect (and(Kon b6 b3)(not (NotKon b6 b3)))
)
(:action R46
:precondition (and(Kon b6 b1))
:effect (and(KNon b6 b3)(not (NotKon b6 b3)))
)
(:action R47
:precondition (and(KNon b6 b3))
:effect (and(Kon b6 b1)(not (NotKon b6 b1)))
)
(:action R48
:precondition (and(Kclear b1))
:effect (and(KNon b6 b1)(not (NotKon b6 b1)))
)
(:action R49
:precondition (and(KNon b6 b1))
:effect (and(Kclear b1)(not (NotKclear b1)))
)
(:action R50
:precondition (and(Kon b6 b1))
:effect (and(KNclear b1)(not (NotKclear b1)))
)
(:action R51
:precondition (and(KNclear b1))
:effect (and(Kon b6 b1)(not (NotKon b6 b1)))
)
(:action R52
:precondition (and(Kclear b6))
:effect (and(KNon b1 b6)(not (NotKon b1 b6)))
)
(:action R53
:precondition (and(KNon b1 b6))
:effect (and(Kclear b6)(not (NotKclear b6)))
)
(:action R54
:precondition (and(Kon b1 b6))
:effect (and(KNclear b6)(not (NotKclear b6)))
)
(:action R55
:precondition (and(KNclear b6))
:effect (and(Kon b1 b6)(not (NotKon b1 b6)))
)
(:action R56
:precondition (and(Kon b7 b4))
:effect (and(KNon b4 b7)(not (NotKon b4 b7)))
)
(:action R57
:precondition (and(Kon b4 b7))
:effect (and(KNon b7 b4)(not (NotKon b7 b4)))
)
(:action R58
:precondition (and(Kon b4 b7))
:effect (and(KNon b7 b4)(not (NotKon b7 b4)))
)
(:action R59
:precondition (and(Kon b7 b4))
:effect (and(KNon b4 b7)(not (NotKon b4 b7)))
)
(:action R60
:precondition (and(Kclear b4))
:effect (and(KNclear b7)(not (NotKclear b7)))
)
(:action R61
:precondition (and(KNclear b7))
:effect (and(Kclear b4)(not (NotKclear b4)))
)
(:action R62
:precondition (and(Kclear b7))
:effect (and(KNclear b4)(not (NotKclear b4)))
)
(:action R63
:precondition (and(KNclear b4))
:effect (and(Kclear b7)(not (NotKclear b7)))
)
(:action R64
:precondition (and(Kon-table b4))
:effect (and(KNon-table b7)(not (NotKon-table b7)))
)
(:action R65
:precondition (and(KNon-table b7))
:effect (and(Kon-table b4)(not (NotKon-table b4)))
)
(:action R66
:precondition (and(Kon-table b7))
:effect (and(KNon-table b4)(not (NotKon-table b4)))
)
(:action R67
:precondition (and(KNon-table b4))
:effect (and(Kon-table b7)(not (NotKon-table b7)))
)
(:action R68
:precondition (and(Kon-table b4))
:effect (and(KNon b4 b7)(not (NotKon b4 b7)))
)
(:action R69
:precondition (and(KNon b4 b7))
:effect (and(Kon-table b4)(not (NotKon-table b4)))
)
(:action R70
:precondition (and(Kon b4 b7))
:effect (and(KNon-table b4)(not (NotKon-table b4)))
)
(:action R71
:precondition (and(KNon-table b4))
:effect (and(Kon b4 b7)(not (NotKon b4 b7)))
)
(:action R72
:precondition (and(Kon-table b7))
:effect (and(KNon b7 b4)(not (NotKon b7 b4)))
)
(:action R73
:precondition (and(KNon b7 b4))
:effect (and(Kon-table b7)(not (NotKon-table b7)))
)
(:action R74
:precondition (and(Kon b7 b4))
:effect (and(KNon-table b7)(not (NotKon-table b7)))
)
(:action R75
:precondition (and(KNon-table b7))
:effect (and(Kon b7 b4)(not (NotKon b7 b4)))
)
(:action R76
:precondition (and(Kclear b4))
:effect (and(KNon b7 b4)(not (NotKon b7 b4)))
)
(:action R77
:precondition (and(KNon b7 b4))
:effect (and(Kclear b4)(not (NotKclear b4)))
)
(:action R78
:precondition (and(Kon b7 b4))
:effect (and(KNclear b4)(not (NotKclear b4)))
)
(:action R79
:precondition (and(KNclear b4))
:effect (and(Kon b7 b4)(not (NotKon b7 b4)))
)
(:action R80
:precondition (and(Kclear b7))
:effect (and(KNon b4 b7)(not (NotKon b4 b7)))
)
(:action R81
:precondition (and(KNon b4 b7))
:effect (and(Kclear b7)(not (NotKclear b7)))
)
(:action R82
:precondition (and(Kon b4 b7))
:effect (and(KNclear b7)(not (NotKclear b7)))
)
(:action R83
:precondition (and(KNclear b7))
:effect (and(Kon b4 b7)(not (NotKon b4 b7)))
)
)
