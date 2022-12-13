(define (domain Kmedicalpks10)
(:requirements :strips :typing)
(:types
 TAG_TYPE VALUE_TYPE
)
(:constants
 i0 - illness
 i1 - illness
 i2 - illness
 i3 - illness
 i4 - illness
 i5 - illness
 i6 - illness
 i7 - illness
 i8 - illness
 i9 - illness
 i10 - illness
 s0 - stain
 s1 - stain
 s2 - stain
 s3 - stain
 s4 - stain
 s5 - stain
 s6 - stain
 s7 - stain
 s8 - stain
 s9 - stain
 s10 - stain
 tag0 - TAG_TYPE ; (ill i0) (not (ill i1))
 tag1 - TAG_TYPE ; (not (ill i0)) (ill i1)
 V_TRUE - VALUE_TYPE
 V_FALSE - VALUE_TYPE
)

(:predicates
(observed )
(ndead)
(stained)
(stain ?i - stain)
(Kstain ?i - stain)
(KNstain ?i - stain)
(KGivenstain ?i - stain ?TAG_PARAM - TAG_TYPE ?V_PARAM - VALUE_TYPE)
(ill ?i - illness)
(Kill ?i - illness)
(KNill ?i - illness)
(KGivenill ?i - illness ?TAG_PARAM - TAG_TYPE ?V_PARAM - VALUE_TYPE)
(KNot ?TAG_PARAM - TAG_TYPE)
)

(:action inspect-stain-T
:parameters ( ?i - stain)
:precondition 
(and (stained ) (stain ?i) (not (Kstain ?i)) (not (KNstain ?i)))
:effect 
(and (Kstain ?i) (observed ))
)
(:action inspect-stain-F
:parameters ( ?i - stain)
:precondition 
(and (stained ) (not (stain ?i)) (not (Kstain ?i)) (not (KNstain ?i)))
:effect 
(and (KNstain ?i) (observed ))
)
(:action medicate1
:precondition 
(and (ill i1) (Kill i1))
:effect 
(and 
	
	(when (ill i1) (ill i0))
	
	(when (Kill i1) 
		(and (Kill i0) (not (KNill i0))))
	
	(when (not (KNill i1)) (not (KNill i0)))
	
	(when (KGivenill i1 tag0 V_TRUE) (KGivenill i0 tag0 V_TRUE))
	
	(when (not (KGivenill i1 tag0 V_FALSE)) (not (KGivenill i0 tag0 V_FALSE)))
	
	(when (KGivenill i1 tag1 V_TRUE) (KGivenill i0 tag1 V_TRUE))
	
	(when (not (KGivenill i1 tag1 V_FALSE)) (not (KGivenill i0 tag1 V_FALSE))))
)
(:action medicate2
:precondition 
(and (ill i2) (Kill i2))
:effect 
(and 
	
	(when (ill i2) (ill i0))
	
	(when (Kill i2) 
		(and (Kill i0) (not (KNill i0))))
	
	(when (not (KNill i2)) (not (KNill i0)))
	
	(when (KGivenill i2 tag0 V_TRUE) (KGivenill i0 tag0 V_TRUE))
	
	(when (not (KGivenill i2 tag0 V_FALSE)) (not (KGivenill i0 tag0 V_FALSE)))
	
	(when (KGivenill i2 tag1 V_TRUE) (KGivenill i0 tag1 V_TRUE))
	
	(when (not (KGivenill i2 tag1 V_FALSE)) (not (KGivenill i0 tag1 V_FALSE))))
)
(:action medicate3
:precondition 
(and (ill i3) (Kill i3))
:effect 
(and 
	
	(when (ill i3) (ill i0))
	
	(when (Kill i3) 
		(and (Kill i0) (not (KNill i0))))
	
	(when (not (KNill i3)) (not (KNill i0)))
	
	(when (KGivenill i3 tag0 V_TRUE) (KGivenill i0 tag0 V_TRUE))
	
	(when (not (KGivenill i3 tag0 V_FALSE)) (not (KGivenill i0 tag0 V_FALSE)))
	
	(when (KGivenill i3 tag1 V_TRUE) (KGivenill i0 tag1 V_TRUE))
	
	(when (not (KGivenill i3 tag1 V_FALSE)) (not (KGivenill i0 tag1 V_FALSE))))
)
(:action medicate4
:precondition 
(and (ill i4) (Kill i4))
:effect 
(and 
	
	(when (ill i4) (ill i0))
	
	(when (Kill i4) 
		(and (Kill i0) (not (KNill i0))))
	
	(when (not (KNill i4)) (not (KNill i0)))
	
	(when (KGivenill i4 tag0 V_TRUE) (KGivenill i0 tag0 V_TRUE))
	
	(when (not (KGivenill i4 tag0 V_FALSE)) (not (KGivenill i0 tag0 V_FALSE)))
	
	(when (KGivenill i4 tag1 V_TRUE) (KGivenill i0 tag1 V_TRUE))
	
	(when (not (KGivenill i4 tag1 V_FALSE)) (not (KGivenill i0 tag1 V_FALSE))))
)
(:action medicate5
:precondition 
(and (ill i5) (Kill i5))
:effect 
(and 
	
	(when (ill i5) (ill i0))
	
	(when (Kill i5) 
		(and (Kill i0) (not (KNill i0))))
	
	(when (not (KNill i5)) (not (KNill i0)))
	
	(when (KGivenill i5 tag0 V_TRUE) (KGivenill i0 tag0 V_TRUE))
	
	(when (not (KGivenill i5 tag0 V_FALSE)) (not (KGivenill i0 tag0 V_FALSE)))
	
	(when (KGivenill i5 tag1 V_TRUE) (KGivenill i0 tag1 V_TRUE))
	
	(when (not (KGivenill i5 tag1 V_FALSE)) (not (KGivenill i0 tag1 V_FALSE))))
)
(:action medicate6
:precondition 
(and (ill i6) (Kill i6))
:effect 
(and 
	
	(when (ill i6) (ill i0))
	
	(when (Kill i6) 
		(and (Kill i0) (not (KNill i0))))
	
	(when (not (KNill i6)) (not (KNill i0)))
	
	(when (KGivenill i6 tag0 V_TRUE) (KGivenill i0 tag0 V_TRUE))
	
	(when (not (KGivenill i6 tag0 V_FALSE)) (not (KGivenill i0 tag0 V_FALSE)))
	
	(when (KGivenill i6 tag1 V_TRUE) (KGivenill i0 tag1 V_TRUE))
	
	(when (not (KGivenill i6 tag1 V_FALSE)) (not (KGivenill i0 tag1 V_FALSE))))
)
(:action medicate7
:precondition 
(and (ill i7) (Kill i7))
:effect 
(and 
	
	(when (ill i7) (ill i0))
	
	(when (Kill i7) 
		(and (Kill i0) (not (KNill i0))))
	
	(when (not (KNill i7)) (not (KNill i0)))
	
	(when (KGivenill i7 tag0 V_TRUE) (KGivenill i0 tag0 V_TRUE))
	
	(when (not (KGivenill i7 tag0 V_FALSE)) (not (KGivenill i0 tag0 V_FALSE)))
	
	(when (KGivenill i7 tag1 V_TRUE) (KGivenill i0 tag1 V_TRUE))
	
	(when (not (KGivenill i7 tag1 V_FALSE)) (not (KGivenill i0 tag1 V_FALSE))))
)
(:action medicate8
:precondition 
(and (ill i8) (Kill i8))
:effect 
(and 
	
	(when (ill i8) (ill i0))
	
	(when (Kill i8) 
		(and (Kill i0) (not (KNill i0))))
	
	(when (not (KNill i8)) (not (KNill i0)))
	
	(when (KGivenill i8 tag0 V_TRUE) (KGivenill i0 tag0 V_TRUE))
	
	(when (not (KGivenill i8 tag0 V_FALSE)) (not (KGivenill i0 tag0 V_FALSE)))
	
	(when (KGivenill i8 tag1 V_TRUE) (KGivenill i0 tag1 V_TRUE))
	
	(when (not (KGivenill i8 tag1 V_FALSE)) (not (KGivenill i0 tag1 V_FALSE))))
)
(:action medicate9
:precondition 
(and (ill i9) (Kill i9))
:effect 
(and 
	
	(when (ill i9) (ill i0))
	
	(when (Kill i9) 
		(and (Kill i0) (not (KNill i0))))
	
	(when (not (KNill i9)) (not (KNill i0)))
	
	(when (KGivenill i9 tag0 V_TRUE) (KGivenill i0 tag0 V_TRUE))
	
	(when (not (KGivenill i9 tag0 V_FALSE)) (not (KGivenill i0 tag0 V_FALSE)))
	
	(when (KGivenill i9 tag1 V_TRUE) (KGivenill i0 tag1 V_TRUE))
	
	(when (not (KGivenill i9 tag1 V_FALSE)) (not (KGivenill i0 tag1 V_FALSE))))
)
(:action medicate10
:precondition 
(and (ill i10) (Kill i10))
:effect 
(and 
	
	(when (ill i10) (ill i0))
	
	(when (Kill i10) 
		(and (Kill i0) (not (KNill i0))))
	
	(when (not (KNill i10)) (not (KNill i0)))
	
	(when (KGivenill i10 tag0 V_TRUE) (KGivenill i0 tag0 V_TRUE))
	
	(when (not (KGivenill i10 tag0 V_FALSE)) (not (KGivenill i0 tag0 V_FALSE)))
	
	(when (KGivenill i10 tag1 V_TRUE) (KGivenill i0 tag1 V_TRUE))
	
	(when (not (KGivenill i10 tag1 V_FALSE)) (not (KGivenill i0 tag1 V_FALSE))))
)
(:action stain
:effect 
(and (stained ) 
	
	(when (ill i1) (stain s1))
	
	(when (Kill i1) 
		(and (Kstain s1) (not (KNstain s1))))
	
	(when (not (KNill i1)) (not (KNstain s1)))
	
	(when (KGivenill i1 tag0 V_TRUE) (KGivenstain s1 tag0 V_TRUE))
	
	(when (not (KGivenill i1 tag0 V_FALSE)) (not (KGivenstain s1 tag0 V_FALSE)))
	
	(when (KGivenill i1 tag1 V_TRUE) (KGivenstain s1 tag1 V_TRUE))
	
	(when (not (KGivenill i1 tag1 V_FALSE)) (not (KGivenstain s1 tag1 V_FALSE)))
	
	(when (ill i2) (stain s2))
	
	(when (Kill i2) 
		(and (Kstain s2) (not (KNstain s2))))
	
	(when (not (KNill i2)) (not (KNstain s2)))
	
	(when (KGivenill i2 tag0 V_TRUE) (KGivenstain s2 tag0 V_TRUE))
	
	(when (not (KGivenill i2 tag0 V_FALSE)) (not (KGivenstain s2 tag0 V_FALSE)))
	
	(when (KGivenill i2 tag1 V_TRUE) (KGivenstain s2 tag1 V_TRUE))
	
	(when (not (KGivenill i2 tag1 V_FALSE)) (not (KGivenstain s2 tag1 V_FALSE)))
	
	(when (ill i3) (stain s3))
	
	(when (Kill i3) 
		(and (Kstain s3) (not (KNstain s3))))
	
	(when (not (KNill i3)) (not (KNstain s3)))
	
	(when (KGivenill i3 tag0 V_TRUE) (KGivenstain s3 tag0 V_TRUE))
	
	(when (not (KGivenill i3 tag0 V_FALSE)) (not (KGivenstain s3 tag0 V_FALSE)))
	
	(when (KGivenill i3 tag1 V_TRUE) (KGivenstain s3 tag1 V_TRUE))
	
	(when (not (KGivenill i3 tag1 V_FALSE)) (not (KGivenstain s3 tag1 V_FALSE)))
	
	(when (ill i4) (stain s4))
	
	(when (Kill i4) 
		(and (Kstain s4) (not (KNstain s4))))
	
	(when (not (KNill i4)) (not (KNstain s4)))
	
	(when (KGivenill i4 tag0 V_TRUE) (KGivenstain s4 tag0 V_TRUE))
	
	(when (not (KGivenill i4 tag0 V_FALSE)) (not (KGivenstain s4 tag0 V_FALSE)))
	
	(when (KGivenill i4 tag1 V_TRUE) (KGivenstain s4 tag1 V_TRUE))
	
	(when (not (KGivenill i4 tag1 V_FALSE)) (not (KGivenstain s4 tag1 V_FALSE)))
	
	(when (ill i5) (stain s5))
	
	(when (Kill i5) 
		(and (Kstain s5) (not (KNstain s5))))
	
	(when (not (KNill i5)) (not (KNstain s5)))
	
	(when (KGivenill i5 tag0 V_TRUE) (KGivenstain s5 tag0 V_TRUE))
	
	(when (not (KGivenill i5 tag0 V_FALSE)) (not (KGivenstain s5 tag0 V_FALSE)))
	
	(when (KGivenill i5 tag1 V_TRUE) (KGivenstain s5 tag1 V_TRUE))
	
	(when (not (KGivenill i5 tag1 V_FALSE)) (not (KGivenstain s5 tag1 V_FALSE)))
	
	(when (ill i6) (stain s6))
	
	(when (Kill i6) 
		(and (Kstain s6) (not (KNstain s6))))
	
	(when (not (KNill i6)) (not (KNstain s6)))
	
	(when (KGivenill i6 tag0 V_TRUE) (KGivenstain s6 tag0 V_TRUE))
	
	(when (not (KGivenill i6 tag0 V_FALSE)) (not (KGivenstain s6 tag0 V_FALSE)))
	
	(when (KGivenill i6 tag1 V_TRUE) (KGivenstain s6 tag1 V_TRUE))
	
	(when (not (KGivenill i6 tag1 V_FALSE)) (not (KGivenstain s6 tag1 V_FALSE)))
	
	(when (ill i7) (stain s7))
	
	(when (Kill i7) 
		(and (Kstain s7) (not (KNstain s7))))
	
	(when (not (KNill i7)) (not (KNstain s7)))
	
	(when (KGivenill i7 tag0 V_TRUE) (KGivenstain s7 tag0 V_TRUE))
	
	(when (not (KGivenill i7 tag0 V_FALSE)) (not (KGivenstain s7 tag0 V_FALSE)))
	
	(when (KGivenill i7 tag1 V_TRUE) (KGivenstain s7 tag1 V_TRUE))
	
	(when (not (KGivenill i7 tag1 V_FALSE)) (not (KGivenstain s7 tag1 V_FALSE)))
	
	(when (ill i8) (stain s8))
	
	(when (Kill i8) 
		(and (Kstain s8) (not (KNstain s8))))
	
	(when (not (KNill i8)) (not (KNstain s8)))
	
	(when (KGivenill i8 tag0 V_TRUE) (KGivenstain s8 tag0 V_TRUE))
	
	(when (not (KGivenill i8 tag0 V_FALSE)) (not (KGivenstain s8 tag0 V_FALSE)))
	
	(when (KGivenill i8 tag1 V_TRUE) (KGivenstain s8 tag1 V_TRUE))
	
	(when (not (KGivenill i8 tag1 V_FALSE)) (not (KGivenstain s8 tag1 V_FALSE)))
	
	(when (ill i9) (stain s9))
	
	(when (Kill i9) 
		(and (Kstain s9) (not (KNstain s9))))
	
	(when (not (KNill i9)) (not (KNstain s9)))
	
	(when (KGivenill i9 tag0 V_TRUE) (KGivenstain s9 tag0 V_TRUE))
	
	(when (not (KGivenill i9 tag0 V_FALSE)) (not (KGivenstain s9 tag0 V_FALSE)))
	
	(when (KGivenill i9 tag1 V_TRUE) (KGivenstain s9 tag1 V_TRUE))
	
	(when (not (KGivenill i9 tag1 V_FALSE)) (not (KGivenstain s9 tag1 V_FALSE)))
	
	(when (ill i10) (stain s10))
	
	(when (Kill i10) 
		(and (Kstain s10) (not (KNstain s10))))
	
	(when (not (KNill i10)) (not (KNstain s10)))
	
	(when (KGivenill i10 tag0 V_TRUE) (KGivenstain s10 tag0 V_TRUE))
	
	(when (not (KGivenill i10 tag0 V_FALSE)) (not (KGivenstain s10 tag0 V_FALSE)))
	
	(when (KGivenill i10 tag1 V_TRUE) (KGivenstain s10 tag1 V_TRUE))
	
	(when (not (KGivenill i10 tag1 V_FALSE)) (not (KGivenstain s10 tag1 V_FALSE))))
)
(:action Merge-stain-T
:parameters ( ?i - stain)
:precondition 
(and (not (Kstain ?i)) (not (KNstain ?i)) 
	(or (KGivenstain ?i tag0 V_TRUE) (KNot tag0))
	(or (KGivenstain ?i tag1 V_TRUE) (KNot tag1))(observed ))
:effect 
(and (Kstain ?i))
)

(:action Merge-stain-F
:parameters ( ?i - stain)
:precondition 
(and (not (Kstain ?i)) (not (KNstain ?i)) 
	(or (KGivenstain ?i tag0 V_FALSE) (KNot tag0))
	(or (KGivenstain ?i tag1 V_FALSE) (KNot tag1))(observed ))
:effect 
(and (KNstain ?i))
)

(:action RefuteT-stain
:parameters ( ?i - stain ?TAG_PARAM - TAG_TYPE)
:precondition 
(and (not (KNot ?TAG_PARAM)) (KGivenstain ?i ?TAG_PARAM V_TRUE) (KNstain ?i) (not (stain ?i)) (observed ))
:effect 
(and (KNot ?TAG_PARAM))
)

(:action RefuteF-stain
:parameters ( ?i - stain ?TAG_PARAM - TAG_TYPE)
:precondition 
(and (not (KNot ?TAG_PARAM)) (KGivenstain ?i ?TAG_PARAM V_FALSE) (Kstain ?i) (stain ?i) (observed ))
:effect 
(and (KNot ?TAG_PARAM))
)

(:action Merge-ill-T
:parameters ( ?i - illness)
:precondition 
(and (not (Kill ?i)) (not (KNill ?i)) 
	(or (KGivenill ?i tag0 V_TRUE) (KNot tag0))
	(or (KGivenill ?i tag1 V_TRUE) (KNot tag1))(observed ))
:effect 
(and (Kill ?i))
)

(:action Merge-ill-F
:parameters ( ?i - illness)
:precondition 
(and (not (Kill ?i)) (not (KNill ?i)) 
	(or (KGivenill ?i tag0 V_FALSE) (KNot tag0))
	(or (KGivenill ?i tag1 V_FALSE) (KNot tag1))(observed ))
:effect 
(and (KNill ?i))
)

(:action RefuteT-ill
:parameters ( ?i - illness ?TAG_PARAM - TAG_TYPE)
:precondition 
(and (not (KNot ?TAG_PARAM)) (KGivenill ?i ?TAG_PARAM V_TRUE) (KNill ?i) (not (ill ?i)) (observed ))
:effect 
(and (KNot ?TAG_PARAM))
)

(:action RefuteF-ill
:parameters ( ?i - illness ?TAG_PARAM - TAG_TYPE)
:precondition 
(and (not (KNot ?TAG_PARAM)) (KGivenill ?i ?TAG_PARAM V_FALSE) (Kill ?i) (ill ?i) (observed ))
:effect 
(and (KNot ?TAG_PARAM))
)

)
 