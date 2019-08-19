theory gpsa1n2
imports 
Main 

begin 

record SS1 = 
(*DECLARATIONS*)

locale 1n2 = 
fixes (*GLOBAL DECLARATIONS*) 
begin

definition IS1 :: 
 "(*IS1_TYPES*) => bool"
where 
"IS1 (*IS1_VARIABLES*) == (PO1)"

definition IS6 :: 
 "(*IS6_TYPES*) => bool"
where 
"IS6 (*IS6_VARIABLES*) == (PO10)"

definition PRE4 :: 
 "(*PRE4_TYPES*) => bool"
where 
"PRE4 (*PRE4_VARIABLES*) == (*PRECONDITION*) "

definition CS8 :: 
"(*CS8_TYPES*) => bool"
where 
"CS8 (*CS8_VARIABLES*) ==
 (PRE17)
\<and> (PO19)"

definition CS5 :: 
"(*CS5_TYPES*) => bool"
where 
"CS5 (*CS5_VARIABLES*) ==
 (PRE14)
\<and> (PO16)"

definition CS7 :: 
"(*CS7_TYPES*) => bool"
where 
"CS7 (*CS7_VARIABLES*) ==
 (PRE16)
\<and> (PO18)"

definition CS3 :: 
"(*CS3_TYPES*) => bool"
where 
"CS3 (*CS3_VARIABLES*) ==
 (PRE8)
\<and> (PO9)"

definition CS12 :: 
"(*CS12_TYPES*) => bool"
where 
"CS12 (*CS12_VARIABLES*) ==
 (PRE21)
\<and> (PO23)"

definition OS1 :: 
 "(*OS1_TYPES*) => bool"
where 
"OS1 (*OS1_VARIABLES*) == (O1)"

definition OS3 :: 
 "(*OS3_TYPES*) => bool"
where 
"OS3 (*OS3_VARIABLES*) == (PRE6)"

definition OS2 :: 
 "(*OS2_TYPES*) => bool"
where 
"OS2 (*OS2_VARIABLES*) == (O2)"

definition OS5 :: 
 "(*OS5_TYPES*) => bool"
where 
"OS5 (*OS5_VARIABLES*) == (O2)"

definition OS4 :: 
 "(*OS4_TYPES*) => bool"
where 
"OS4 (*OS4_VARIABLES*) == (O1)"

definition OS6 :: 
 "(*OS6_TYPES*) => bool"
where 
"OS6 (*OS6_VARIABLES*) == (O3)"

definition IS9 :: 
"(*IS9_TYPES*) => bool"
where 
"IS9 (*IS9_VARIABLES*) == True"

definition PRE11 :: 
 "(*PRE11_TYPES*) => bool"
where 
"PRE11 (*PRE11_VARIABLES*) == (*PRECONDITION*) "

definition IS8 :: 
"(*IS8_TYPES*) => bool"
where 
"IS8 (*IS8_VARIABLES*) == True"

definition PRE10 :: 
 "(*PRE10_TYPES*) => bool"
where 
"PRE10 (*PRE10_VARIABLES*) == (*PRECONDITION*) "

definition IS3 :: 
"(*IS3_TYPES*) => bool"
where 
"IS3 (*IS3_VARIABLES*) == True"

definition PRE2 :: 
 "(*PRE2_TYPES*) => bool"
where 
"PRE2 (*PRE2_VARIABLES*) == (*PRECONDITION*) "

definition IS2 :: 
"(*IS2_TYPES*) => bool"
where 
"IS2 (*IS2_VARIABLES*) == True"

definition PRE1 :: 
 "(*PRE1_TYPES*) => bool"
where 
"PRE1 (*PRE1_VARIABLES*) == (*PRECONDITION*) "

definition IS7 :: 
"(*IS7_TYPES*) => bool"
where 
"IS7 (*IS7_VARIABLES*) == True"

definition PRE9 :: 
 "(*PRE9_TYPES*) => bool"
where 
"PRE9 (*PRE9_VARIABLES*) == (*PRECONDITION*) "

definition IS5 :: 
"(*IS5_TYPES*) => bool"
where 
"IS5 (*IS5_VARIABLES*) == True"

definition IS4 :: 
"(*IS4_TYPES*) => bool"
where 
"IS4 (*IS4_VARIABLES*) == True"

definition PRE3 :: 
 "(*PRE3_TYPES*) => bool"
where 
"PRE3 (*PRE3_VARIABLES*) == (*PRECONDITION*) "

definition CS10 :: 
"(*CS10_TYPES*) => bool"
where 
"CS10 (*CS10_VARIABLES*) ==
 (PRE19)
\<and> (PO21)"

definition PO4 :: 
"(*PO4_TYPES*) => bool"
where 
"PO4 (*PO4_VARIABLES*) == (*POSTCONDITION*) "

definition PO5 :: 
"(*PO5_TYPES*) => bool"
where 
"PO5 (*PO5_VARIABLES*) == (*POSTCONDITION*) "

definition PO2 :: 
"(*PO2_TYPES*) => bool"
where 
"PO2 (*PO2_VARIABLES*) == (*POSTCONDITION*) "

definition PO3 :: 
"(*PO3_TYPES*) => bool"
where 
"PO3 (*PO3_VARIABLES*) == (*POSTCONDITION*) "

definition CS9 :: 
"(*CS9_TYPES*) => bool"
where 
"CS9 (*CS9_VARIABLES*) ==
 (PRE18)
\<and> (PO20)"

definition CS4 :: 
"(*CS4_TYPES*) => bool"
where 
"CS4 (*CS4_VARIABLES*) ==
 (PRE13)
\<and> (PO15)"

definition CS6 :: 
"(*CS6_TYPES*) => bool"
where 
"CS6 (*CS6_VARIABLES*) ==
 (PRE15)
\<and> (PO17)"

definition CS1 :: 
"(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) ==
 (PRE5)
\<and> (PO6)"

definition CS2 :: 
"(*CS2_TYPES*) => bool"
where 
"CS2 (*CS2_VARIABLES*) ==
 (PRE7)
\<and> (PO8)"

definition CS11 :: 
"(*CS11_TYPES*) => bool"
where 
"CS11 (*CS11_VARIABLES*) ==
 (PRE20)
\<and> (PO22)"

definition CS13 :: 
"(*CS13_TYPES*) => bool"
where 
"CS13 (*CS13_VARIABLES*) ==
 (PRE22)
\<and> (PO24)"

definition IS10 :: 
"(*IS10_TYPES*) => bool"
where 
"IS10 (*IS10_VARIABLES*) == True"

definition PRE12 :: 
 "(*PRE12_TYPES*) => bool"
where 
"PRE12 (*PRE12_VARIABLES*) == (*PRECONDITION*) "

definition PO11 :: 
"(*PO11_TYPES*) => bool"
where 
"PO11 (*PO11_VARIABLES*) == (*POSTCONDITION*) "

definition PO12 :: 
"(*PO12_TYPES*) => bool"
where 
"PO12 (*PO12_VARIABLES*) == (*POSTCONDITION*) "

definition PO13 :: 
"(*PO13_TYPES*) => bool"
where 
"PO13 (*PO13_VARIABLES*) == (*POSTCONDITION*) "

definition PO14 :: 
"(*PO14_TYPES*) => bool"
where 
"PO14 (*PO14_VARIABLES*) == (*POSTCONDITION*) "

lemma TS5: 
"(*TS5_EXPRESSION*)"
sorry

lemma TS4: 
"(*TS4_EXPRESSION*)"
sorry

lemma TS1: 
"(*TS1_EXPRESSION*)"
sorry

lemma TS2: 
"(*TS2_EXPRESSION*)"
sorry

lemma TS3: 
"(*TS3_EXPRESSION*)"
sorry

lemma TS6: 
"(*TS6_EXPRESSION*)"
sorry

end
end