theory gpsazml_clubstate
imports 
Main 

begin 

record SS3 = 
(*DECLARATIONS*)

locale zml_clubstate = 
fixes (*GLOBAL DECLARATIONS*) 
assumes SI3
begin

definition OS3 :: 
 "(*OS3_TYPES*) => bool"
where 
"OS3 (*OS3_VARIABLES*) == (O3)"

record SS1 = 
(*DECLARATIONS*)

locale zml_clubstate = 
fixes (*GLOBAL DECLARATIONS*) 
assumes SI1
begin

record SS2 = 
(*DECLARATIONS*)

locale zml_clubstate = 
fixes (*GLOBAL DECLARATIONS*) 
assumes SI2
begin

definition PRE8 :: 
 "(*PRE8_TYPES*) => bool"
where 
"PRE8 (*PRE8_VARIABLES*) == (*PRECONDITION*) "

definition CS5 :: 
"(*CS5_TYPES*) => bool"
where 
"CS5 (*CS5_VARIABLES*) ==
 (PRE5)
\<and> (PO5)"

definition CS4 :: 
"(*CS4_TYPES*) => bool"
where 
"CS4 (*CS4_VARIABLES*) ==
 (PRE4)
\<and> (PO4)"

definition CS7 :: 
 "(*CS7_TYPES*) => bool"
where 
"CS7 (*CS7_VARIABLES*) == (PO8)"

definition CS6 :: 
"(*CS6_TYPES*) => bool"
where 
"CS6 (*CS6_VARIABLES*) ==
 (PRE7)
\<and> (PO7)"

definition CS1 :: 
"(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) ==
 (PRE1)
\<and> (PO1)"

definition CS3 :: 
"(*CS3_TYPES*) => bool"
where 
"CS3 (*CS3_VARIABLES*) ==
 (PRE3)
\<and> (PO3)"

definition CS2 :: 
"(*CS2_TYPES*) => bool"
where 
"CS2 (*CS2_VARIABLES*) ==
 (PRE2)
\<and> (PO2)"

definition OS2 :: 
 "(*OS2_TYPES*) => bool"
where 
"OS2 (*OS2_VARIABLES*) == (PRE6)
\<and> (O2)"

definition OS1 :: 
 "(*OS1_TYPES*) => bool"
where 
"OS1 (*OS1_VARIABLES*) == (O1)"

definition OS4 :: 
 "(*OS4_TYPES*) => bool"
where 
"OS4 (*OS4_VARIABLES*) == (PRE9)
\<and> (O4)"

definition IS1 :: 
 "(*IS1_TYPES*) => bool"
where 
"IS1 (*IS1_VARIABLES*) == (PO6)"

definition PRE11 :: 
 "(*PRE11_TYPES*) => bool"
where 
"PRE11 (*PRE11_VARIABLES*) == (*PRECONDITION*) "

definition PRE10 :: 
 "(*PRE10_TYPES*) => bool"
where 
"PRE10 (*PRE10_VARIABLES*) == (*PRECONDITION*) "

end
end