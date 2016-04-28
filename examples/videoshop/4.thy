theory gpsazml_videoshop
imports 
Main 

begin 

record SS1 = 
(*DECLARATIONS*)

locale zml_videoshop = 
fixes (*GLOBAL DECLARATIONS*) 
assumes SI1
begin

definition IS1 :: 
 "(*IS1_TYPES*) => bool"
where 
"IS1 (*IS1_VARIABLES*) == (PO1)

definition OS10 :: 
 "(*OS10_TYPES*) => bool"
where 
"OS10 (*OS10_VARIABLES*) == (PRE13)
\<and> (O10)"

definition OS9 :: 
 "(*OS9_TYPES*) => bool"
where 
"OS9 (*OS9_VARIABLES*) == (PRE12)
\<and> (O9)"

definition OS8 :: 
 "(*OS8_TYPES*) => bool"
where 
"OS8 (*OS8_VARIABLES*) == (PRE11)
\<and> (O8)"

definition OS1 :: 
 "(*OS1_TYPES*) => bool"
where 
"OS1 (*OS1_VARIABLES*) == (PRE4)
\<and> (O1)"

definition OS5 :: 
 "(*OS5_TYPES*) => bool"
where 
"OS5 (*OS5_VARIABLES*) == (PRE8)
\<and> (O5)"

definition OS3 :: 
 "(*OS3_TYPES*) => bool"
where 
"OS3 (*OS3_VARIABLES*) == (PRE6)
\<and> (O3)"

definition OS2 :: 
 "(*OS2_TYPES*) => bool"
where 
"OS2 (*OS2_VARIABLES*) == (PRE5)
\<and> (O2)"

definition OS4 :: 
 "(*OS4_TYPES*) => bool"
where 
"OS4 (*OS4_VARIABLES*) == (PRE7)
\<and> (O4)"

definition OS7 :: 
 "(*OS7_TYPES*) => bool"
where 
"OS7 (*OS7_VARIABLES*) == (PRE10)
\<and> (O7)"

definition OS6 :: 
 "(*OS6_TYPES*) => bool"
where 
"OS6 (*OS6_VARIABLES*) == (PRE9)
\<and> (O6)"
"

definition CS1 :: 
"(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) ==
 (PRE1)
\<and> (PO2)"

definition CS2 :: 
"(*CS2_TYPES*) => bool"
where 
"CS2 (*CS2_VARIABLES*) ==
 (PRE2)
\<and> (PO3)"

definition CS3 :: 
"(*CS3_TYPES*) => bool"
where 
"CS3 (*CS3_VARIABLES*) ==
 (PRE3)
\<and> (PO4)"

end
end
