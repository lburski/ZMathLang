theory isakeleton_birthdaybook
imports 
Main 

begin 

record SS1 = 
(*DECLARATIONS*)

locale zmathlang_birthdaybook = 
fixes (*GLOBAL DECLARATIONS*) 
assumes SI1
begin

definition IS1 :: 
 "(*IS1_TYPES*) => bool"
where 
"IS1 (*IS1_VARIABLES*) == (PO2)"

definition OS1 :: 
 "(*OS1_TYPES*) => bool"
where 
"OS1 (*OS1_VARIABLES*) == (PRE2)
\<and> (O1)"

definition OS5 :: 
 "(*OS5_TYPES*) => bool"
where 
"OS5 (*OS5_VARIABLES*) == (PRE4)
\<and> (O5)"

definition OS4 :: 
 "(*OS4_TYPES*) => bool"
where 
"OS4 (*OS4_VARIABLES*) == (PRE3)
\<and> (O4)"

definition CS1 :: 
"(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) ==
 (PRE1)
\<and> (PO3)"

definition OS3 :: 
 "(*OS3_TYPES*) => bool"
where 
"OS3 (*OS3_VARIABLES*) == (O3)"

definition TS2 :: 
 "(*TS2_TYPES*) => bool"
where 
"TS2 (*TS2_VARIABLES*) == (*EXPRESSION*) "

definition TS1 :: 
 "(*TS1_TYPES*) => bool"
where 
"TS1 (*TS1_VARIABLES*) == (*EXPRESSION*) "

end
end
