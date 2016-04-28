theory gpsa1n2
imports 
Main 

begin 

record SS1 = 
(*DECLARATIONS*)

locale 1n2 = 
fixes (*GLOBAL DECLARATIONS*) 
assumes SI1
begin

definition IS1 :: 
 "(*IS1_TYPES*) => bool"
where 
"IS1 (*IS1_VARIABLES*) == (PO1)"

definition OS1 :: 
 "(*OS1_TYPES*) => bool"
where 
"OS1 (*OS1_VARIABLES*) == (PRE5)
\<and> (O1)"

definition OS2 :: 
 "(*OS2_TYPES*) => bool"
where 
"OS2 (*OS2_VARIABLES*) == (PRE6)
\<and> (O2)"

definition CS3 :: 
"(*CS3_TYPES*) => bool"
where 
"CS3 (*CS3_VARIABLES*) ==
 (PRE3)
\<and> (PO4)"

definition CS4 :: 
"(*CS4_TYPES*) => bool"
where 
"CS4 (*CS4_VARIABLES*) ==
 (PRE4)
\<and> (PO5)"

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

end
end