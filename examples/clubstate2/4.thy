theory gpsazml_clubstate2
imports 
Main 
begin 

record SS1 = 
(*DECLARATIONS*)

locale zml_clubstate2 = 
fixes (*GLOBAL DECLARATIONS*) 
assumes SI1
begin

record SS2 = 
(*DECLARATIONS*)

locale zml_clubstate2 = 
fixes (*GLOBAL DECLARATIONS*) 
assumes SI2
begin

definition IS1 :: 
 "(*IS1_TYPES*) => bool"
where 
"IS1 (*IS1_VARIABLES*) == (PO1)"

definition CS1 :: 
"(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) ==
 (PRE1)
\<and> (PO2)"

definition CS3 :: 
"(*CS3_TYPES*) => bool"
where 
"CS3 (*CS3_VARIABLES*) ==
 (PRE3)
\<and> (PO4)"

definition CS2 :: 
"(*CS2_TYPES*) => bool"
where 
"CS2 (*CS2_VARIABLES*) ==
 (PRE2)
\<and> (PO3)"

end
end