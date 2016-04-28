theory gpsazml_timetable
imports 
Main 

begin 

primrec A1:: "(*A1_TYPES*)"
where
"(*A1_EXPRESSION*)"

record SS1 = 
(*DECLARATIONS*)

locale zml_timetable = 
fixes (*GLOBAL DECLARATIONS*) 
assumes SI1
begin

definition IS1 :: 
 "(*IS1_TYPES*) => bool"
where 
"IS1 (*IS1_VARIABLES*) == (PO1)"

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