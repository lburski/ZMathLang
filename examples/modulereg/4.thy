theory gpsazml_modulereg
imports 
Main 

begin 

record SS1 = 
(*DECLARATIONS*)

locale zml_modulereg = 
fixes (*GLOBAL DECLARATIONS*) 
assumes SI1
begin

definition CS2 :: 
"(*CS2_TYPES*) => bool"
where 
"CS2 (*CS2_VARIABLES*) ==
 (PRE2)
\<and> (PO2)"

definition CS1 :: 
"(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) ==
 (PRE1)
\<and> (PO1)"

end
end