theory gpsa1n2
imports 
Main 

begin 
(*DATATYPES*)

record SS1 = 
(*DECLARATIONS*)

locale 1n2 = 
fixes (*GLOBAL DECLARATIONS*) 
begin

definition OS1 :: 
 "(*OS1_TYPES*) => bool"
where 
"OS1 (*OS1_VARIABLES*) == (O1)"

definition CS1 :: 
"(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) ==
 (PRE1)
\<and> (PO1)"

end
end
