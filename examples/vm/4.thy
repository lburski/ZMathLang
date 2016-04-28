theory isaSkeleton_vendingmachine
imports 
Main 
begin 

record SS1 = 
(*DECLARATIONS*)

locale zmathlang_vm = 
fixes (*GLOBAL DECLARATIONS*) 
begin

definition PRE1 :: 
 "(*PRE1_TYPES*) => bool"
where 
"PRE1 (*PRE1_VARIABLES*) == (*PRECONDITION*) "

definition PRE2 :: 
 "(*PRE2_TYPES*) => bool"
where 
"PRE2 (*PRE2_VARIABLES*) == (*PRECONDITION*) "

definition CS0 :: 
"(*CS0_TYPES*) => bool"
where 
"CS0 (*CS0_VARIABLES*) == True"

definition PRE3 :: 
 "(*PRE3_TYPES*) => bool"
where 
"PRE3 (*PRE3_VARIABLES*) == (*PRECONDITION*) "

definition CS2 :: 
 "(*CS2_TYPES*) => bool"
where 
"CS2 (*CS2_VARIABLES*) == (PO2)"

lemma TS2: 
"(*TS2_EXPRESSION*)"
sorry

definition CS1 :: 
 "(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) == (PO1)"

lemma TS1: 
"(*TS1_EXPRESSION*)"
sorry

lemma TS3: 
"(*TS3_EXPRESSION*)"
sorry

end
end