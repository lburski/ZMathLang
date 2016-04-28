\begin{verbatim}
theory gpsazml_projectalloc
imports 
Main 
begin 

record SS1 = 
(*DECLARATIONS*)

locale zml_projectalloc = 
fixes (*GLOBAL DECLARATIONS*) 
begin

definition IS1 :: 
 "(*IS1_TYPES*) => bool"
where 
"IS1 (*IS1_VARIABLES*) == (PO1)"

definition OS1 :: 
 "(*OS1_TYPES*) => bool"
where 
"OS1 (*OS1_VARIABLES*) == (O1)"

definition OS9 :: 
 "(*OS9_TYPES*) => bool"
where 
"OS9 (*OS9_VARIABLES*) == (PRE10)
\<and> (O9)"

definition OS8 :: 
 "(*OS8_TYPES*) => bool"
where 
"OS8 (*OS8_VARIABLES*) == (PRE9)
\<and> (O8)"

definition OS5 :: 
 "(*OS5_TYPES*) => bool"
where 
"OS5 (*OS5_VARIABLES*) == (PRE7)
\<and> (O5)"

definition OS3 :: 
 "(*OS3_TYPES*) => bool"
where 
"OS3 (*OS3_VARIABLES*) == (PRE5)
\<and> (O3)"

definition OS4 :: 
 "(*OS4_TYPES*) => bool"
where 
"OS4 (*OS4_VARIABLES*) == (PRE6)
\<and> (O4)"

definition OS7 :: 
 "(*OS7_TYPES*) => bool"
where 
"OS7 (*OS7_VARIABLES*) == (O7)"

definition OS6 :: 
 "(*OS6_TYPES*) => bool"
where 
"OS6 (*OS6_VARIABLES*) == (PRE8)
\<and> (O6)"

definition OS11 :: 
 "(*OS11_TYPES*) => bool"
where 
"OS11 (*OS11_VARIABLES*) == (O11)"

definition OS10 :: 
 "(*OS10_TYPES*) => bool"
where 
"OS10 (*OS10_VARIABLES*) == (PRE11)
\<and> (O10)"

definition CS1 :: 
"(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) ==
 (PRE1)
\<and> (PO2)"

definition CS4 :: 
 "(*CS4_TYPES*) => bool"
where 
"CS4 (*CS4_VARIABLES*) == (PO5)"

definition CS3 :: 
"(*CS3_TYPES*) => bool"
where 
"CS3 (*CS3_VARIABLES*) ==
 (PRE3)
\<and> (PO4)"

definition CS5 :: 
"(*CS5_TYPES*) => bool"
where 
"CS5 (*CS5_VARIABLES*) ==
 (PRE4)
\<and> (PO6)"

definition CS2 :: 
"(*CS2_TYPES*) => bool"
where 
"CS2 (*CS2_VARIABLES*) ==
 (PRE2)
\<and> (PO3)"

end
end
\end{verbatim}