theory gpsazmathlang_stInvIncorrect
imports 
Main 

begin 
(*DATATYPES*)

record SS1 = 
(*DECLARATIONS*)

locale zmathlang_stInvIncorrect = 
fixes (*GLOBAL DECLARATIONS*) 
assumes SI1
begin

definition OS1 :: 
 "(*OS1_TYPES*) => bool"
where 
"OS1 (*OS1_VARIABLES*) == (O1)"

definition IS1 :: 
 "(*IS1_TYPES*) => bool"
where 
"IS1 (*IS1_VARIABLES*) == (PO1)"

definition OS3 :: 
 "(*OS3_TYPES*) => bool"
where 
"OS3 (*OS3_VARIABLES*) == (PRE5)
\<and> (O3)"

definition OS2 :: 
 "(*OS2_TYPES*) => bool"
where 
"OS2 (*OS2_VARIABLES*) == (PRE4)
\<and> (O2)"

definition OS5 :: 
 "(*OS5_TYPES*) => bool"
where 
"OS5 (*OS5_VARIABLES*) == (PRE8)
\<and> (O5)"

definition OS4 :: 
 "(*OS4_TYPES*) => bool"
where 
"OS4 (*OS4_VARIABLES*) == (PRE7)
\<and> (O4)"

definition CS1 :: 
"(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) ==
 (PRE1)
\<and> (PO2)"

lemma TS1: 
"(*TS1_EXPRESSION*)"
sorry

definition CS4 :: 
"(*CS4_TYPES*) => bool"
where 
"CS4 (*CS4_VARIABLES*) ==
 (PRE6)
\<and> (PO5)"

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

lemma TS4: 
"(*TS4_EXPRESSION*)"
sorry

lemma TS2: 
"(*TS2_EXPRESSION*)"
sorry

lemma TS3: 
"(*TS3_EXPRESSION*)"
sorry

lemma TS5: 
"(*TS5_EXPRESSION*)"
sorry

lemma OS1_L6:
"(\<exists> (*OS1_VARIABLESANDTYPES*).
(O1)
\<and> (SI1))"
sorry

lemma OS3_L7:
"(\<exists> (*OS3_VARIABLESANDTYPES*).
(PRE5)
\<and> (O3)
\<and> (SI1))"
sorry

lemma OS2_L8:
"(\<exists> (*OS2_VARIABLESANDTYPES*).
(PRE4)
\<and> (O2)
\<and> (SI1))"
sorry

lemma OS5_L9:
"(\<exists> (*OS5_VARIABLESANDTYPES*).
(PRE8)
\<and> (O5)
\<and> (SI1))"
sorry

lemma OS4_L10:
"(\<exists> (*OS4_VARIABLESANDTYPES*).
(PRE7)
\<and> (O4)
\<and> (SI1))"
sorry

lemma CS1_L11:
"(\<exists> (*CS1_VARIABLESANDTYPES*).
(PRE1)
\<and> (PO2)
\<and> (SI1))"
sorry

lemma CS4_L12:
"(\<exists> (*CS4_VARIABLESANDTYPES*).
(PRE6)
\<and> (PO5)
\<and> (SI1))"
sorry

lemma CS3_L13:
"(\<exists> (*CS3_VARIABLESANDTYPES*).
(PRE3)
\<and> (PO4)
\<and> (SI1))"
sorry

lemma CS2_L14:
"(\<exists> (*CS2_VARIABLESANDTYPES*).
(PRE2)
\<and> (PO3)
\<and> (SI1))"
sorry

end
end
