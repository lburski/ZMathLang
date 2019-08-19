theory new4
imports 
Main 

begin 
(*DATATYPES*)

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

definition CS7 :: 
"(*CS7_TYPES*) => bool"
where 
"CS7 (*CS7_VARIABLES*) ==
 (PRE8)
\<and> (PO9)"

definition CS2 :: 
"(*CS2_TYPES*) => bool"
where 
"CS2 (*CS2_VARIABLES*) ==
 (PRE2)
\<and> (PO3)"

definition OS1 :: 
 "(*OS1_TYPES*) => bool"
where 
"OS1 (*OS1_VARIABLES*) == (O1)"

definition OS3 :: 
 "(*OS3_TYPES*) => bool"
where 
"OS3 (*OS3_VARIABLES*) == (PRE6)"

definition OS2 :: 
 "(*OS2_TYPES*) => bool"
where 
"OS2 (*OS2_VARIABLES*) == (O2)"

definition CS5 :: 
"(*CS5_TYPES*) => bool"
where 
"CS5 (*CS5_VARIABLES*) ==
 (PRE5)
\<and> (PO6)"

definition CS4 :: 
"(*CS4_TYPES*) => bool"
where 
"CS4 (*CS4_VARIABLES*) == 
 (PRE4)
\<and> (PO5)"

definition CS6 :: 
"(*CS6_TYPES*) => bool"
where 
"CS6 (*CS6_VARIABLES*) ==
 (PRE7)
\<and> (PO8)"

definition CS3 :: 
"(*CS3_TYPES*) => bool"
where 
"CS3 (*CS3_VARIABLES*) ==
 (PRE3)
\<and> (PO4)"

definition TS2 :: 
"(*TS2_TYPES*) => bool"
where 
"TS2 (*TS2_VARIABLES*) == (*TS2_EXPRESSION*)"

definition TS1 :: 
"(*TS1_TYPES*) => bool"
where 
"TS1 (*TS1_VARIABLES*) == (*TS1_EXPRESSION*)"

definition TS3 :: 
"(*TS3_TYPES*) => bool"
where 
"TS3 (*TS3_VARIABLES*) == (*TS3_EXPRESSION*)"

end

record SS2 = SS1 +

definition IS2 :: 
 "(*IS2_TYPES*) => bool"
where 
"IS2 (*IS2_VARIABLES*) == (PO10)"

definition OS5 :: 
 "(*OS5_TYPES*) => bool"
where 
"OS5 (*OS5_VARIABLES*) == (O4)"

definition OS4 :: 
 "(*OS4_TYPES*) => bool"
where 
"OS4 (*OS4_VARIABLES*) == (O3)"

definition CS9 :: 
"(*CS9_TYPES*) => bool"
where 
"CS9 (*CS9_VARIABLES*) ==
 (PRE10)
\<and> (PO12)"

definition CS8 :: 
"(*CS8_TYPES*) => bool"
where 
"CS8 (*CS8_VARIABLES*) ==
 (PRE9)
\<and> (PO11)"

definition CS11 :: 
"(*CS11_TYPES*) => bool"
where 
"CS11 (*CS11_VARIABLES*) ==
 (PRE12)
\<and> (PO14)"

definition CS13 :: 
"(*CS13_TYPES*) => bool"
where 
"CS13 (*CS13_VARIABLES*) ==
 (PRE14)
\<and> (PO16)"

definition CS15 :: 
"(*CS15_TYPES*) => bool"
where 
"CS15 (*CS15_VARIABLES*) ==
 (PRE16)
\<and> (PO18)"

definition CS14 :: 
"(*CS14_TYPES*) => bool"
where 
"CS14 (*CS14_VARIABLES*) ==
 (PRE15)
\<and> (PO17)"

definition OS6 :: 
 "(*OS6_TYPES*) => bool"
where 
"OS6 (*OS6_VARIABLES*) == (O5)"

definition CS20 :: 
"(*CS20_TYPES*) => bool"
where 
"CS20 (*CS20_VARIABLES*) ==
 (PRE21)
\<and> (PO23)"

definition CS21 :: 
"(*CS21_TYPES*) => bool"
where 
"CS21 (*CS21_VARIABLES*) ==
 (PRE22)
\<and> (PO24)"

definition CS19 :: 
"(*CS19_TYPES*) => bool"
where 
"CS19 (*CS19_VARIABLES*) ==
 (PRE20)
\<and> (PO22)"

definition CS18 :: 
"(*CS18_TYPES*) => bool"
where 
"CS18 (*CS18_VARIABLES*) ==
 (PRE19)
\<and> (PO21)"

definition CS10 :: 
"(*CS10_TYPES*) => bool"
where 
"CS10 (*CS10_VARIABLES*) ==
 (PRE11)
\<and> (PO13)"

definition CS12 :: 
"(*CS12_TYPES*) => bool"
where 
"CS12 (*CS12_VARIABLES*) ==
 (PRE13)
\<and> (PO15)"

definition CS17 :: 
"(*CS17_TYPES*) => bool"
where 
"CS17 (*CS17_VARIABLES*) ==
 (PRE18)
\<and> (PO20)"

definition CS16 :: 
"(*CS16_TYPES*) => bool"
where 
"CS16 (*CS16_VARIABLES*) ==
 (PRE17)
\<and> (PO19)"

definition TS6 :: 
"(*TS6_TYPES*) => bool"
where 
"TS6 (*TS6_VARIABLES*) == (*TS6_EXPRESSION*)"

definition TS4 :: 
"(*TS4_TYPES*) => bool"
where 
"TS4 (*TS4_VARIABLES*) == (*TS4_EXPRESSION*)"

definition TS5 :: 
"(*TS5_TYPES*) => bool"
where 
"TS5 (*TS5_VARIABLES*) == (*TS5_EXPRESSION*)"

lemma CS7_L1:
"(\<exists> (*CS7_VARIABLESANDTYPES*).
(PRE8)
\<and> (PO9)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS2_L2:
"(\<exists> (*CS2_VARIABLESANDTYPES*).
(PRE8)
\<and> (PO9)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS5_L3:
"(\<exists> (*CS5_VARIABLESANDTYPES*).
(PRE5)
\<and> (PO6)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS4_L4:
"(\<exists> (*CS4_VARIABLESANDTYPES*).
(PRE4)
\<and> (PO5)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS6_L5:
"(\<exists> (*CS6_VARIABLESANDTYPES*).
(PRE7)
\<and> (PO8)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS1_L6:
"(\<exists> (*CS1_VARIABLESANDTYPES*).
(PRE1)
\<and> (PO2)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS3_L7:
"(\<exists> (*CS3_VARIABLESANDTYPES*).
(PRE3)
\<and> (PO4)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS9_L8:
"(\<exists> (*CS9_VARIABLESANDTYPES*).
(PRE10)
\<and> (PO12)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS8_L9:
"(\<exists> (*CS8_VARIABLESANDTYPES*).
(PRE9)
\<and> (PO11)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS11_L10:
"(\<exists> (*CS11_VARIABLESANDTYPES*).
(PRE12)
\<and> (PO14)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS13_L11:
"(\<exists> (*CS13_VARIABLESANDTYPES*).
(PRE14)
\<and> (PO16)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS15_L12:
"(\<exists> (*CS15_VARIABLESANDTYPES*).
(PRE16)
\<and> (PO18)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS14_L13:
"(\<exists> (*CS14_VARIABLESANDTYPES*).
(PRE15)
\<and> (PO17)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS20_L14:
"(\<exists> (*CS20_VARIABLESANDTYPES*).
(PRE21)
\<and> (PO23)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS21_L15:
"(\<exists> (*CS21_VARIABLESANDTYPES*).
(PRE22)
\<and> (PO24)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS19_L16:
"(\<exists> (*CS19_VARIABLESANDTYPES*).
(PRE20)
\<and> (PO22)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS18_L17:
"(\<exists> (*CS18_VARIABLESANDTYPES*).
(PRE19)
\<and> (PO21)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS10_L18:
"(\<exists> (*CS10_VARIABLESANDTYPES*).
(PRE11)
\<and> (PO13)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS12_L19:
"(\<exists> (*CS12_VARIABLESANDTYPES*).
(PRE13)
\<and> (PO25)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS17_L20:
"(\<exists> (*CS17_VARIABLESANDTYPES*).
(PRE18)
\<and> (PO20)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

lemma CS16_L21:
"(\<exists> (*CS16_VARIABLESANDTYPES*).
(PRE17)
\<and> (PO19)
\<longrightarrow> ((SI1)
\<and> (SI1')))"
sorry

end
