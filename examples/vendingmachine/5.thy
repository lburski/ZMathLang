theory gpsa1n2
imports 
Main 

begin 

datatype State = init | norm | broken | stop
datatype OnOff = on |off
datatype OpenClosed = open | closed
datatype WorksBroken = works | broken


record SteamBoiler0 = 
W_{MIN} :: nat
W_{MAX} :: nat
L :: nat
D_{MAX} :: nat
\DELTA_{P} :: nat
\DELTA_{D} :: nat
W? :: nat
D? :: nat
P_{1}}, \TERM{P_{2}}, \TERM{P_{3}}, \TERM{P_{4} :: OnOff
V :: OpenClosed
A :: OnOff
Z :: State
PAMOUNT :: (OnOff times WorksBroken) fun nat
S :: nat
\DELTA :: nat

locale 1n2 = 
fixes w_{min} :: "nat"
and w_{max} :: "nat"
and l :: "nat"
and d_{max} :: "nat"
and \delta_{p} :: "nat"
and \delta_{d} :: "nat"
and w? :: "nat"
and d? :: "nat"
and p_{1}}, \term{p_{2}}, \term{p_{3}}, \term{p_{4} :: "OnOff"
and v :: "OpenClosed"
and a :: "OnOff"
and z :: "State"
and pamount :: "(OnOff times WorksBroken) fun nat"
and v :: "OpenClosed"
and a :: "OnOff"
and z :: "State"
and s :: "nat"
and \delta :: "nat"
begin

definition SteamBoilerInit0 :: 
 "OpenClosed => OpenClosed => OnOff => OnOff => State => State => bool"
where 
"SteamBoilerInit0 v' a' z' == ((
(a' = off) 
\<and> (z' = init)))"

definition SteamBoilerInit1 :: 
" bool"
where 
"SteamBoilerInit1  == ((
(a' = off) 
\<and> (z' = init))0)"

definition (
(z = init) 
\<and> (d = 0) 
\<and> (w > w_max)) :: 
 "(*(
(z = init) 
\<and> (d = 0) 
\<and> (w > w_max))_TYPES*) => bool"
where 
"(
(z = init) 
\<and> (d = 0) 
\<and> (w > w_max)) (*(
(z = init) 
\<and> (d = 0) 
\<and> (w > w_max))_VARIABLES*) == (*PRECONDITION*) "

definition SNormalControlStop1 :: 
"(*SNormalControlStop1_TYPES*) => bool"
where 
"SNormalControlStop1 (*SNormalControlStop1_VARIABLES*) ==
 ((
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))7)
\<and> ((
(a' = off) 
\<and> (z' = init))9)"

definition SNormalContinue1 :: 
"(*SNormalContinue1_TYPES*) => bool"
where 
"SNormalContinue1 (*SNormalContinue1_VARIABLES*) ==
 ((
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))4)
\<and> ((
(a' = off) 
\<and> (z' = init))6)"

definition SNormalWaterStop1 :: 
" bool"
where 
"SNormalWaterStop1  ==
 ((
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))6)
\<and> ((
(a' = off) 
\<and> (z' = init))8)"

definition SNormalStop0 :: 
"(*SNormalStop0_TYPES*) => bool"
where 
"SNormalStop0 (*SNormalStop0_VARIABLES*) ==
 ((
(z = norm) 
\<and> (w < w_min \<or>
 w > w_max)))
\<and> ((
(a' = off \<and>
 z' = stop)))"

definition SBrokenControlStop1 :: 
"(*SBrokenControlStop1_TYPES*) => bool"
where 
"SBrokenControlStop1 (*SBrokenControlStop1_VARIABLES*) ==
 ((
(z = init) 
\<and> (d > 0))1)
\<and> ((
(w \<le> w_max) 
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on))3)"

definition PumpsOff :: 
" bool"
where 
"PumpsOff  == ((
(p_1 = off \<and>
 p_2' = off \<and>
 p_3' = off \<and>
 p_4' = off)))"

definition SNormalContinue0 :: 
 "(*SNormalContinue0_TYPES*) => bool"
where 
"SNormalContinue0 (*SNormalContinue0_VARIABLES*) == ((
(z = norm) 
\<and> (w > w_opt - 3l) 
\<and> (w \<le> w_opt)))"

definition PumpsOn :: 
" bool"
where 
"PumpsOn  == ((
(p_1 = on \<and>
 p_2' = on \<and>
 p_3' = on \<and>
 p_4' = on)))"

definition PumpsControlledOff :: 
" bool"
where 
"PumpsControlledOff  == ((
(p_1 = on \<and>
 p_2' = on \<and>
 p_3' = on \<and>
 p_4' = on)))"

definition PumpsControlledOn :: 
" bool"
where 
"PumpsControlledOn  == ((
(p_1 = off \<and>
 p_2' = off \<and>
 p_3' = off \<and>
 p_4' = off)))"

definition AmountComputation :: 
 "nat => nat => nat => nat => bool"
where 
"AmountComputation  == ((
))"

definition SInitEmpty1 :: 
"(*SInitEmpty1_TYPES*) => bool"
where 
"SInitEmpty1 (*SInitEmpty1_VARIABLES*) == True"

definition (
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))1 :: 
 "(*(
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))1_TYPES*) => bool"
where 
"(
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))1 (*(
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))1_VARIABLES*) == (*PRECONDITION*) "

definition SInitFill1 :: 
"(*SInitFill1_TYPES*) => bool"
where 
"SInitFill1 (*SInitFill1_VARIABLES*) == True"

definition (
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))0 :: 
 "(*(
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))0_TYPES*) => bool"
where 
"(
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))0 (*(
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))0_VARIABLES*) == (*PRECONDITION*) "

definition SInitStop0 :: 
"(*SInitStop0_TYPES*) => bool"
where 
"SInitStop0 (*SInitStop0_VARIABLES*) == True"

definition (
(z = init) 
\<and> (d > 0)) :: 
 "(*(
(z = init) 
\<and> (d > 0))_TYPES*) => bool"
where 
"(
(z = init) 
\<and> (d > 0)) (*(
(z = init) 
\<and> (d > 0))_VARIABLES*) == (*PRECONDITION*) "

definition SInitNormal0 :: 
"(*SInitNormal0_TYPES*) => bool"
where 
"SInitNormal0 (*SInitNormal0_VARIABLES*) == True"

definition (
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max)) :: 
 "(*(
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))_TYPES*) => bool"
where 
"(
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max)) (*(
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))_VARIABLES*) == (*PRECONDITION*) "

definition SInitNormal1 :: 
"(*SInitNormal1_TYPES*) => bool"
where 
"SInitNormal1 (*SInitNormal1_VARIABLES*) == True"

definition (
(z = init) 
\<and> (d = 0) 
\<and> (k_w = works \<and>
 k_d = works) 
\<and> (w \<ge> w_min + d_max) 
\<and> (w \<le> w_max)) :: 
 "(*(
(z = init) 
\<and> (d = 0) 
\<and> (k_w = works \<and>
 k_d = works) 
\<and> (w \<ge> w_min + d_max) 
\<and> (w \<le> w_max))_TYPES*) => bool"
where 
"(
(z = init) 
\<and> (d = 0) 
\<and> (k_w = works \<and>
 k_d = works) 
\<and> (w \<ge> w_min + d_max) 
\<and> (w \<le> w_max)) (*(
(z = init) 
\<and> (d = 0) 
\<and> (k_w = works \<and>
 k_d = works) 
\<and> (w \<ge> w_min + d_max) 
\<and> (w \<le> w_max))_VARIABLES*) == (*PRECONDITION*) "

definition SInitEmpty0 :: 
"(*SInitEmpty0_TYPES*) => bool"
where 
"SInitEmpty0 (*SInitEmpty0_VARIABLES*) == True"

definition SInitFill0 :: 
"(*SInitFill0_TYPES*) => bool"
where 
"SInitFill0 (*SInitFill0_VARIABLES*) == True"

definition (
(z = init) 
\<and> (d = 0) 
\<and> (w < w_min + d_max)) :: 
 "(*(
(z = init) 
\<and> (d = 0) 
\<and> (w < w_min + d_max))_TYPES*) => bool"
where 
"(
(z = init) 
\<and> (d = 0) 
\<and> (w < w_min + d_max)) (*(
(z = init) 
\<and> (d = 0) 
\<and> (w < w_min + d_max))_VARIABLES*) == (*PRECONDITION*) "

definition SNormalFill00 :: 
"(*SNormalFill00_TYPES*) => bool"
where 
"SNormalFill00 (*SNormalFill00_VARIABLES*) ==
 ((
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))9)
\<and> ((
(w \<le> w_max) 
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on))1)"

definition (
(z' = z) 
\<and> (v' = closed) 
\<and> (a' = off)) :: 
"(*(
(z' = z) 
\<and> (v' = closed) 
\<and> (a' = off))_TYPES*) => bool"
where 
"(
(z' = z) 
\<and> (v' = closed) 
\<and> (a' = off)) (*(
(z' = z) 
\<and> (v' = closed) 
\<and> (a' = off))_VARIABLES*) == (*POSTCONDITION*) "

definition (
(z' = z) 
\<and> (v' = open) 
\<and> (a' = off)) :: 
"(*(
(z' = z) 
\<and> (v' = open) 
\<and> (a' = off))_TYPES*) => bool"
where 
"(
(z' = z) 
\<and> (v' = open) 
\<and> (a' = off)) (*(
(z' = z) 
\<and> (v' = open) 
\<and> (a' = off))_VARIABLES*) == (*POSTCONDITION*) "

definition (
(w \<le> w_max) 
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on)) :: 
"(*(
(w \<le> w_max) 
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on))_TYPES*) => bool"
where 
"(
(w \<le> w_max) 
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on)) (*(
(w \<le> w_max) 
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on))_VARIABLES*) == (*POSTCONDITION*) "

definition P(
) :: 
"(*P(
)_TYPES*) => bool"
where 
"P(
) (*P(
)_VARIABLES*) == (*POSTCONDITION*) "

definition SNormalBroken1 :: 
"(*SNormalBroken1_TYPES*) => bool"
where 
"SNormalBroken1 (*SNormalBroken1_VARIABLES*) ==
 ((
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))8)
\<and> ((
(w \<le> w_max) 
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on))0)"

definition SNormalFill1 :: 
"(*SNormalFill1_TYPES*) => bool"
where 
"SNormalFill1 (*SNormalFill1_VARIABLES*) ==
 ((
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))3)
\<and> ((
(a' = off) 
\<and> (z' = init))5)"

definition SNormalNotFill1 :: 
"(*SNormalNotFill1_TYPES*) => bool"
where 
"SNormalNotFill1 (*SNormalNotFill1_VARIABLES*) ==
 ((
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))5)
\<and> ((
(a' = off) 
\<and> (z' = init))7)"

definition SNormalFill0 :: 
"(*SNormalFill0_TYPES*) => bool"
where 
"SNormalFill0 (*SNormalFill0_VARIABLES*) ==
 ((
(z = norm) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_opt -3l)))
\<and> ((
(v' = closed \<and>
 a' = on \<and>
 z' = z)))"

definition SNormalNotFill0 :: 
"(*SNormalNotFill0_TYPES*) => bool"
where 
"SNormalNotFill0 (*SNormalNotFill0_VARIABLES*) ==
 ((
(z = norm) 
\<and> (w > w_opt) 
\<and> (w \<le> w_max)))
\<and> ((
(v' = closed \<and>
 a' = on \<and>
 z' = z)))"

definition SNormalFill01 :: 
"(*SNormalFill01_TYPES*) => bool"
where 
"SNormalFill01 (*SNormalFill01_VARIABLES*) ==
 ((
(z = init) 
\<and> (d > 0))0)
\<and> ((
(w \<le> w_max) 
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on))2)"

definition SNormalFill03 :: 
"(*SNormalFill03_TYPES*) => bool"
where 
"SNormalFill03 (*SNormalFill03_VARIABLES*) ==
 ((
(z = init) 
\<and> (d > 0))2)
\<and> ((
(w \<le> w_max) 
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on))4)"

definition SteamBoilerInit00 :: 
"(*SteamBoilerInit00_TYPES*) => bool"
where 
"SteamBoilerInit00 (*SteamBoilerInit00_VARIABLES*) == True"

definition (
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))2 :: 
 "(*(
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))2_TYPES*) => bool"
where 
"(
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))2 (*(
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max))2_VARIABLES*) == (*PRECONDITION*) "

definition (
(a' = off) 
\<and> (z' = init))1 :: 
"(*(
(a' = off) 
\<and> (z' = init))1_TYPES*) => bool"
where 
"(
(a' = off) 
\<and> (z' = init))1 (*(
(a' = off) 
\<and> (z' = init))1_VARIABLES*) == (*POSTCONDITION*) "

definition (
(a' = off) 
\<and> (z' = init))2 :: 
"(*(
(a' = off) 
\<and> (z' = init))2_TYPES*) => bool"
where 
"(
(a' = off) 
\<and> (z' = init))2 (*(
(a' = off) 
\<and> (z' = init))2_VARIABLES*) == (*POSTCONDITION*) "

definition (
(a' = off) 
\<and> (z' = init))3 :: 
"(*(
(a' = off) 
\<and> (z' = init))3_TYPES*) => bool"
where 
"(
(a' = off) 
\<and> (z' = init))3 (*(
(a' = off) 
\<and> (z' = init))3_VARIABLES*) == (*POSTCONDITION*) "

definition (
(a' = off) 
\<and> (z' = init))4 :: 
"(*(
(a' = off) 
\<and> (z' = init))4_TYPES*) => bool"
where 
"(
(a' = off) 
\<and> (z' = init))4 (*(
(a' = off) 
\<and> (z' = init))4_VARIABLES*) == (*POSTCONDITION*) "

lemma ControlNormal1: 
"(*ControlNormal1_EXPRESSION*)"
sorry

lemma ControlInit1: 
"(*ControlInit1_EXPRESSION*)"
sorry

lemma ControlInit0: 
"(*ControlInit0_EXPRESSION*)"
sorry

lemma ControlNormal0: 
"(*ControlNormal0_EXPRESSION*)"
sorry

lemma Control0: 
"(*Control0_EXPRESSION*)"
sorry

lemma ControlBroken1: 
"(*ControlBroken1_EXPRESSION*)"
sorry

end
end
