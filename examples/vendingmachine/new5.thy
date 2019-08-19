theory new5
imports 
Main 

begin 
datatype State = init | norm | broken0 | stop
datatype OnOff = on |off
datatype OpenClosed = open0 | closed
datatype WorksBroken = works | broken

record SteamBoiler0 = 
PSWITCH :: "State"
W_MAX :: "nat"
D_MAX :: "nat"
PAMOUNT :: "State"
W_MIN :: "nat"
A :: "OnOff"
DELTA_D :: "nat"
DELTA_P :: "nat"
L :: "nat"
V :: "OpenClosed"
Z :: "State"
W :: "nat"
D :: "nat"
W_OPT :: "nat"
S :: "nat"
DELTA :: "nat"

locale thesteamboiler = 
fixes 
w_max :: "nat"
and 
d_max :: "nat"
and 
l :: "nat"
and a :: "OnOff"
and 
w_min :: "nat"
and 
delta_p :: "nat"
and 
delta_d :: "nat"
and v :: "OpenClosed"
and z :: "State"
and w :: "nat"
and d :: "nat"
and w_opt :: "nat"
and s :: "nat"
and delta :: "nat"
assumes
"w_min < w_max"
 
begin

(*IS1*)
definition SteamBoilerInit0 :: 
 "SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"SteamBoilerInit0 steamboiler0 a' steamboiler0' z' v' == (a' = off) 
\<and> (z' = init)"

(*CS7*)
definition SNormalStop0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"SNormalStop0 steamboiler0 a' steamboiler0' z' v' ==
 (z = norm) 
\<and> (w < w_min \<or>
 w > w_max)
\<and> (a' = off \<and>
 z' = stop)"

(*CS2*)
definition SInitStop0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"SInitStop0 steamboiler0 a' steamboiler0' z' v' ==
 (z = init) 
\<and> (d > 0)
\<and> (z' = stop)"

(* OS1*)
definition PumpsOff :: 
 "OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => bool"
where 
"PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0' == (p_1' = off \<and>
 p_2' = off \<and>
 p_3' = off \<and>
 p_4' = off)"

(* OS3*)
definition SNormalContinue0 :: 
 "SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"SNormalContinue0 steamboiler0 a' steamboiler0' z' v' == (z = norm) 
\<and> (w > w_opt - 3*l) 
\<and> (w \<le> w_opt)"

(* OS2*)
definition PumpsOn :: 
 "OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => bool"
where 
"PumpsOn p_4' steamboiler0 p_3' p_2' p_1' steamboiler0' == (p_1' = on \<and>
 p_2' = on \<and>       
 p_3' = on \<and>
 p_4' = on)"

(*CS5*)
definition SNormalFill0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SNormalFill0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4'==
 (z = norm) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_opt -3*l)
\<and> ((PumpsOn p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)"

(*CS4*)
definition SInitEmpty0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SInitEmpty0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4' == 
(z = init)
\<and> (d = 0)
\<and> (w > w_max)
\<and> ((PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (z' = z)
\<and> (v' = open0)
\<and> (a' = off)"

(*CS6*)
definition SNormalNotFill0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SNormalNotFill0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4' ==
 (z = norm) 
\<and> (w > w_opt) 
\<and> (w \<le> w_max)
\<and> ((PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)"

(*CS1*)
definition SInitNormal0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SInitNormal0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4' ==
 (z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max)
\<and> (w \<le> w_max) 
\<and> ((PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on)"

(*CS3*)
definition SInitFill0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SInitFill0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4' ==
 (z = init) 
\<and> (d = 0) 
\<and> (w < w_min + d_max)
\<and> ((PumpsOn p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (z' = z) 
\<and> (v' = closed) 
\<and> (a' = off)"

(*TS2*)
definition ControlNormal0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"ControlNormal0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4' == (SNormalFill0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4')
\<or> (SNormalContinue0 steamboiler0 a' steamboiler0' z' v')
\<or> (SNormalNotFill0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4')
\<or> (SNormalStop0 steamboiler0 a' steamboiler0' z' v')"

(*TS1*)
definition ControlInit0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"ControlInit0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4' == (SInitNormal0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4')
\<or> (SInitStop0 steamboiler0 a' steamboiler0' z' v')
\<or> (SInitFill0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4')
\<or> (SInitEmpty0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4')"

(*TS3*)
definition Control0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"Control0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4' == (ControlInit0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4')
\<or> (ControlNormal0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4')"

end

record SteamBoiler1 = SteamBoiler0 +

s :: "nat"
delta :: "nat"

(*IS2*)
definition (in  thesteamboiler) SteamBoilerInit1 :: 
 "SteamBoiler0 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> SteamBoiler0 => OnOff \<Rightarrow> State \<Rightarrow> bool"
where 
"SteamBoilerInit1 steamboiler0 delta' s' steamboiler0' a' z' == (a' = off) 
\<and> (z' = init)"

(*A5*)
fun (in  thesteamboiler) pswitch ::
"(OnOff * WorksBroken) \<Rightarrow> OnOff"
where
"pswitch (on,works) = on"
| "pswitch (on,broken) = off"
| "pswitch (off,works) = off"
| "pswitch (off,broken) = off"

(*A6*)
fun (in  thesteamboiler) pamount :: "(OnOff * WorksBroken) => nat"
   where  "pamount (on , works)  = 1"
| "pamount (off , _) = 0"
| "pamount (_ , broken) = 0"

(* OS5*)
definition (in  thesteamboiler)  PumpsControlledOff :: 
 "OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> WorksBroken => bool"
where 
"PumpsControlledOff p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4 == 
(p_1' = pswitch(off, k_p1) \<and>
 p_2' = pswitch(off, k_p2) \<and>
 p_3' = pswitch(off, k_p3) \<and>
 p_4' = pswitch(off, k_p4))"

(* OS4*)
definition (in  thesteamboiler) PumpsControlledOn :: 
 "OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> WorksBroken => bool"
where 
"PumpsControlledOn p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4 == 
(p_1' = pswitch(on, k_p1) \<and>
 p_2' = pswitch(on, k_p2) \<and>
 p_3' = pswitch(on, k_p3) \<and>
 p_4' = pswitch(on, k_p4))"

(*CS9*)
definition (in  thesteamboiler) SInitFill1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> bool"
where 
"SInitFill1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_4' p_3' p_2' p_1' steamboiler0' z' v' a' ==
 (z = init) 
\<and> (d = 0) 
\<and> (k_w = works \<and>
 k_d = works) 
\<and> (w < w_min + d_max)
\<and> (z' = z) 
\<and> (v' = closed) 
\<and> (a' = off) 
\<and> ((PumpsOn p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))"

(*CS8*)
definition (in  thesteamboiler) SInitNormal1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> bool"
where 
"SInitNormal1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_4' p_3' p_2' p_1' steamboiler0' z' v' a' ==
 (z = init) 
\<and> (d = 0) 
\<and> (k_w = works \<and>
 k_d = works) 
\<and> (w \<ge> w_min + d_max) 
\<and> (w \<le> w_max)
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on) 
\<and> (s' = w) 
\<and> ((PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))"

(*CS11*)
definition (in  thesteamboiler) SInitStop1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => State \<Rightarrow>bool"
where 
"SInitStop1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 steamboiler0' z' ==
 (z = init) 
\<and> (d > 0 \<or>
 k_w = broken \<or> k_d = broken)
\<and> (z' = stop)"

(*CS13*)
definition (in  thesteamboiler) SNormalContinue1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
 OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OnOff \<Rightarrow> OpenClosed \<Rightarrow> bool"
where 
"SNormalContinue1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v'==
 (z = norm) 
\<and> (k_w = works) 
\<and> (w > w_opt - 3*l) 
\<and> (w \<le> w_opt)
\<and> (p_1' = pswitch(p_1, k_p1) \<and>
 p_2' = pswitch(p_2, k_p2)) 
\<and> (p_3' = pswitch(p_3, k_p3) \<and>
 p_4' = pswitch(p_4, k_p4)) 
\<and> (s' = w) 
\<and> (v' = v \<and>
 a' = a \<and>
 z' = z)"

(*CS15*)
definition (in thesteamboiler) SNormalWaterStop1 ::
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OnOff \<Rightarrow> OpenClosed \<Rightarrow> bool"
where
"SNormalWaterStop1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v' == 
(z = norm \<or>
 z = broken0)
\<and> (k_w = works) 
\<and> (w < w_min \<or>
 w > w_max)
\<and> (a' = off \<and>
 z' = stop)"

(*CS14*)
definition (in thesteamboiler) SNormalNotFill1 ::
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OnOff \<Rightarrow> OpenClosed \<Rightarrow> bool"
where
"SNormalNotFill1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v' == 
 (z = norm) 
\<and> (k_w = works) 
\<and> (w > w_opt) 
\<and> (w \<le> w_max)
\<and> (s' = w) 
\<and> (PumpsControlledOff p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4) 
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)"

(* OS6*)
definition (in thesteamboiler) AmountComputation :: 
"nat \<Rightarrow> nat => SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OnOff \<Rightarrow> OpenClosed \<Rightarrow> bool"
where 
"AmountComputation amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v' == 
(amount = l * (pamount(p_1, k_p1) + pamount(p_2, k_p2) + pamount(p_3, k_p3) + pamount(p_4, k_p4)))
\<and> (delta_pumps = delta_p * (pamount(p_1, works) + pamount(p_2, works) + pamount(p_3, works) + pamount(p_4, works))) "

(* CS20 *)
definition (in thesteamboiler) SBrokenControlStop1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OnOff \<Rightarrow> OpenClosed \<Rightarrow> bool"
where 
"SBrokenControlStop1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v' == 
 (z = broken0) 
\<and> (k_w = broken) 
\<and> (k_d = broken)
\<and> (a' = off \<and>
 z' = stop)"

(*CS21*)
definition (in thesteamboiler) SBrokenWaterStop1 :: 
"nat \<Rightarrow> nat => SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OnOff \<Rightarrow> OpenClosed \<Rightarrow> bool"
where 
"SBrokenWaterStop1 amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v' == 
 (z = broken0 \<or>
 z = norm) 
\<and> (k_w = broken) 
\<and> (k_d = works)
\<and> (s' = s + amount - d) 
\<and> (z = broken0 \<longrightarrow> delta' = delta + delta_pumps + delta_d) 
\<and> (z = norm \<longrightarrow> delta' = delta_pumps + delta_d) 
\<and> (s' < w_min + delta' \<or>
 s' > w_max - delta') 
\<and> (a' = off \<and>
 z' = stop)"

(*CS19*)
definition (in thesteamboiler) SBrokenNormal1 :: 
"nat \<Rightarrow> nat => SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OnOff \<Rightarrow> OpenClosed \<Rightarrow> bool"
where 
"SBrokenNormal1 amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v' ==
 (z = broken0) 
\<and> (k_w = works) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_max) 
\<and> (w < (w_min + w_max) div 2 \<longrightarrow> (PumpsControlledOn p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4))
\<and> (w \<ge> (w_min + w_max) div 2 \<longrightarrow> (PumpsControlledOff p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4))
\<and> (s' = w) 
\<and> (v' = closed \<and>
 a' = on) 
\<and> (z' = norm)"

(*CS18*)
definition (in thesteamboiler) SBrokenContinue1 :: 
"nat \<Rightarrow> nat => SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OnOff \<Rightarrow> OpenClosed \<Rightarrow> bool"
where 
"SBrokenContinue1 amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v' ==
 (z = broken0) 
\<and> (k_w = broken) 
\<and> (k_d = works)
\<and> (s' = s + amount -d) 
\<and> (delta' = delta + delta_pumps + delta_d) 
\<and> (s' \<ge> w_min + delta') 
\<and> (s' \<le> w_max - delta') 
\<and> (s' < (w_min + w_max) div 2 \<longrightarrow> (PumpsControlledOn p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4))
\<and> (s' \<ge> (w_min + w_max) div 2 \<longrightarrow> (PumpsControlledOff p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4))
\<and> (v' = closed \<and>
 a' = on) 
\<and> (z' = broken0)"

(*CS10*)
definition (in thesteamboiler) SInitEmpty1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> bool"
where 
"SInitEmpty1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_4' p_3' p_2' p_1' steamboiler0' z' v' a' ==
 (z = init) 
\<and> (d = 0) 
\<and> (w > w_max)
\<and> (z' = z) 
\<and> (v' = open0) 
\<and> (a' = off) 
\<and> (PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0')"

(*CS12*)
definition (in thesteamboiler) SNormalFill1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> bool"
where 
"SNormalFill1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_4' p_3' p_2' p_1' steamboiler0' z' v' a' ==
 (z = norm) 
\<and> (k_w = works) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_opt - 3*l)
\<and> (s' = w) 
\<and> (PumpsControlledOn p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4)
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)"

(*CS17*)
definition (in thesteamboiler) SNormalBroken1 :: 
"nat \<Rightarrow> nat => SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OnOff \<Rightarrow> OpenClosed \<Rightarrow> bool"
where 
"SNormalBroken1 amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v' ==
 (z = norm) 
\<and> (k_w = broken) 
\<and> (k_d = works) 
\<and> (s' = s + amount -d)
\<and> (delta' = delta_pumps + delta_d)
\<and> (s' \<ge> w_min + delta') 
\<and> (s' \<le> w_max - delta') 
\<and> (s' < (w_min + w_max) div 2 \<longrightarrow> (PumpsControlledOn p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4))
\<and> (s' \<ge> (w_min + w_max) div 2 \<longrightarrow> (PumpsControlledOff p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4))
\<and> (v' = closed \<and>
 a' = on) 
\<and> (z' = broken0)"

(*CS16*)
definition (in thesteamboiler) SNormalControlStop1 :: 
"nat \<Rightarrow> nat => SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OnOff \<Rightarrow> OpenClosed \<Rightarrow> bool"
where 
"SNormalControlStop1 amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v' ==
 (z = norm) 
\<and> (k_w = broken \<and>
 k_d = broken)
\<and> (a' = off \<and>
 z' = stop)"

(*TS6*)
definition (in thesteamboiler) ControlBroken1 :: 
"nat \<Rightarrow> nat => SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OnOff \<Rightarrow> OpenClosed \<Rightarrow> bool"
where 
"ControlBroken1 amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' 
k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v' == (SBrokenContinue1 amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v')
\<or> (SBrokenNormal1  amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v')
\<or> (SBrokenControlStop1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v')
\<or> (SBrokenWaterStop1 amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v')"

(*TS4*)
definition (in thesteamboiler) ControlInit1 :: 
"nat \<Rightarrow> nat => SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OnOff \<Rightarrow> OpenClosed \<Rightarrow> bool"
where 
"ControlInit1 amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' 
k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v' == (SInitNormal1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_4' p_3' p_2' p_1' steamboiler0' z' v' a')
\<or> (SInitFill1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_4' p_3' p_2' p_1' steamboiler0' z' v' a')
\<or> (SInitEmpty1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_4' p_3' p_2' p_1' steamboiler0' z' v' a')
\<or> (SInitStop1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 steamboiler0' z')"

(*TS5*)
definition (in thesteamboiler) ControlNormal1  :: 
"nat \<Rightarrow> nat => SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OnOff \<Rightarrow> OpenClosed \<Rightarrow> bool"
where 
"ControlNormal1  amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' 
k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v' == (SNormalFill1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_4' p_3' p_2' p_1' steamboiler0' z' v' a')
\<or> (SNormalContinue1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v')
\<or> (SNormalNotFill1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v')
\<or> (SNormalWaterStop1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v')
\<or> (SNormalControlStop1 amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v')
\<or> (SNormalBroken1 amount delta_pumps steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_2' p_4' p_1' p_3' p_2 p_4 p_1 p_3 steamboiler0' z' a' v')"


(*Proof Obligations*)

lemma (in  thesteamboiler) SNormalStop0_L1:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
 (z = norm) 
\<and> (w < w_min \<or>
 w > w_max)
\<and> (a' = off \<and>
 z' = stop)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SInitStop0_L2:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
(z = init) 
\<and> (d > 0)
\<and> (z' = stop)
\<longrightarrow>( w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SNormalFill0_L3:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> p_1' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_4' :: OnOff.
(z = norm) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_opt -3*l)
\<and> ((PumpsOn p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SInitEmpty0_L4:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> p_1' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_4' :: OnOff.
(z = init)
\<and> (d = 0)
\<and> (w > w_max)
\<and> ((PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (z' = z)
\<and> (v' = open0)
\<and> (a' = off)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SNormalNotFill0_L5:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> p_1' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_4' :: OnOff.
 (z = norm) 
\<and> (w > w_opt) 
\<and> (w \<le> w_max)
\<and> ((PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SInitNormal01_L6:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> p_1' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_4' :: OnOff.
 (z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max)
\<and> (w \<le> w_max) 
\<and> ((PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SInitFill0_L7:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> p_1' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_4' :: OnOff.
 (z = init) 
\<and> (d = 0) 
\<and> (w < w_min + d_max)
\<and> ((PumpsOn p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (z' = z) 
\<and> (v' = closed) 
\<and> (a' = off)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SInitFill1_L8:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> p_4' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_1' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> a' :: OnOff.
 (z = init) 
\<and> (d = 0) 
\<and> (k_w = works \<and>
 k_d = works) 
\<and> (w < w_min + d_max)
\<and> (z' = z) 
\<and> (v' = closed) 
\<and> (a' = off) 
\<and> ((PumpsOn p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SInitNormal1_L9:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> p_4' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_1' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> a' :: OnOff.
(z = init) 
\<and> (d = 0) 
\<and> (k_w = works \<and>
 k_d = works) 
\<and> (w \<ge> w_min + d_max) 
\<and> (w \<le> w_max)
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on) 
\<and> (s' = w) 
\<and> ((PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SInitStop1_L10:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State.
 (z = init) 
\<and> (d > 0 \<or>
 k_w = broken \<or> k_d = broken)
\<and> (z' = stop)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SNormalContinue1_L11:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> p_4' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_1' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> a' :: OnOff.
 (z = norm) 
\<and> (k_w = works) 
\<and> (w > w_opt - 3*l) 
\<and> (w \<le> w_opt)
\<and> (p_1' = pswitch(p_1, k_p1) \<and>
 p_2' = pswitch(p_2, k_p2)) 
\<and> (p_3' = pswitch(p_3, k_p3) \<and>
 p_4' = pswitch(p_4, k_p4)) 
\<and> (s' = w) 
\<and> (v' = v \<and>
 a' = a \<and>
 z' = z)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SNormalWaterStop1_L12:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> p_4' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_1' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> a' :: OnOff.
(z = norm \<or>
 z = broken0)
\<and> (k_w = works) 
\<and> (w < w_min \<or>
 w > w_max)
\<and> (a' = off \<and>
 z' = stop)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SNormalNotFill1_L13:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> p_4' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_1' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> a' :: OnOff.
 (z = norm) 
\<and> (k_w = works) 
\<and> (w > w_opt) 
\<and> (w \<le> w_max)
\<and> (s' = w) 
\<and> (PumpsControlledOff p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4) 
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SBrokenControlStop1_L14:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> p_4' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_1' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> a' :: OnOff.
 (z = broken0) 
\<and> (k_w = broken) 
\<and> (k_d = broken)
\<and> (a' = off \<and>
 z' = stop)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SBrokenWaterStop1_L15:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> p_4' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_1' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> a' :: OnOff.
 (z = broken0 \<or>
 z = norm) 
\<and> (k_w = broken) 
\<and> (k_d = works)
\<and> (s' = s + amount - d) 
\<and> (z = broken0 \<longrightarrow> delta' = delta + delta_pumps + delta_d) 
\<and> (z = norm \<longrightarrow> delta' = delta_pumps + delta_d) 
\<and> (s' < w_min + delta' \<or>
 s' > w_max - delta') 
\<and> (a' = off \<and>
 z' = stop)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SBrokenNormal1_L16:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> p_4' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_1' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> a' :: OnOff.
 (z = broken0) 
\<and> (k_w = works) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_max) 
\<and> (w < (w_min + w_max) div 2 \<longrightarrow> (PumpsControlledOn p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4))
\<and> (w \<ge> (w_min + w_max) div 2 \<longrightarrow> (PumpsControlledOff p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4))
\<and> (s' = w) 
\<and> (v' = closed \<and>
 a' = on) 
\<and> (z' = norm)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SBrokenContinue1_L17:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> p_4' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_1' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> a' :: OnOff.
 (z = broken0) 
\<and> (k_w = broken) 
\<and> (k_d = works)
\<and> (s' = s + amount -d) 
\<and> (delta' = delta + delta_pumps + delta_d) 
\<and> (s' \<ge> w_min + delta') 
\<and> (s' \<le> w_max - delta') 
\<and> (s' < (w_min + w_max) div 2 \<longrightarrow> (PumpsControlledOn p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4))
\<and> (s' \<ge> (w_min + w_max) div 2 \<longrightarrow> (PumpsControlledOff p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4))
\<and> (v' = closed \<and>
 a' = on) 
\<and> (z' = broken0)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SInitEmpty1_L18:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> p_4' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_1' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> a' :: OnOff.
 (z = init) 
\<and> (d = 0) 
\<and> (w > w_max)
\<and> (z' = z) 
\<and> (v' = open0) 
\<and> (a' = off) 
\<and> (PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0')
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SNormalFill1_L19:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> p_4' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_1' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> a' :: OnOff.
 (z = norm) 
\<and> (k_w = works) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_opt - 3*l)
\<and> (s' = w) 
\<and> (PumpsControlledOn p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4)
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SNormalBroken1_L20:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> p_4' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_1' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> a' :: OnOff.
 (z = norm) 
\<and> (k_w = broken) 
\<and> (k_d = works) 
\<and> (s' = s + amount -d)
\<and> (delta' = delta_pumps + delta_d)
\<and> (s' \<ge> w_min + delta') 
\<and> (s' \<le> w_max - delta') 
\<and> (s' < (w_min + w_max) div 2 \<longrightarrow> (PumpsControlledOn p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4))
\<and> (s' \<ge> (w_min + w_max) div 2 \<longrightarrow> (PumpsControlledOff p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4))
\<and> (v' = closed \<and>
 a' = on) 
\<and> (z' = broken0)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

lemma (in  thesteamboiler) SNormalControlStop1_L21:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w WorksBroken.
\<exists> s' :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> p_4' :: OnOff.
\<exists> p_3' :: OnOff.
\<exists> p_2' :: OnOff.
\<exists> p_1' :: OnOff.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> w_max' :: nat.
\<exists> w_min' :: nat.
\<exists> z' :: State .
\<exists> v' :: OpenClosed.
\<exists> a' :: OnOff.
 (z = norm) 
\<and> (k_w = broken \<and>
 k_d = broken)
\<and> (a' = off \<and>
 z' = stop)
\<longrightarrow> (w_min < w_max
\<and> (w_min' < w_max')))"
sorry

end
