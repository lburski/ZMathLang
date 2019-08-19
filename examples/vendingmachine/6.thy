theory 6
imports 
Main 

begin 

datatype State = init | norm | brokenn | stop
datatype OnOff = on |off
datatype OpenClosed = openn | closed
datatype WorksBroken = works | broken

record SteamBoiler0 = 
W_MIN :: nat
W_MAX :: nat
W_OPT :: nat
L :: nat
D_MAX :: nat
DELTA_P :: nat
DELTA_D :: nat
V :: OpenClosed
A :: OnOff
Z :: State
P_1 :: OnOff
P_2 :: OnOff
P_3 :: OnOff
P_4 :: OnOff

locale Steamboiler = 
fixes w_min :: "nat"
and w_max :: "nat"
and w_opt :: "nat"
and l :: "nat"
and d_max :: "nat"
and delta_p :: "nat"
and delta_d :: "nat"
and v :: "OpenClosed"
and a :: "OnOff"
and z :: "State"
and s :: "nat"
and delta :: "nat"
assumes
"w_min < w_max"

begin

definition Input ::
"nat \<Rightarrow> nat \<Rightarrow> bool"
where
" Input w d == True"

definition Pumps ::
"OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"Pumps p_1 p_2 p_3 p_4 == True"

definition PumpsOff ::
"OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"PumpsOff p_1' p_2' p_3' p_4' == ((
(p_1' = off)
\<and> (p_2' = off)
\<and> (p_3' = off)
\<and> (p_4' = off)))"

definition PumpsOn ::
"OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"PumpsOn p_1' p_2' p_3' p_4' == ((
(p_1' = on)
\<and> (p_2' = on)
\<and> (p_3' = on)
\<and> (p_4' = on)))"

definition SteamBoilerInit0 :: 
 "SteamBoiler0 => OpenClosed => OnOff =>  State => bool"
where 
"SteamBoilerInit0 steamboiler0' v' a' z' == ((
(a' = off) 
\<and> (z' = init)))"

definition SInitNormal0 ::
"SteamBoiler0 \<Rightarrow> SteamBoiler0 \<Rightarrow> OpenClosed => OnOff =>  State => nat \<Rightarrow> nat \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SInitNormal0  steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4'  == ((
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max)
\<and> (PumpsOff p_1' p_2' p_3' p_4')
\<and> (z' = norm)
\<and> (v' = closed)
\<and> (a' = on)
))"

definition SInitStop0 ::
"SteamBoiler0 \<Rightarrow> SteamBoiler0 \<Rightarrow> OpenClosed => OnOff =>  State => nat \<Rightarrow> nat \<Rightarrow> bool"
where
"SInitStop0 steamboiler0  steamboiler0' v' a' z' w  d  == ((
(z' = init)
\<and> (d > 0)
\<and> (z' = stop)
))"

definition SInitFill0 ::
"SteamBoiler0 \<Rightarrow> SteamBoiler0 \<Rightarrow> OpenClosed => OnOff =>  State => nat \<Rightarrow> nat \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SInitFill0  steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4'  == ((
(z = init) 
\<and> (d = 0) 
\<and> (w < w_min + d_max)
\<and> (PumpsOn p_1' p_2' p_3' p_4')
\<and> (z' = z)
\<and> (v' = closed)
\<and> (a' = off)
))"

definition SInitEmpty0 ::
"SteamBoiler0 \<Rightarrow> SteamBoiler0 \<Rightarrow> OpenClosed => OnOff =>  State => nat \<Rightarrow> nat \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SInitEmpty0  steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4'  == ((
(z = init) 
\<and> (d = 0) 
\<and> (w > w_max)
\<and> (PumpsOff p_1' p_2' p_3' p_4')
\<and> (z' = z)
\<and> (v' = openn)
\<and> (a' = off)
))"

lemma ControlInit0:
"(SInitNormal0  steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4')
\<or> (SInitStop0 steamboiler0  steamboiler0' v' a' z' w  d)
\<or> (SInitFill0  steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4')
\<or> (SInitEmpty0  steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4')"
apply (unfold SInitNormal0_def SInitStop0_def SInitFill0_def SInitEmpty0_def)
apply (unfold PumpsOff_def PumpsOn_def)
sorry

definition SNormalFill0 ::
"SteamBoiler0 \<Rightarrow> SteamBoiler0 \<Rightarrow> OpenClosed => OnOff =>  State => nat \<Rightarrow> nat \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SNormalFill0  steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4'  == ((
(z = norm)
\<and> (w \<ge> w_min)
\<and> (w \<le> w_opt- 3*l)
\<and> (PumpsOn p_1' p_2' p_3' p_4')
\<and> (v' = closed \<and> a' = on \<and> z' = z)
))"

definition SNormalContinue0 :: 
"SteamBoiler0 \<Rightarrow> SteamBoiler0 \<Rightarrow> OpenClosed => OnOff =>  State => nat \<Rightarrow> nat \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SNormalContinue0  steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4'  == ((
(z = norm) 
\<and> (w > w_opt - 3*l)
\<and> (w \<le> w_opt)
))"

definition SNormalNotFill0 ::
"SteamBoiler0 \<Rightarrow> SteamBoiler0 \<Rightarrow> OpenClosed => OnOff =>  State => nat \<Rightarrow> nat \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SNormalNotFill0  steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4'  == ((
(z = norm)
\<and> (w > w_opt)
\<and> (w \<le> w_max)
\<and> (PumpsOff p_1' p_2' p_3' p_4')
\<and> (v' = closed \<and> a' = on \<and> z' = z)
))"

definition SNormalStop0 :: 
"SteamBoiler0 \<Rightarrow> SteamBoiler0 \<Rightarrow> OpenClosed => OnOff =>  State => nat \<Rightarrow> nat \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SNormalStop0 steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4'  == ((
(z = norm) 
\<and> (w < w_min \<or>
 w > w_max)))
\<and> ((
(a' = off \<and>
 z' = stop)))"

lemma ControlNormal0: 
"(SNormalFill0  steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4')
\<or> (SNormalContinue0  steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4')
\<or> (SNormalNotFill0  steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4')
\<or> (SNormalStop0 steamboiler0  steamboiler0' v' a' z' w  d  p_1' p_2' p_3' p_4')"
by (meson ControlInit0 SInitEmpty0_def SInitFill0_def 
SInitNormal0_def SInitStop0_def State.distinct(4) old.nat.distinct(2))


lemma Control0: 
"(ControlInit0)
\<or> (ControlNormal0)"
by (meson ControlInit0 SInitEmpty0_def SInitFill0_def 
SInitNormal0_def SInitStop0_def State.distinct(4) old.nat.distinct(2))


end

record SteamBoiler1 = SteamBoiler0 +
s :: nat
delta :: nat

definition ControlInput ::
"WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> bool"
where
"ControlInput k_w k_d k_p1 k_p2 k_p3 k_p4 == ((
(True)
))"

definition (in  Steamboiler) SteamBoilerInit1 ::
"SteamBoiler1 \<Rightarrow> OnOff \<Rightarrow> State \<Rightarrow> bool"
where
"SteamBoilerInit1 steamboiler1 a' z' == ((
(a' = off)
\<and> (z' = init)
))"

fun pswitch ::
"(OnOff * WorksBroken) \<Rightarrow> OnOff"
where
"pswitch (on,works) = on"
| "pswitch (on,broken) = off"
| "pswitch (off,works) = off"
| "pswitch (off,broken) = off"

fun pamount :: "(OnOff * WorksBroken) => nat"
   where  "pamount (on , works)  = 1"
| "pamount (off , _) = 0"
| "pamount (_ , broken) = 0"

definition (in  Steamboiler) PumpsControlledOn ::
"OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken
 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> bool"
where
"PumpsControlledOn p_1' p_2' p_3' p_4' k_w k_d k_p1 k_p2 k_p3 k_p4 == ((
((p_1' = pswitch(on,k_p1))
\<and> (p_2' = pswitch(on,k_p2)))
\<and> ((p_3' = pswitch(on,k_p3))
\<and> (p_4' = pswitch(on,k_p4)))
))"

definition (in  Steamboiler) PumpsControlledOff ::
"OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken
 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> bool"
where
"PumpsControlledOff p_1' p_2' p_3' p_4' k_w k_d k_p1 k_p2 k_p3 k_p4 == ((
((p_1' = pswitch(off,k_p1))
\<and> (p_2' = pswitch(off,k_p2)))
\<and> ((p_3' = pswitch(off,k_p3))
\<and> (p_4' = pswitch(off,k_p4)))
))"

definition (in  Steamboiler) SInitNormal1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SInitNormal1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1' p_2' p_3' p_4' ==
((
(z = init)
\<and> (d = 0)
\<and> ((k_w = works) \<and> k_d = works)
\<and> (w \<ge> w_min + d_max)
\<and> (w \<le> w_max)
\<and> (z'= norm)
\<and> (v' = closed)
\<and> (a' = on)
\<and> (s' = w)
\<and> (PumpsOff p_1' p_2' p_3' p_4')
))"

definition (in  Steamboiler) SInitFill1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SInitFill1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1' p_2' p_3' p_4' ==
((
(z = init)
\<and> (d = 0)
\<and> ((k_w = works) \<and> (k_d = works))
\<and> (w < w_min + d_max)
\<and> (z' = z)
\<and> (v' = closed)
\<and> (a' = off)
\<and> (PumpsOn p_1' p_2' p_3' p_4')
))"

definition (in  Steamboiler) SInitEmpty1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SInitEmpty1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1' p_2' p_3' p_4' ==
((
(z = init)
\<and> (d = 0)
\<and> (w > w_max)
\<and> (z' = z)
\<and> (v' = openn)
\<and> (a' = off)
\<and> (PumpsOff p_1' p_2' p_3' p_4')
))"

definition (in  Steamboiler) SInitStop1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SInitStop1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1' p_2' p_3' p_4' ==
((
(z = init)
\<and> ((d > 0) \<or> (k_w = broken) \<or> (k_d = broken))
\<and> (z' = stop)
))"

lemma (in Steamboiler) ControlInit1 : 
"(SInitNormal1 steamboiler1 steamboiler1' w d v' a' z' s' k_w k_d k_p1 k_p2 k_p3 k_p4 p_1' p_2' p_3' p_4')
\<or> (SInitFill1 steamboiler1 steamboiler1' w d v' a' z' s' k_w k_d k_p1 k_p2 k_p3 k_p4 p_1' p_2' p_3' p_4')
\<or> (SInitEmpty1 steamboiler1 steamboiler1' w d v' a' z' s' k_w k_d k_p1 k_p2 k_p3 k_p4 p_1' p_2' p_3' p_4')
\<or> (SInitStop1 steamboiler1 steamboiler1' w d v' a' z' s' k_w k_d k_p1 k_p2 k_p3 k_p4 p_1' p_2' p_3' p_4')"
using ControlInit0 SInitEmpty0_def SInitFill0_def SInitNormal0_def SInitStop0_def by fastforce


definition (in  Steamboiler) SNormalFill1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SNormalFill1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1' p_2' p_3' p_4' ==
((
(z = norm)
\<and> (k_w = works)
\<and> (w \<ge> w_min)
\<and> (w \<le> w_opt - 3 * l)
\<and> (s' = w)
\<and> (PumpsControlledOn p_1' p_2' p_3' p_4' k_w k_d k_p1 k_p2 k_p3 k_p4)
\<and> ((v' = closed) \<and> (a' = on) \<and> (z' = z))
))"

definition (in  Steamboiler) SNormalContinue1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SNormalContinue1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1 p_2 p_3 p_4
p_1' p_2' p_3' p_4' ==
((
(z = norm)
\<and> (k_w = works)
\<and> (w > w_opt - 3 * l)
\<and> (w \<le> w_opt)
\<and> ((p_1' = pswitch(p_1, k_p1)) \<and> (p_2' = pswitch(p_2, k_p2)))
\<and> ((p_3' = pswitch(p_3, k_p3)) \<and> (p_4' = pswitch(p_2, k_p4)))
\<and> (s' = w)
\<and> ((v' = v) \<and> (a' = a) \<and> (z' = z))
))"

definition (in  Steamboiler) SNormalNotFill1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SNormalNotFill1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1' p_2' p_3' p_4' ==
((
(z = norm)
\<and> (k_w = works)
\<and> (w > w_opt)
\<and> (w \<le> w_max)
\<and> (s' = w)
\<and> (PumpsControlledOff p_1' p_2' p_3' p_4' k_w k_d k_p1 k_p2 k_p3 k_p4)
\<and> ((v' = closed) \<and> (a' = on) \<and> (z' = z))
))"

definition (in  Steamboiler) SNormalWaterStop1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SNormalWaterStop1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1' p_2' p_3' p_4' ==
((
((z = norm) \<or> (z = brokenn))
\<and> (k_w = works)
\<and> ((w < w_min) \<or> (w > w_max))
\<and> ((a' = off) \<and> (z' = stop))
))"

definition (in  Steamboiler) SNormalControlStop1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SNormalControlStop1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1' p_2' p_3' p_4' ==
((
(z = norm)
\<and> ((k_w = broken) \<and> (k_d = broken))
\<and> ((a' = off) \<and> (z' = stop))
))"

definition (in  Steamboiler) AmountComputation ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
nat \<Rightarrow> nat \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"AmountComputation steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1 p_2 p_3 p_4
amount delta_pumps
p_1' p_2' p_3' p_4' ==
((
(amount = l * (pamount(p_1, k_p1) + pamount(p_2, k_p2) +
pamount(p_3, k_p3) + pamount(p_4, k_p4)))
\<and> (delta_pumps = delta_p * (pamount(p_1, works) + pamount(p_2, works) +
pamount(p_3, works) + pamount(p_4, works)))
))"

definition (in  Steamboiler) SNormalBroken1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SNormalBroken1 steamboiler1 steamboiler1' w d v' a' z' s' 
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1 p_2 p_3 p_4
amount delta_pumps delta'
p_1' p_2' p_3' p_4' ==
((
(z = norm)
\<and> (k_w = broken)
\<and> (k_d = works)
\<and> (s' = s + amount - d)
\<and> (delta' = delta_pumps + delta_d)
\<and> (s' \<ge> w_min + delta')
\<and> (s' \<le> w_max - delta')
\<and> ((s' < ((w_min + w_max)(*/2*))) \<longrightarrow> (PumpsControlledOn p_1' p_2' p_3' p_4' k_w k_d k_p1 k_p2 k_p3 k_p4))
\<and> ((s' \<ge> ((w_min + w_max)(*/2*))) \<longrightarrow> (PumpsControlledOff p_1' p_2' p_3' p_4' k_w k_d k_p1 k_p2 k_p3 k_p4))
\<and> ((v' = closed) \<and> (a' = on))
\<and> (z' = brokenn)
))"

lemma (in Steamboiler) ControlNormal1: 
"(SNormalFill1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1' p_2' p_3' p_4')
\<or> (SNormalContinue1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1 p_2 p_3 p_4
p_1' p_2' p_3' p_4')
\<or> (SNormalNotFill1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1' p_2' p_3' p_4')
\<or> (SNormalWaterStop1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1' p_2' p_3' p_4')
\<or> (SNormalControlStop1 steamboiler1 steamboiler1' w d v' a' z' s'
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1' p_2' p_3' p_4')
\<or> (SNormalBroken1 steamboiler1 steamboiler1' w d v' a' z' s' k_w k_d k_p1 k_p2 k_p3 k_p4 p_1 p_2 p_3 p_4 amount delta_pumps delta' p_1' p_2' p_3' p_4' )"
sorry

definition (in  Steamboiler) SBrokenContinue1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SBrokenContinue1 steamboiler1 steamboiler1' w d v' a' z' s' 
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1 p_2 p_3 p_4
amount delta_pumps delta'
p_1' p_2' p_3' p_4' == ((
(z = brokenn)
\<and> (k_w = broken)
\<and> (k_d = works)
\<and> (s' = s + amount -d)
\<and> (delta' = delta + delta_pumps + delta_d)
\<and> (s' \<ge> w_min + delta')
\<and> (s' \<le> w_max -d)
\<and> (s' < ((w_min + w_max)(*/2*)) \<longrightarrow> (PumpsControlledOn p_1' p_2' p_3' p_4' k_w k_d k_p1 k_p2 k_p3 k_p4))
\<and> (s' \<ge> ((w_min + w_max)(*/2*)) \<longrightarrow> (PumpsControlledOn p_1' p_2' p_3' p_4' k_w k_d k_p1 k_p2 k_p3 k_p4))
\<and> ((v' = closed) \<and> (a' = on))
\<and> (z' = brokenn)
))"

definition (in  Steamboiler) SBrokenNormal1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SBrokenNormal1 steamboiler1 steamboiler1' w d v' a' z' s' 
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1 p_2 p_3 p_4
amount delta_pumps delta'
p_1' p_2' p_3' p_4' == ((
(z = brokenn)
\<and> (k_w = works)
\<and> (w \<ge> w_min)
\<and> (w \<le> w_max)
\<and> (w < ((w_min + w_max)(*/2*)) \<longrightarrow> (PumpsControlledOn p_1' p_2' p_3' p_4' k_w k_d k_p1 k_p2 k_p3 k_p4))
\<and> (w \<ge> ((w_min + w_max)(*/2*)) \<longrightarrow> (PumpsControlledOn p_1' p_2' p_3' p_4' k_w k_d k_p1 k_p2 k_p3 k_p4))
\<and> (s' = w)
\<and> ((v' = closed) \<and> (a' = on))
\<and> (z' = norm)
))"

definition (in  Steamboiler) SBrokenControlStop1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SBrokenControlStop1 steamboiler1 steamboiler1' w d v' a' z' s' 
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1 p_2 p_3 p_4
amount delta_pumps delta'
p_1' p_2' p_3' p_4' == ((
(z = brokenn)
\<and> (k_w = broken)
\<and> (k_d = broken)
\<and> ((a' = off) \<and> (z' = stop))
))"

definition (in  Steamboiler) SBrokenWaterStop1 ::
"SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpenClosed => OnOff => State => nat \<Rightarrow>
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow>
nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where
"SBrokenWaterStop1 steamboiler1 steamboiler1' w d v' a' z' s' 
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1 p_2 p_3 p_4
amount delta_pumps delta'
p_1' p_2' p_3' p_4' == ((
((z = brokenn) \<or> (z = norm))
\<and> (k_w = broken)
\<and> (k_d = works)
\<and> (s' = s + amount - d)
\<and> ((z = brokenn) \<longrightarrow> (delta' = delta + delta_pumps + delta_d))
\<and> ((z = norm) \<longrightarrow> (delta' = delta_pumps + delta_d))
\<and> ((s' < w_min + delta') \<or> (s' > w_max - delta'))
\<and> ((a' = off) \<and> (z' = stop))
))"

lemma (in  Steamboiler) ControlBroken1:
"(SBrokenContinue1 steamboiler1 steamboiler1' w d v' a' z' s' 
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1 p_2 p_3 p_4
amount delta_pumps delta'
p_1' p_2' p_3' p_4')
\<or> (SBrokenNormal1 steamboiler1 steamboiler1' w d v' a' z' s' 
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1 p_2 p_3 p_4
amount delta_pumps delta'
p_1' p_2' p_3' p_4')
\<or> (SBrokenControlStop1 steamboiler1 steamboiler1' w d v' a' z' s' 
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1 p_2 p_3 p_4
amount delta_pumps delta'
p_1' p_2' p_3' p_4')
\<or> (SBrokenWaterStop1 steamboiler1 steamboiler1' w d v' a' z' s' 
k_w k_d k_p1 k_p2 k_p3 k_p4 
p_1 p_2 p_3 p_4
amount delta_pumps delta'
p_1' p_2' p_3' p_4')"
proof -
  have "norm = z"
    by (metis (no_types) ControlNormal0 SNormalContinue0_def SNormalFill0_def SNormalNotFill0_def SNormalStop0_def)
  thus ?thesis
    using ControlInit1 SInitEmpty1_def SInitFill1_def SInitNormal1_def SInitStop1_def by auto
qed


lemma (in  Steamboiler) Control1:
"(ControlInit1)
\<or> (ControlNormal1)
\<or> (ControlBroken1)"
by (metis ControlInit1 ControlNormal0 SInitEmpty1_def 
SInitFill1_def SInitNormal1_def SInitStop1_def SNormalContinue0_def 
SNormalFill0_def SNormalNotFill0_def SNormalStop0_def State.distinct(2))



end