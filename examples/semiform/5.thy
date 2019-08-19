theory 5
imports 
Main 

begin 
datatype events = press_att_cws | press_cas_eng | press_alt_eng | 
 press_fpa_sel
datatype mode_status = off | engaged


record AutoPilot = 
ALT_ENG :: "mode_status"
CAS_ENG :: "mode_status"
ATT_CWS :: "mode_status"
FPA_SEL :: "mode_status"


locale theautopilot = 
fixes alt_eng :: "mode_status"
and cas_eng :: "mode_status"
and att_cws :: "mode_status"
and fpa_sel :: "mode_status"
 
begin

definition off_eng :: 
 "mode_status => bool"
where 
"off_eng mode == (mode = off \<or> mode = engaged)"

definition att_cwsDo :: 
"mode_status \<Rightarrow> mode_status \<Rightarrow> mode_status \<Rightarrow> mode_status => bool"
where 
"att_cwsDo fpa_sel' cas_eng' att_cws' alt_eng'  ==
 (att_cws = off)
\<and> (att_cws' = engaged) 
\<and> (fpa_sel' = off) 
\<and> (alt_eng' = off) 
\<and> (cas_eng' = off \<or>
 cas_eng' = engaged)"

end
end
