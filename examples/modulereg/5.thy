theory gpsazml_modulereg
imports 
Main 

begin 

typedecl PERSON
typedecl MODULE

record ModuleReg = 
STUDENTS :: " PERSON set"
DEGMODULES :: " MODULE set"
TAKING :: "(PERSON * MODULE) set"

locale zml_modulereg = 
fixes students :: " PERSON set"
and degModules :: " MODULE set"
and taking :: "(PERSON * MODULE) set"
assumes "Domain taking \<subseteq> students" 
 and "Range taking \<subseteq> degModules"
begin

definition RegForModule :: 
"ModuleReg => ModuleReg =>  PERSON set =>  MODULE set
 => (PERSON * MODULE) set => PERSON => MODULE => bool"
where 
"RegForModule modulereg modulereg' students' 
degModules' taking' p m ==
 ((
(p \<in> students) 
\<and> (m \<in> degModules) 
\<and> (p, m \<notin> taking)))
\<and> ((
(taking' = taking \<union> {(p, m)}) 
\<and> (students' = students) 
\<and> (degModules' = degModules)))"

definition AddStudent :: 
"ModuleReg => ModuleReg =>  PERSON set =>  MODULE set =>
 (PERSON * MODULE) set => PERSON => bool"
where 
"AddStudent modulereg modulereg' students' degModules'
 taking' p ==
 ((
(p \<notin> students)))
\<and> ((
(students' = students \<union> {(p)}) 
\<and> (degModules' = degModules) 
\<and> (taking' = taking)))"

end
end