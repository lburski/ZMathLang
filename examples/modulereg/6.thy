theory 6
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
"ModuleReg => ModuleReg =>  PERSON set =>  
MODULE set => (PERSON * MODULE) set => PERSON
 => MODULE => bool"
where 
"RegForModule modulereg modulereg' students'
degModules' taking' p m ==
 ((
(p \<in> students) 
\<and> (m \<in> degModules) 
\<and> ((p, m) \<notin> taking)))
\<and> ((
(taking' = taking \<union> {(p, m)}) 
\<and> (students' = students) 
\<and> (degModules' = degModules)))"

definition AddStudent :: 
"ModuleReg => ModuleReg =>  PERSON set =>  
MODULE set => (PERSON * MODULE) set => PERSON => bool"
where 
"AddStudent modulereg modulereg' students' 
degModules' taking' p ==
 ((
(p \<notin> students)))
\<and> ((
(students' = students \<union> {(p)}) 
\<and> (degModules' = degModules) 
\<and> (taking' = taking)))"

lemma pre_AddStudent:
"(\<exists> modulereg modulereg' students' degModules' taking'.
AddStudent modulereg modulereg' students' degModules' taking' p)
\<longleftrightarrow> (p \<notin> students)"
apply (unfold AddStudent_def)
apply auto
done

lemma pre_RegForModule:
"(\<exists> modulereg modulereg' students' degModules' taking'.
RegForModule modulereg modulereg' students' degModules' taking' p m)
 \<longleftrightarrow> (p \<in> students)
 \<and> (m \<in> degModules)
 \<and> ((p,m) \<notin> taking)"
 apply (unfold RegForModule_def)
 apply auto
done

definition InitModuleReg::
"ModuleReg \<Rightarrow> PERSON set \<Rightarrow> MODULE set \<Rightarrow> (PERSON * MODULE) set \<Rightarrow> bool"
where
"InitModuleReg modulereg' students' degmodules' taking' == ((
(students' = {})
\<and> (degmodules' = {})
\<and> (taking' = {})))"

(*PO1 proof obligation showing init goes with the state invariants*)

lemma InitOK:
"(\<exists> modulereg'. InitModuleReg modulereg' students' degmodules' taking')
\<longrightarrow>  ((
(students' = {})
\<and> (degmodules' = {})
\<and> (taking' = {})))
\<and> ((Domain taking' \<subseteq> students')
\<and> (Range taking' \<subseteq> degModules'))"
by (simp add: InitModuleReg_def)

(*PO2 obligations *)

lemma AddStudentDoesntChangeSI:
"(\<exists> taking taking'  :: (PERSON * MODULE) set.
 \<exists>degModules degModules':: MODULE set.
 \<exists>students students':: PERSON set.
  \<exists>p :: PERSON.
(students' = students \<union> {(p)}) 
\<and> (taking' = taking)
\<and> (degModules' = degModules)
\<and> (Domain taking \<subseteq> students)
\<and> (Range taking \<subseteq> degModules)
\<and> (Domain taking' \<subseteq> students')
\<and> (Range taking' \<subseteq> degModules')
) "
by blast

lemma RegForModuleDoesntChangeSI:
"(\<exists> taking taking'  :: (PERSON * MODULE) set.
 \<exists>degModules degModules':: MODULE set.
 \<exists>students students':: PERSON set.
  \<exists>p :: PERSON.
 \<exists>m :: MODULE.
(taking' = taking \<union> {(p, m)})
\<and> (students' = students) 
\<and> (degModules' = degModules)
\<and> (Domain taking \<subseteq> students)
\<and> (Range taking \<subseteq> degModules)
\<and> (Domain taking' \<subseteq> students')
\<and> (Range taking' \<subseteq> degModules')
) "
by blast


(* Here I start PO3 obligations *)

lemma RegForModuleNotEmpty:
"(\<exists> modulereg modulereg' students' degModules' taking' p m.
RegForModule modulereg modulereg' students' degModules' taking' p m)
 \<longrightarrow> (students \<noteq> {})
 \<and> (degModules \<noteq> {})"
by (smt RegForModule_def empty_iff empty_iff)

(*Here i start PO4 which are other proof obligations*)

lemma notEmpty:
"(taking' = taking \<union> {(p,m)}) \<longrightarrow> (taking' \<noteq> {})"
by (smt Un_empty insert_not_empty)


end
end
