theory 5
imports 
Main 

begin 

typedecl PERSON
datatype GENDER = male | female


record GenDB = 
PARENT :: "(PERSON * PERSON) set"
SEX :: "(PERSON * GENDER) set"

locale 1n2 = 
fixes parent :: "(PERSON * PERSON) set"
and sex :: "(PERSON * GENDER) set"
assumes "Domain parent \<union> Range parent \<subseteq> Domain sex" 
 and "\<forall>p. PERSON <longrightarrow p, p \<notin> parentplus" 
 and "\<forall>p q r. PERSON <longrightarrow {(p, q p, r )} \<subseteq> parent" 
 and "q \<noteq> r \<longrightarrow> sex q \<noteq> sex r"
begin

definition InitGenDB :: 
 "(PERSON * PERSON) set => (PERSON * GENDER) set => bool"
where 
"InitGenDB parent' sex' == ((
(sex' = {}) 
\<and> (parent' = {})))"

definition CommonAncestors :: 
 "GenDB => GenDB => PERSON => PERSON =>  PERSON set => PERSON => nat => nat => bool"
where 
"CommonAncestors gendb gendb' p q cas ca m n == ((
({(p q)} \<union> cas \<subseteq> Domain sex)))
\<and> ((
(cas = {(ca. PERSON) 
\<and> (p, ca \<in> parent^n) 
\<and> (q, ca \<in> parent^m)) 
\<and> (p, r \<in> parent^x)))"

definition Cousins :: 
 "GenDB => GenDB => PERSON => nat => nat =>  PERSON set => bool"
where 
"Cousins gendb gendb' p nth rem cousins == ((
({(p)} \<union> cousins \<subseteq> Domain sex )))
\<and> ((
))"

definition ChangeName :: 
"GenDB => GenDB => (PERSON * PERSON) set => (PERSON * GENDER) set => PERSON => PERSON => PERSON => PERSON => bool"
where 
"ChangeName gendb gendb' parent' sex' old new x ==
 ((
(old \<in> Domain sex) 
\<and> (new \<notin> Domain sex)))
\<and> ((
(sex' = ({(old)} n\<lhd> sex) \<union> {(new, sex old)}) 
\<and> (parent' = ({(old)} n\<lhd> parent \<unlhd> {(old)}) 
\<and> (x \<in> parent \<lparr> {(old)} \<rparr>)))"

definition ChangeSex :: 
"GenDB => GenDB => (PERSON * PERSON) set => (PERSON * GENDER) set => PERSON => bool"
where 
"ChangeSex gendb gendb' parent' sex' p ==
 ((
(p \<in> Domain sex)))
\<and> ((
(parent' = parent)))"

definition AddPerson :: 
"GenDB => GenDB => (PERSON * PERSON) set => (PERSON * GENDER) set => PERSON => GENDER => bool"
where 
"AddPerson gendb gendb' parent' sex' name morf ==
 ((
(name \<notin> Domain sex)))
\<and> (P(
))"

definition AddRel :: 
"GenDB => GenDB => (PERSON * PERSON) set => (PERSON * GENDER) set => PERSON => PERSON => PERSON => bool"
where 
"AddRel gendb gendb' parent' sex' off par x ==
 ((
({(off par)} \<subseteq> Domain sex) 
\<and> (off, par \<notin> parent) 
\<and> (par, off \<notin> parent) 
\<and> (card({(off)} \<lhd> parent) \<le> 1)))
\<and> ((
(off, x \<in> parent) 
\<and> (sex x \<noteq> sex par) 
\<and> (sex' = sex)))"

end
end