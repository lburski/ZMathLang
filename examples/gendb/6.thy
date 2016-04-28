theory 6
imports 
Main 

begin 

typedecl PERSON
datatype GENDER = male | female


record GenDB = 
PARENT :: "(PERSON * PERSON) set"
SEX :: "PERSON \<rightharpoonup> GENDER"

locale zml_gendb  = 
fixes parent :: "(PERSON * PERSON) set"
and sex :: "(PERSON \<rightharpoonup> GENDER)"
assumes "Domain parent \<union> Range parent \<subseteq> dom sex" 
 and "(\<forall>p. PERSON \<longrightarrow>  (p, p) \<notin> parent^*)" 
 and "(\<forall>p q r. PERSON \<longrightarrow>  {(p,q),(p,r)} \<subseteq> parent)" 
 and "q \<noteq> r \<longrightarrow> the (sex q) \<noteq> the (sex r)"
begin

definition InitGenDB :: 
 "(PERSON * PERSON) set => (PERSON * GENDER) set => bool"
where 
"InitGenDB parent' sex' == ((
(sex' = {}) 
\<and> (parent' = {})))"

definition CommonAncestors ::
"GenDB \<Rightarrow> GenDB \<Rightarrow> PERSON \<Rightarrow> PERSON \<Rightarrow> PERSON set \<Rightarrow> bool"
where
"CommonAncestors gendb  gendb' p q cas == ((
({p,q} \<union> cas \<subseteq> dom sex)
(*\<and> cas = {ca. (\<exists>m n::nat. ((p,ca) \<in> parent^n \<and> (q,ca) \<in> parent^m)
\<and> (\<exists>r x y. (x+y < m + n)
\<and> ((p,r) \<in> parent^x)
\<and> ((q,r) \<in> parent^y)))}*)
))"

definition Cousins :: 
 "GenDB => GenDB => PERSON => nat => nat => PERSON set => bool"
where 
"Cousins gendb gendb' p n rem cousins == ((
({p} \<union> cousins \<subseteq> dom sex )
(*\<and> (let cosrel = (parent^(n + 1) semi (parent^-1)^(n+1+rem)) - (parent semi parent^1)
 in (cousins = cosrel \<lparr>{p}\<rparr> \<union> cosrel^-1 \<lparr>{p}\<rparr>))*)
))"

definition ChangeName :: 
"GenDB => GenDB => (PERSON * PERSON) set => (PERSON \<rightharpoonup> GENDER) => PERSON => PERSON => bool"
where 
"ChangeName gendb gendb' parent' sex' old new ==
 ((
(old \<in> dom sex) 
\<and> (new \<notin> dom sex)
(*\<and> ( ({p. (old, p) \<notin> parent})= parent' )
\<union> {x.PERSON \<longrightarrow> x \<in> parent\<lparr>{old}\<rparr>}
\<union> {x.PERSON \<longrightarrow> x \<notin> parent^-1 \<lparr>{old}\<rparr>}*)
))"

definition ChangeSex :: 
"GenDB => GenDB => (PERSON * PERSON) set => (PERSON \<rightharpoonup> GENDER) => PERSON => bool"
where 
"ChangeSex gendb gendb' parent' sex' p ==
 ((
(p \<in> dom sex)
(*\<and> sex' = sex \<oplus>
({q s. (q \<in> PERSON) \<and> s \<in> GENDER \<longleftrightarrow>}
((q \<in> (parent^-1 semi parent)^* \<lparr>{p?}\<rparr>)
\<and> (s \<noteq> the sex q)})) *)
\<and> (parent' = parent)))"

definition AddPerson :: 
"GenDB => GenDB => (PERSON * PERSON) set => (PERSON \<rightharpoonup> GENDER) => PERSON => GENDER => bool"
where 
"AddPerson gendb gendb' parent' sex' name morf == ((
(name \<notin> dom sex)
(*\<and> (sex' = sex \<union> {name, morf})*)
\<and> (parent' = parent)
))"

definition AddRel :: 
"GenDB => GenDB => (PERSON * PERSON) set => (PERSON \<rightharpoonup> GENDER) => PERSON => PERSON  => bool"
where 
"AddRel gendb gendb' parent' sex' off par ==
 ((
({off,par} \<subseteq> dom sex)
\<and> ((off, par) \<notin> parent) 
\<and> ((par,off) \<notin> parent)
\<and> (card  ({p. (off, p) \<in> parent}) \<le> 1)
\<and> (\<forall>x.  ((off,x) \<in> parent) \<longrightarrow> (the (sex x) \<noteq> the (sex par)))
\<and> (sex' = sex)))"

lemma pre_AddPerson:
"(\<exists> gendb gendb' parent' sex' morf.
AddPerson gendb gendb' parent' sex' name morf)
\<longleftrightarrow> (name \<notin> dom sex)"
apply (unfold AddPerson_def)
apply auto
done

lemma pre_AddRel:
"(\<exists> gendb gendb' parent' sex'.
AddRel gendb gendb' parent' sex' off par)
\<longleftrightarrow> 
({off,par} \<subseteq> dom sex)
\<and> ((off, par) \<notin> parent) 
\<and> ((par,off) \<notin> parent)
\<and> (card  ({p. (off, p) \<in> parent}) \<le> 1)"
apply (unfold AddRel_def)
sorry

lemma pre_ChangeName:
"(\<exists> gendb gendb' parent' sex'.
ChangeName gendb gendb' parent' sex' old new)
\<longleftrightarrow> 
(old \<in> dom sex) 
\<and> (new \<notin> dom sex)"
apply (unfold ChangeName_def)
apply auto
done

lemma pre_ChangeSex:
"(\<exists> gendb gendb' parent' sex'.
ChangeSex gendb gendb' parent' sex' p)
\<longleftrightarrow> 
(p \<in> dom sex)"
apply (unfold ChangeSex_def)
apply auto
done


end
end