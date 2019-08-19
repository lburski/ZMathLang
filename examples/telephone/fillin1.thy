theory fillin1
imports 
Main 

begin 
typedecl NAME 
typedecl SURNAME
typedecl TELEPHONE
datatype OUTPUT = success | alreadyInDirectory | nameNotInDirectory | numberInUse | numberDoesntExist


record thetelephone = 
PHONENUMBERS :: "(NAME \<rightharpoonup> TELEPHONE) set"
PERSONS :: "(NAME * SURNAME) set"


locale zmathlang_stInvIncorrect = 
fixes phoneNumbers :: "(NAME \<rightharpoonup> TELEPHONE)"
and persons :: "(NAME * SURNAME) set"
 
assumes "dom phoneNumbers = Domain persons"
begin

definition Success :: 
 "OUTPUT \<Rightarrow> NAME \<Rightarrow> SURNAME => bool"
where 
"Success message n s == (message = success)"

definition InitTelephoneDirectory :: 
 "(NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) => bool"
where 
"InitTelephoneDirectory persons' phoneNumbers' == (phoneNumbers' = empty) 
\<and> (persons' = {})"

definition NameNotInDirectory :: 
 "(NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) \<Rightarrow> OUTPUT \<Rightarrow> NAME \<Rightarrow> SURNAME => bool"
where 
"NameNotInDirectory persons' phoneNumbers' message n s == ((n, s) \<notin> persons)
\<and> (message = nameNotInDirectory)"

definition AlreadyInDirectory :: 
 "(NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) \<Rightarrow> OUTPUT \<Rightarrow> NAME \<Rightarrow> SURNAME => bool"
where 
"AlreadyInDirectory persons' phoneNumbers' message n s == ((n, s) \<in> persons)
\<and> (message = alreadyInDirectory)"

definition NumberDoesntExist :: 
 "OUTPUT \<Rightarrow> TELEPHONE => bool"
where 
"NumberDoesntExist message p == (p \<notin> ran phoneNumbers)
\<and> (message = numberDoesntExist)"

definition NumberInUse :: 
 "OUTPUT \<Rightarrow> TELEPHONE => bool"
where 
"NumberInUse message p == (p \<in> ran phoneNumbers)
\<and> (message = numberInUse)"

definition AddPerson :: 
"NAME \<Rightarrow> SURNAME \<Rightarrow> TELEPHONE => (NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) \<Rightarrow> bool"
where 
"AddPerson name surname phone persons' phoneNumbers'== ((name, surname) \<notin> persons)
\<and> (persons' = persons  \<union> {(name, surname)})"

definition TotalAddPerson :: 
"NAME \<Rightarrow> SURNAME \<Rightarrow> TELEPHONE => (NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) \<Rightarrow> NAME \<Rightarrow> SURNAME \<Rightarrow> OUTPUT \<Rightarrow> bool"
where 
"TotalAddPerson name surname phone persons' phoneNumbers' n s message ==
((AddPerson name surname phone persons' phoneNumbers')
\<and> (Success message n s))
\<or> (AlreadyInDirectory persons' phoneNumbers' message n s)"

definition RemoveNumber :: 
"TELEPHONE => (NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE)  \<Rightarrow> SURNAME \<Rightarrow> TELEPHONE \<Rightarrow>bool"
where 
"RemoveNumber phone persons' phoneNumbers' s p ==
 (p \<in> ran phoneNumbers)
\<and> (ran phoneNumbers' = ran phoneNumbers - {p})"

definition RemovePerson :: 
"(NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) \<Rightarrow> NAME \<Rightarrow> SURNAME \<Rightarrow> TELEPHONE => bool"
where 
"RemovePerson persons' phoneNumbers' n s p ==
 ((n, s) \<in> persons)
\<and> (dom phoneNumbers' = dom phoneNumbers - {n}) 
\<and> (persons' = persons - {(n, s)})"

definition AddNumber :: 
"(NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) \<Rightarrow> NAME \<Rightarrow> TELEPHONE => bool"
where 
"AddNumber persons' phoneNumbers' m p ==
 (m \<notin> Domain persons) 
\<and> (p \<notin> ran phoneNumbers)
\<and> (phoneNumbers' = phoneNumbers (m \<mapsto> p))"

definition TotalRemoveNumber ::
"NAME \<Rightarrow> SURNAME \<Rightarrow> TELEPHONE => (NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) \<Rightarrow> NAME \<Rightarrow> SURNAME \<Rightarrow> OUTPUT \<Rightarrow> TELEPHONE \<Rightarrow> bool"
where
"TotalRemoveNumber name surname phone persons' phoneNumbers' n s message p == 
((RemoveNumber phone persons' phoneNumbers' s p)
\<and> (Success message n s))
\<or> (NumberDoesntExist message p)
\<or> (NameNotInDirectory persons' phoneNumbers' message n s)"

definition TotalRemovePerson ::
"NAME \<Rightarrow> SURNAME \<Rightarrow> TELEPHONE => (NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) \<Rightarrow> NAME \<Rightarrow> SURNAME \<Rightarrow> OUTPUT \<Rightarrow> TELEPHONE \<Rightarrow> bool"
where
"TotalRemovePerson name surname phone persons' phoneNumbers' n s message p == 
((RemovePerson persons' phoneNumbers' n s p)
\<and> (Success message n s))
\<or> (NameNotInDirectory persons' phoneNumbers' message n s)"

definition TotalAddNumber ::
"NAME \<Rightarrow> SURNAME \<Rightarrow> TELEPHONE => (NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) \<Rightarrow> NAME \<Rightarrow> SURNAME \<Rightarrow> OUTPUT \<Rightarrow> TELEPHONE \<Rightarrow> NAME \<Rightarrow> bool"
where
"TotalAddNumber name surname phone persons' phoneNumbers' n s message p m ==
((AddNumber persons' phoneNumbers' m p)
\<and> (Success message n s))
\<or> (NameNotInDirectory persons' phoneNumbers' message n s)
\<or> (NumberInUse message p)"

definition TotalPhone ::
"NAME \<Rightarrow> SURNAME \<Rightarrow> TELEPHONE => (NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) \<Rightarrow> NAME \<Rightarrow> SURNAME \<Rightarrow> OUTPUT \<Rightarrow> TELEPHONE \<Rightarrow> NAME \<Rightarrow> bool"
where
"TotalPhone name surname phone persons' phoneNumbers' n s message p m ==
((TotalAddPerson name surname phone persons' phoneNumbers' n s message)
\<or> (TotalRemovePerson name surname phone persons' phoneNumbers' n s message p)
\<or> (TotalAddNumber name surname phone persons' phoneNumbers' n s message p m)
\<or> (TotalRemoveNumber name surname phone persons' phoneNumbers' n s message p))"

lemma AddPerson_L1:
"(\<exists> name :: NAME.
\<exists> surname :: SURNAME.
\<exists> phone :: TELEPHONE.
\<exists> persons' :: (NAME * SURNAME) set.
\<exists> phoneNumbers' :: (NAME \<rightharpoonup> TELEPHONE).
((name, surname) \<notin> persons)
\<and> (persons' = persons  \<union> {(name, surname)})
\<longrightarrow> ((dom phoneNumbers = Domain persons)
\<and> (dom phoneNumbers' = Domain persons')))"
sorry

lemma RemoveNumber_L2:
"(\<exists> phone :: TELEPHONE.
\<exists> persons' :: (NAME * SURNAME) set.
\<exists> phoneNumbers' :: (NAME \<rightharpoonup> TELEPHONE).
\<exists> s :: SURNAME.
\<exists> p :: TELEPHONE.
 (p \<in> ran phoneNumbers)
\<and> (ran phoneNumbers' = ran phoneNumbers - {p})
\<longrightarrow> ((dom phoneNumbers = Domain persons)
\<and> (dom phoneNumbers' = Domain persons')))"
sorry

lemma RemovePerson_L3:
"(\<exists> persons' :: (NAME * SURNAME) set.
\<exists> phoneNumbers' :: (NAME \<rightharpoonup> TELEPHONE).
\<exists> n :: NAME.
\<exists> s :: SURNAME.
\<exists> p :: TELEPHONE.
((n, s) \<in> persons)
\<and> (dom phoneNumbers' = dom phoneNumbers - {n}) 
\<and> (persons' = persons - {(n, s)})
\<longrightarrow> ((dom phoneNumbers = Domain persons)
\<and> (dom phoneNumbers' = Domain persons')))"
sorry

lemma RemoveNumber_L4:
"(\<exists> phone :: TELEPHONE.
\<exists> persons' :: (NAME * SURNAME) set.
\<exists> phoneNumbers :: (NAME \<rightharpoonup> TELEPHONE).
\<exists> s :: SURNAME.
\<exists> p :: TELEPHONE.
 (p \<in> ran phoneNumbers)
\<and> (ran phoneNumbers' = ran phoneNumbers - {p})
\<longrightarrow> ((dom phoneNumbers = Domain persons)
\<and> (dom phoneNumbers' = Domain persons')))"
sorry

end
end
