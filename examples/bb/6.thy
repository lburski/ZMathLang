theory 6
imports 
Main 

begin 

typedecl NAME
typedecl DATE
datatype REPORT = ok | already_known | not_known

record BirthdayBook = 
KNOWN :: " NAME set"
BIRTHDAY :: "(NAME * DATE) set"

locale zmathlang_birthdaybook = 
fixes known :: " NAME set"
and birthday :: "(NAME * DATE) set"
assumes "known = Domain birthday"
begin

definition InitBirthdayBook :: 
 "BirthdayBook \<Rightarrow> (NAME * DATE) set =>  NAME set => bool"
where 
"InitBirthdayBook birthdaybook  birthday' known' == ((
((birthday' = {}))
\<and>
(known' = {})))"

definition FindBirthday :: 
 "BirthdayBook => BirthdayBook => NAME => DATE => bool"
where 
"FindBirthday birthdaybook birthdaybook' name date == ((
(name \<in> known)))
\<and> (
((name, date) \<in> birthday ))"

definition AddBirthday :: 
"BirthdayBook => BirthdayBook =>  NAME set => (NAME * DATE) set => 
NAME => DATE => bool"
where 
"AddBirthday birthdaybook birthdaybook' known' 
birthday' name date ==
 ((
(name \<notin> known)))
\<and> ((
(birthday' = birthday \<union> {(name, date)})))"

definition NotKnown :: 
 "BirthdayBook => BirthdayBook => NAME => REPORT => bool"
where 
"NotKnown birthdaybook birthdaybook' name result == ((
(name \<notin> known)))
\<and> ((
(result = not_known)))"

definition AlreadyKnown :: 
 "BirthdayBook  => BirthdayBook => NAME => REPORT => bool"
where 
"AlreadyKnown birthdaybook birthdaybook' name result == ((
(name \<in> known)))
\<and> ((
(result = already_known)))"

definition Success :: 
 "REPORT => bool"
where 
"Success result == ((
(result = ok)))"

definition RFindBirthday :: 
 "BirthdayBook => BirthdayBook => NAME => DATE => REPORT => bool"
where 
"RFindBirthday birthdaybook birthdaybook' name date result = (
((FindBirthday birthdaybook birthdaybook' name date) &
 (Success result)) |
 (NotKnown birthdaybook birthdaybook' name result) ) "

definition RAddBirthday :: 
 "BirthdayBook => BirthdayBook =>  NAME set => 
 (NAME * DATE) set => NAME => DATE => REPORT => bool"
where 
"RAddBirthday birthdaybook birthdaybook' known' 
birthday' name date result = (
((AddBirthday birthdaybook birthdaybook' known' 
birthday' name date) &
 (Success result))  |
 (AlreadyKnown birthdaybook birthdaybook' name result) ) "

definition (in zmathlang_birthdaybook)
birthdaybookstate :: "BirthdayBook \<Rightarrow> bool"
where
"birthdaybookstate birthdaybook == (known = Domain birthday)"

lemma AddBirthdayIsHonest:
"(\<exists> known' birthday' birthdaybook birthdaybook' date.
AddBirthday birthdaybook birthdaybook' known' birthday' name date)
\<longleftrightarrow>
(name \<notin> known)"
apply (unfold AddBirthday_def)
apply auto
done

lemma preAddBirthdayTotal:
" (name \<notin> known) \<or> (name \<in> known)"
apply (rule excluded_middle)
done

lemma BirthdayBookPredicate:
"(\<exists> birthdaybook. birthdaybookstate birthdaybook) 
\<longrightarrow> known = Domain birthday"
apply (rule impI)
apply (unfold birthdaybookstate_def)
apply auto
done

lemma InitisOk:
"(\<exists> birthdaybook. InitBirthdayBook birthdaybook  birthday' known') 
\<longleftrightarrow> (known' = {}) \<and> (birthday'= {})"
apply (unfold InitBirthdayBook_def)
apply auto
done

lemma knownAddBirthday:
"(AddBirthday birthdaybook birthdaybook' 
known' birthday' name date) \<and> 
(InitBirthdayBook birthdaybook birthday' known')
\<longrightarrow> known' = known \<union> {(name)}"
apply (unfold AddBirthday_def)
apply (unfold InitBirthdayBook_def)
apply (rule impI)
apply auto
done

lemma RAddBirthdayIsTotal:
"(\<exists> known' birthday' birthdaybook 
birthdaybook' date.
RAddBirthday birthdaybook birthdaybook' 
known' birthday' name date result)
\<longrightarrow>
(name \<notin> known) \<or> (name \<in> known)"
apply (unfold RAddBirthday_def)
apply (unfold AddBirthday_def AlreadyKnown_def Success_def)
apply auto
done

end
end