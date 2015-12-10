theory fillinbb
imports 
Main 

begin 

typedecl NAME
typedecl DATE
datatype REPORT = ok | already_known | not_known

datatype  REPORT .. = ok | already_known | not_known

record SS1 = 
KNOWN :: " NAME set"
BIRTHDAY :: "(NAME * DATE) set"

locale zmathlang_birthdaybook = 
fixes known :: " NAME set"
and birthday :: "(NAME * DATE) set"
assumes "known = Domain birthday"
begin

definition IS1 :: 
 "(NAME * DATE) set =>  NAME set => bool"
where 
"IS1 birthday' known' == ((
(known' = {})))"

definition OS1 :: 
 "SS1 => SS1 => NAME => DATE => bool"
where 
"OS1 birthdaybook birthdaybook' name date == ((
(name \<in> known)))
\<and> ((
(date = birthday (name))))"

definition CS1 :: 
"SS1 => SS1 =>  NAME set => (NAME * DATE) set => NAME => DATE => bool"
where 
"CS1 birthdaybook birthdaybook' known' birthday' name date ==
 ((
(name \<notin> known)))
\<and> ((
(birthday' = birthday \<union> {(name  date)})))"

definition OS5 :: 
 "SS1 => SS1 => NAME => REPORT => bool"
where 
"OS5 birthdaybook birthdaybook' name result == ((
(name \<notin> known)))
\<and> ((
(result = not_known)))"

definition OS4 :: 
 "SS1 => SS1 => NAME => REPORT => bool"
where 
"OS4 birthdaybook birthdaybook' name result == ((
(name \<in> known)))
\<and> ((
(result = already_known)))"

definition OS3 :: 
 "REPORT => bool"
where 
"OS3 result == ((
(result = ok)))"

lemma TS2: 
"(((OS1 birthdaybook birthdaybook' name date) birthdaybook birthdaybook' name date) <and>
 (OS3 result)) <or>
 ((OS5 birthdaybook birthdaybook' name result) birthdaybook birthdaybook' name result) "
sorry

lemma TS1: 
"(((CS1 birthdaybook birthdaybook' known' birthday' name date) birthdaybook birthdaybook' known' birthday' name date) <and>
 (OS3 result))  <or>
 ((OS4 birthdaybook birthdaybook' name result) birthdaybook birthdaybook' name result) "
sorry

end
end
