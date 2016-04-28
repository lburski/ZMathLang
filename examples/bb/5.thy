theory 5
imports 
Main 

begin 

typedecl NAME
typedecl DATE
datatype REPORT = ok | already_known | not_known

datatype  REPORT .. = ok | already_known | not_known

record BirthdayBook = 
KNOWN :: " NAME set"
BIRTHDAY :: "(NAME * DATE) set"

locale zmathlang_birthdaybook = 
fixes known :: " NAME set"
and birthday :: "(NAME * DATE) set"
assumes "known = Domain birthday"
begin

definition InitBirthdayBook :: 
 "(NAME * DATE) set =>  NAME set => bool"
where 
"InitBirthdayBook  birthday' known' == ((
(known' = {})))"

definition FindBirthday :: 
 "BirthdayBook => BirthdayBook => NAME => DATE => bool"
where 
"FindBirthday birthdaybook birthdaybook' name date == ((
(name \<in> known)))
\<and> (
((name, date) \<in> birthday ))"

definition AddBirthday :: 
"SS1 => SS1 =>  NAME set => (NAME * DATE) set => 
NAME => DATE => bool"
where 
"AddBirthday birthdaybook birthdaybook' known' 
birthday' name date ==
 ((
(name \<notin> known)))
\<and> ((
(birthday' = birthday \<union> {(name, date)})))"

definition NotKnown :: 
 "SS1 => SS1 => NAME => REPORT => bool"
where 
"NotKnown birthdaybook birthdaybook' name result == ((
(name \<notin> known)))
\<and> ((
(result = not_known)))"

definition AlreadyKnown :: 
 "SS1 => SS1 => NAME => REPORT => bool"
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

end
end