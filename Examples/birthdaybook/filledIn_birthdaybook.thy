theory filledIn_birthdaybook
imports 
Main 

begin 

typedecl NAME
typedecl DATE
datatype  REPORT = ok | already_known | not_known

record BirthdayBook = 
KNOWN :: " NAME set"
BIRTHDAY :: "(NAME * DATE) set"

locale zmathlang_birthdaybook = 
fixes known :: " NAME set"
and birthday :: "(NAME * DATE) set"
assumes "known = Domain birthday"
begin

definition InitBirthdayBook :: 
 " NAME set => (NAME * DATE) set => bool"
where 
"InitBirthdayBook known' birthday' == ((
(known' = {})))"

definition FindBirthday :: 
 "BirthdayBook => BirthdayBook => NAME => DATE => bool"
where 
"FindBirthday birthdaybook birthdaybook' name date == ((
(name \<in> known)))
\<and> (
((name, date) \<in> birthday ))"

definition NotKnown :: 
 "BirthdayBook => BirthdayBook => NAME => REPORT => bool"
where 
"NotKnown birthdaybook birthdaybook' name result == ((
(name \<notin> known)))
\<and> ((
(result = not_known)))"

definition AlreadyKnown :: 
 "BirthdayBook => BirthdayBook => NAME => REPORT => bool"
where 
"AlreadyKnown birthdaybook birthdaybook' name result == ((
(name \<in> known)))
\<and> ((
(result = already_known)))"

definition AddBirthday :: 
"BirthdayBook => BirthdayBook =>  NAME set => (NAME * DATE) set => NAME => DATE => bool"
where 
"AddBirthday birthdaybook birthdaybook' known' birthday' name date ==
 ((
(name \<notin> known)))
\<and> ((
(birthday' = birthday \<union> {(name, date)})))"

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
 "BirthdayBook => BirthdayBook =>  NAME set => (NAME * DATE) set => NAME => DATE => REPORT => bool"
where 
"RAddBirthday birthdaybook birthdaybook' known' birthday' name date result = (
((AddBirthday birthdaybook birthdaybook' known' birthday' name date) &
 (Success result))  |
 (AlreadyKnown birthdaybook birthdaybook' name result) ) "
 


end
end
