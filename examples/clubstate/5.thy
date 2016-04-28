theory 5

imports 
Main 

begin 

typedecl STUDENT
datatype MESSAGE = success| isMember | notMember
 | hallFull | inHall | notInHall

record ClubState = 
MAXPLAYERS :: nat
BADMINTON :: " STUDENT set"
HALL :: " STUDENT set"

locale zml_clubstate = 
fixes maxPlayers :: "nat"
and badminton :: " STUDENT set"
and hall :: " STUDENT set"
assumes "maxPlayers = 20" 
 and "hall \<subseteq> badminton" 
 and "card hall \<le> maxPlayers"
 and  "hall' \<noteq> hall"
 and  "badminton' \<noteq> badminton"
begin

definition InitClubState :: 
 " STUDENT set =>  STUDENT set => bool"
where 
"InitClubState badminton' hall' == ((
(badminton' = {}) 
\<and> (hall' = {})))"

definition LeaveHall :: 
"ClubState => ClubState =>  STUDENT set =>  
STUDENT set => STUDENT => bool"
where 
"LeaveHall clubstate clubstate' badminton' hall'
 leaver ==
 ((
(leaver \<in> hall)))
\<and> ((
(hall' = hall - {(leaver)}) 
\<and> (badminton' = badminton)))"

definition AddMember :: 
"ClubState => ClubState =>  STUDENT set =>  
STUDENT set => STUDENT => bool"
where 
"AddMember clubstate clubstate' badminton' 
hall' newMember ==
 ((
(newMember \<notin> badminton)))
\<and> ((
(badminton' = badminton \<union> {(newMember)}) 
\<and> (hall' = hall)))"

definition EnterHall :: 
"ClubState => ClubState =>  STUDENT set =>  
STUDENT set => STUDENT => bool"
where 
"EnterHall clubstate clubstate' badminton' hall'
 enterer ==
 ((
(enterer \<in> badminton) 
\<and> (enterer \<notin> hall) 
\<and> (card hall < maxPlayers)))
\<and> ((
(hall' = hall \<union> {(enterer)}) 
\<and> (badminton' = badminton)))"

definition RemoveMember :: 
"ClubState => ClubState =>  STUDENT set =>  
STUDENT set => STUDENT => bool"
where 
"RemoveMember clubstate clubstate' badminton' 
hall' member ==
 ((
(member \<in> badminton)))
\<and> ((
(badminton' = badminton - {(member)}) 
\<and> (hall' = hall - {(member)})))"

definition IsMember :: 
 "ClubState => ClubState => STUDENT => MESSAGE => bool"
where 
"IsMember clubstate clubstate' newMember outcome == ((
(newMember \<in> badminton)))
\<and> ((
(outcome = isMember)))"

definition AlreadyInHall :: 
 "ClubState => ClubState => STUDENT => MESSAGE => bool"
where 
"AlreadyInHall clubstate clubstate' enterer outcome == ((
(enterer \<in> hall)))
\<and> ((
(outcome = inHall)))"

definition NotMember :: 
 "ClubState => ClubState => STUDENT => MESSAGE => bool"
where 
"NotMember clubstate clubstate' member outcome == ((
(member \<notin> badminton)))
\<and> ((
(outcome = notMember)))"

definition NotInHall :: 
 "ClubState => ClubState => STUDENT => MESSAGE => bool"
where 
"NotInHall clubstate clubstate' leaver outcome == ((
(leaver \<notin> hall)))
\<and> ((
(outcome = notInHall)))"

definition SuccessMessage :: 
 "MESSAGE => bool"
where 
"SuccessMessage outcome == ((
(outcome = success)))"

lemma pre_leaveHall: 
"(\<exists> clubstate clubstate' badminton' hall'.
 LeaveHall clubstate clubstate' badminton' hall' leaver)
 \<longleftrightarrow> (leaver \<in> hall)"
sorry
 
 lemma pre_notInHall:
 "(\<exists> clubstate clubstate'  outcome.
 NotInHall clubstate clubstate' leaver outcome)
 \<longleftrightarrow> (leaver \<notin> hall)"
sorry

lemma TotalLeaveHall: 
"((LeaveHall clubstate clubstate' badminton' hall' leaver \<and>
 SuccessMessage outcome)) \<or>
 NotInHall clubstate clubstate' leaver outcome"
sorry

lemma TotalRemoveMember: 
"(RemoveMember clubstate clubstate' badminton' hall' member \<and>
 SuccessMessage outcome) \<or>
 NotMember clubstate clubstate' member outcome"
sorry

lemma TotalAddMember: 
"(AddMember clubstate clubstate' badminton' hall' newMember \<and>
 SuccessMessage outcome) \<or>
 IsMember clubstate clubstate' newMember outcome"
sorry

definition HallFull :: 
 "ClubState => ClubState => MESSAGE => bool"
where 
"HallFull clubstate clubstate' outcome == ((
(card hall = maxPlayers)))
\<and> ((
(outcome = hallFull)))"

lemma TotalEnterHall: 
"(EnterHall clubstate clubstate' badminton' hall' enterer \<and>
 SuccessMessage outcome) \<or>
 NotMember clubstate clubstate' member outcome \<or>
 AlreadyInHall clubstate clubstate' enterer outcome \<or>
 HallFull clubstate clubstate' outcome"
sorry

end
end