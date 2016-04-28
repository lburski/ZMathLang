theory 6
imports Main 

begin 

typedecl STUDENT

record ClubState = 
MAXPLAYERS :: nat
BADMINTON :: " STUDENT set"
HALL :: " STUDENT set"
ONCOURT :: " STUDENT set"
WAITING :: " STUDENT list"

locale zml_clubstate2 = 
fixes maxPlayers :: "nat"
and badminton :: " STUDENT set"
and hall :: " STUDENT set"
and onCourt :: " STUDENT set"
and waiting :: " STUDENT list"
assumes "maxPlayers = 20" 
 and "hall \<subseteq> badminton" 
 and "card hall \<le> maxPlayers" 
(* and "[(sorted_list_of_set onCourt), ran waiting] partition hall"*)
begin

definition InitClubState2 :: 
 " STUDENT set =>  STUDENT set =>  STUDENT set => bool"
where 
"InitClubState2 badminton' hall' onCourt' == ((
(badminton' = {})))"

definition NewGame :: 
 " STUDENT set =>  STUDENT set =>  STUDENT set=> STUDENT set  => bool"
where 
"NewGame badminton' hall' onCourt' waiting' ==
onCourt = {}
\<and> (length waiting \<ge> 2)
\<and> ((length waiting \<ge> 4) \<longrightarrow> (card onCourt' = 4))
\<and> ((length waiting) < 4 \<longrightarrow> ((card onCourt' = 2) \<or> (card onCourt' = 3)))
\<and> (hd waiting \<in> onCourt')
\<and> (onCourt' \<subseteq> (set waiting))
(*\<and> (waiting' = waiting \<restriction> ((Range waiting) - onCourt'))*)
\<and> (hall' = hall)
\<and> (badminton' = badminton)"

definition LeaveHall :: 
"ClubState => ClubState =>  STUDENT list \<Rightarrow> STUDENT set =>  STUDENT set =>  STUDENT set => STUDENT => bool"
where 
"LeaveHall clubstate2 clubstate2' waiting' badminton' hall' onCourt' p ==
(p \<in> set waiting)
(* \<and> (waiting' = squash(waiting \<unlhd> {(p)})) *)
\<and> (hall' = hall - {(p)}) 
\<and> (badminton' = badminton)"

definition FinishGame :: 
"ClubState => ClubState =>  STUDENT set =>  STUDENT set =>  STUDENT set =>  STUDENT list => bool"
where 
"FinishGame clubstate2 clubstate2' badminton' hall' onCourt' waiting' ==
(onCourt \<noteq> {})
\<and> (onCourt' = {})
\<and> (\<exists>s::STUDENT list. (set s=onCourt') \<and> (waiting' =  concat [s]))
\<and> (hall' = hall) 
\<and> (badminton' = badminton)"

lemma pre_FinishGame:
"(\<exists> clubstate2 clubstate2' badminton' hall' onCourt' waiting'.
FinishGame clubstate2 clubstate2' badminton' hall' onCourt' waiting')
\<longleftrightarrow> (onCourt \<noteq> {})"
apply (unfold FinishGame_def)
apply auto
done

lemma pre_NewGame:
"(\<exists> badminton' hall'.
NewGame badminton' hall' onCourt' waiting')
\<longleftrightarrow> 
onCourt = {}
\<and> (length waiting \<ge> 2)
\<and> ((length waiting \<ge> 4) \<longrightarrow> (card onCourt' = 4))
\<and> ((length waiting) < 4 \<longrightarrow> ((card onCourt' = 2) \<or> (card onCourt' = 3)))
\<and> (hd waiting \<in> onCourt')
\<and> (onCourt' \<subseteq> (set waiting))"
apply (unfold NewGame_def)
apply auto
done

lemma pre_LeaveHall:
"(\<exists> clubstate2 clubstate2' waiting' badminton' hall' onCourt'.
LeaveHall clubstate2 clubstate2' waiting' badminton' hall' onCourt' p)
\<longleftrightarrow> (p \<in> set waiting)"
apply (unfold LeaveHall_def)
apply auto
done

end
end
