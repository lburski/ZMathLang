theory 5
imports 
Main

begin 

typedecl PERSON
typedecl TITLE
datatype MESSAGE = success | notMember | notInStock | allCopiesOut  |
 alreadyRented | nonPosStockLevel | tooManyRented | stillRented


record VideoShop = 
MEMBERS :: " PERSON set"
RENTED :: "(PERSON * TITLE) set"
STOCKLEVEL :: "(TITLE \<rightharpoonup> nat)"

locale zml_videoshop = 
fixes members :: " PERSON set"
and rented :: "(PERSON * TITLE) set"
and stockLevel :: "(TITLE \<rightharpoonup> nat)"
assumes "Domain rented \<subseteq> members" 
 and "Range rented \<subseteq> dom stockLevel" 
 and "(\<forall>t \<in> Range rented. card ({p. (p, t) \<in> rented}) < (the (stockLevel t)))"
begin

definition StillRented :: 
 "VideoShop => VideoShop => TITLE => MESSAGE  => bool"
where 
"StillRented videoshop videoshop' t outcome == (
(t \<in> Range rented)
\<and>
(outcome = stillRented))"

definition TooManyRented :: 
 "VideoShop => VideoShop => TITLE => nat  \<Rightarrow> MESSAGE => bool"
where 
"TooManyRented videoshop videoshop' t change  outcome == ((
(((the (stockLevel t)) + change) < card ({p. (p, t) \<in> rented})) \<and>
(outcome = tooManyRented)))"

definition NonPosStockLevel :: 
 "VideoShop => VideoShop => TITLE => nat  => MESSAGE => bool"
where 
"NonPosStockLevel videoshop videoshop' t change outcome == ((
((the (stockLevel t)) + change \<le> 0)
\<and> (outcome = nonPosStockLevel)
))"

definition TitlesOut :: 
 "VideoShop => VideoShop => PERSON =>  TITLE set => bool"
where 
"TitlesOut videoshop videoshop' p titles == (
(p \<in> members)
(*\<and> 
(titles = rented \<lparr> {(p)} \<rparr>)*)
)"

definition CopiesInShop :: 
 "VideoShop => VideoShop => nat => TITLE => nat  => bool"
where 
"CopiesInShop videoshop' videoshop copiesIn t copiesOut == ((
(t \<in> dom stockLevel)
\<and> (copiesIn = (the (stockLevel t)) - copiesOut)
))"

definition CopiesRentedOut :: 
 "VideoShop => VideoShop => TITLE => nat => nat => bool"
where 
"CopiesRentedOut videoshop videoshop' t copiesOut copiesIn == ((
(t \<in> dom stockLevel)
\<and> (copiesOut = card ({p. (p, t) \<in> rented}))
))"

definition NotInStock :: 
 "VideoShop => VideoShop => TITLE => MESSAGE => bool"
where 
"NotInStock videoshop videoshop' t outcome == ((
(t \<notin> dom stockLevel)))
\<and> ((
(outcome = notInStock)))"

definition NotMember :: 
 "VideoShop => VideoShop => PERSON => MESSAGE => bool"
where 
"NotMember videoshop videoshop' p outcome == ((
(p \<notin> members)))
\<and> ((
(outcome = notMember)))"

definition AlreadyRented :: 
 "VideoShop => VideoShop => PERSON => TITLE => MESSAGE => bool"
where 
"AlreadyRented videoshop videoshop' p t outcome == (
((p,t) \<in> rented)
\<and> (outcome = alreadyRented)
)"

definition AllCopiesOut :: 
 "VideoShop => VideoShop => TITLE => MESSAGE  \<Rightarrow> bool"
where 
"AllCopiesOut videoshop videoshop' t outcome == ((
(the (stockLevel t) = card ({p. (p, t) \<in> rented}))
\<and>
(outcome = allCopiesOut)
))"

definition InitVideoShop :: 
 " PERSON set => (PERSON * TITLE) set => (TITLE \<rightharpoonup> nat)  => bool"
where 
"InitVideoShop members' rented' stockLevel' == (
(members' = {})
)"

definition SuccessMessage ::
"MESSAGE \<Rightarrow> bool"
where
"SuccessMessage outcome == ((
(outcome = success)
))"

definition RentVideo :: 
"VideoShop => VideoShop =>  PERSON set => (PERSON * TITLE) set => (TITLE \<rightharpoonup> nat) => PERSON => TITLE => bool"
where 
"RentVideo videoshop videoshop' members' rented' stockLevel' p t ==
 ((
(p \<in> members)
\<and> (t \<in> dom stockLevel)
\<and> (the (stockLevel t) > card ({p. (p, t) \<in> rented}))
\<and>((p,t) \<notin> rented)
\<and>(rented' = (rented \<union> {(p,t)}))
\<and>(stockLevel' = stockLevel)
\<and>(members' = members)
))"

definition DeleteTitle :: 
"VideoShop => VideoShop =>  PERSON set => (PERSON * TITLE) set => (TITLE \<rightharpoonup> nat) => TITLE => bool"
where 
"DeleteTitle videoshop videoshop' members' rented' stockLevel' t ==
 (
(t \<notin> Range rented) 
\<and> (t \<in> dom stockLevel)
(*({p. (p, t) \<in> rented})*)
(*stockLevel' = {t} \<unlhd> stockLevel*)
\<and>
(members' = members)
\<and>
(rented' = rented)
)
"

definition ChangeStockLevel :: 
"VideoShop => VideoShop =>  PERSON set => (PERSON * TITLE) set => (TITLE * nat) set => TITLE => nat  => bool"
where 
"ChangeStockLevel videoshop videoshop' members' rented' stockLevel' t change ==
 ((
(t \<in> dom stockLevel) 
\<and> (the (stockLevel t) + change > 0)
\<and> (the (stockLevel t) + change \<ge> card ({p. (p, t) \<in> rented}))
(*\<and> stockLevel' = stockLevl \<oplus> {(t, (the (stockLevel t) + change))}*)
\<and> (rented' = rented)
\<and>(members' = members)
))"

lemma TotalRentVideo: 
"((RentVideo videoshop videoshop' members' rented' stockLevel' p t)
\<and> (SuccessMessage outcome))
\<or> (NotMember videoshop videoshop' p outcome)
\<or> (NotInStock videoshop videoshop' t outcome)
\<or> (AllCopiesOut videoshop videoshop' t outcome)
\<or> (AlreadyRented videoshop videoshop' p t outcome)"
sorry

lemma TotalChangeStockLevel:
"((ChangeStockLevel videoshop videoshop' members' rented' stockLevel' t change)
\<and> SuccessMessage outcome)
\<or> (NonPosStockLevel videoshop videoshop' t change outcome)
\<or> (TooManyRented videoshop videoshop' t change  outcome)"
sorry

lemma TotalDeleteTitle:
"((DeleteTitle videoshop videoshop' members' rented' stockLevel' t)
\<and> SuccessMessage outcome)
\<or> (NotInStock videoshop videoshop' t outcome)
\<or> (StillRented videoshop videoshop' t outcome)"
sorry

lemma TotalTitlesOut:
"((TitlesOut videoshop videoshop' p titles)
\<and> SuccessMessage outcome)
\<or> (NotMember videoshop videoshop' p outcome)"
sorry

lemma TotalCopiesRentedOut:
"((CopiesRentedOut videoshop videoshop' t copiesOut copiesIn)
\<and> SuccessMessage outcome)
\<or> (NotInStock videoshop videoshop' t outcome)"
sorry

lemma TotalCopiesInShop:
"((CopiesInShop videoshop' videoshop copiesIn t copiesOut)
\<and> SuccessMessage outcome)
\<or> (NotInStock videoshop videoshop' t outcome)"
sorry


end
end
