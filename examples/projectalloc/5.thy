\begin{verbatim}
theory projectalloc
imports 
Main 

begin 

typedecl PERSON
typedecl TOPIC
datatype MESSAGE = success | isStudent |
 isLecturer | notStudent | isAllocated  |
 noLecAvailable | notAllocated |
 notLecturer | notListedTopic



record ProjectAlloc = 
STUDINTERESTS ::  "(PERSON \<times> (nat \<times> TOPIC) set) set"
LECINTERESTS ::  "(PERSON \<times> (nat \<times> TOPIC) set) set"
ALLOCATION :: "(PERSON * PERSON) set"
MAXPLACES :: "(PERSON * nat) set"

locale zml_projectalloc = 
fixes studInterests :: "(PERSON \<times> (nat \<times> TOPIC) set) set"
and lecInterests :: "(PERSON \<times> (nat \<times> TOPIC) set) set"
and allocation :: "(PERSON * PERSON) set"
and maxPlaces :: "(PERSON * nat) set"
assumes
"Domain studInterests \<inter> Domain lecInterests = {}"
and "Domain allocation \<subseteq> Domain studInterests"
and "Range allocation \<subseteq> Domain lecInterests"
and "Domain maxPlaces = Domain lecInterests"
and "(\<forall> lec. (lec \<in> Domain maxPlaces) \<longrightarrow> 
card (allocation \<rhd> {lec}) \<le> maxPlaces lec)
)"

begin

definition SupsDiffer :: 
 "ProjectAlloc => ProjectAlloc => (PERSON * TOPIC) set  => (PERSON * TOPIC) set => (PERSON * PERSON) set => (PERSON * nat) set => PERSON => bool"
where 
"SupsDiffer projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s == ((
(
\<exists> old new. ((old \<in> Domain lecInterests) \<and>
 (new \<in> Domain lecInterests))
\<longrightarrow>
((s, old) \<in> allocation)
\<and> ((s, new) \<in> allocation')
\<and> (old \<noteq> new))
))"

definition LecsAvailable :: 
 "ProjectAlloc => ProjectAlloc => TOPIC => PERSON set \<Rightarrow> bool"
where 
"LecsAvailable projectalloc projectalloc' t ps == ((
\<and> (ps = {p \<in> Domain lecInterests. t \<in> Range (lecInterets p)
\<and> macPlaces p > Card (allocation \<rhd> {p})}})
))"

definition NotListedTopic :: 
 "ProjectAlloc => ProjectAlloc => PERSON \<Rightarrow> TOPIC \<Rightarrow> MESSAGE \<Rightarrow> (nat \<times> TOPIC) set \<Rightarrow> bool"
where 
"NotListedTopic projectalloc projectalloc' l t outcome nt == ((
((l, nt) \<in> lecInterests)
\<and> (t \<notin> Range nt)
\<and> (outcome = notListedTopic)
))"

definition NotLecturer :: 
 "ProjectAlloc => ProjectAlloc => PERSON => MESSAGE => bool"
where 
"NotLecturer projectalloc projectalloc' l outcome == ((
(l \<notin>  Domain lecInterests)
\<and> ((
(outcome = notLecturer)))))"

definition NotAllocated :: 
 "ProjectAlloc => ProjectAlloc => PERSON => MESSAGE => bool"
where 
"NotAllocated  projectalloc projectalloc' s outcome == ((
(s \<notin> Domain allocation)))
\<and> ((
(outcome = notAllocated )))"


definition IsStudent :: 
 "ProjectAlloc => ProjectAlloc => PERSON => MESSAGE => bool"
where 
"IsStudent projectalloc projectalloc' s outcome == ((
(s \<in> Domain studInterests)))
\<and> (outcome = isStudent)"

definition SuccessMessage :: 
"MESSAGE => bool"
where 
"SuccessMessage outcome == (outcome = success)"

definition NotStudent :: 
 "ProjectAlloc => ProjectAlloc => PERSON => MESSAGE => bool"
where 
"NotStudent projectalloc projectalloc' s outcome == ((
(s \<notin> Domain studInterests)))
\<and> ((
(outcome = notStudent)))"

definition IsLecturer :: 
 "ProjectAlloc => ProjectAlloc => PERSON => MESSAGE => bool"
where 
"IsLecturer projectalloc projectalloc' s outcome == ((
(s \<in> Domain lecInterests)))
\<and> ((
(outcome = isLecturer)))"

definition NoLecAvailable :: 
 "ProjectAlloc => ProjectAlloc => PERSON => MESSAGE => nat \<Rightarrow> (nat * TOPIC) set \<Rightarrow> (nat * TOPIC) set \<Rightarrow> bool"
where 
"NoLecAvailable projectalloc projectalloc' s outcome m studentInterestS lecInterestsSup == ((
\<not>(\<exists>sup. (sup \<in> Domain lecInterests)
\<longrightarrow> ( ((sup,m) \<in> maxPlaces)
\<and> m > (card (allocation \<rhd> {sup}))
\<and> (((s,studentInterestS ) \<in> studInterests) \<and> ((sup, lecInterestsSup) \<in> lecInterests))
\<and> ((Range studentInterestS) \<inter> Range lecInterestsSup) \<noteq> {})
)
\<and> (outcome = noLecAvailable)
))"

definition IsAllocated :: 
 "ProjectAlloc => ProjectAlloc => PERSON => MESSAGE => bool"
where 
"IsAllocated projectalloc projectalloc' s outcome == ((
(s \<notin> Domain allocation)))
\<and> ((
(outcome = isAllocated)))"

definition InitProjectAlloc :: 
 "ProjectAlloc \<Rightarrow> ProjectAlloc \<Rightarrow> (PERSON \<times> (nat \<times> TOPIC) set) set \<Rightarrow> (PERSON \<times> (nat \<times> TOPIC) set) set \<Rightarrow> bool"
where 
"InitProjectAlloc projectAlloc projectAlloc' lecInterests' studInterests' == ((
(lecInterests' = {})
\<and> (studInterests' = {})
))"

definition RemoveLecsTopic :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<times> (nat \<times> TOPIC) set) set => (PERSON \<times> (nat \<times> TOPIC) set) set => (PERSON * PERSON) set => (PERSON * nat) set => PERSON => TOPIC \<Rightarrow> (nat \<times> TOPIC) set  => bool"
where 
"RemoveLecsTopic projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' l t nt ==
 ((
(l \<in> Domain lecInterests)
\<and> (nt \<in> Range lecInterests)
\<and> (t \<in> Range nt)
\<and> (lecInterests' = lecInterests \<oplus> {(l, (squash(nt \<unrhd> {t}))}))
\<and> (maxPlaces'=  maxPlaces)
\<and> (studInterests' = studInterests)
\<and> (allocation' = allocation)
 ))"

definition DeAllocate :: 
 "ProjectAlloc => ProjectAlloc => (PERSON \<times> (nat \<times> TOPIC) set) set => (PERSON \<times> (nat \<times> TOPIC) set) set => (PERSON * PERSON) set => (PERSON * nat) set => PERSON => bool"
where 
"DeAllocate projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s == ((

(\<exists> sup \<in> Domain lecInterests.
((s, sup) \<in> allocation) \<and>
(allocation' = allocation - {(s, sup)}))
\<and> (studInterests' = studInterests)
\<and> (lecInterests' = lecInterests)
))"

definition AddStudent :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<times> (nat \<times> TOPIC) set) set => (PERSON \<times> (nat \<times> TOPIC) set) set => (PERSON * PERSON) set => (PERSON * nat) set => PERSON =>  (nat \<times> TOPIC) set => bool"
where 
"AddStudent projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s ts ==
((
(s \<notin> ((Domain studInterests) \<union> (Domain lecInterests)))
\<and> (studInterests' = studInterests \<union> {(s, ts)})
\<and> (lecInterests' = lecInterests)
\<and> (allocation' = allocation)
\<and> (maxPlaces' = maxPlaces)
))"

definition Allocate :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<times> (nat \<times> TOPIC) set) set => (PERSON \<times> (nat \<times> TOPIC) set) set => (PERSON * PERSON) set => (PERSON * nat) set => PERSON => bool"
where 
"Allocate projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s ==
((
(s \<in> Domain studInterests)
\<and> (s \<notin> Domain allocation)

\<and> ( \<exists> sup \<in> Domain lecInterests. \<exists>t:: TOPIC. \<exists>i j:: nat. True)

\<and> (studInterests' = studInterests)
\<and> (lecInterests' = lecInterests)
))"

definition AddLecturer :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<times> (nat \<times> TOPIC) set) set => (PERSON \<times> (nat \<times> TOPIC) set) set => (PERSON * PERSON) set => (PERSON * nat) set => PERSON =>  (nat * TOPIC) set => nat => bool"
where 
"AddLecturer projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' l ts maxAlloc ==
 ((
(l \<notin> Domain studInterests \<union> Domain lecInterests)))
\<and> ((
(lecInterests' = lecInterests \<union> {(l, ts)}) 
\<and> (maxPlaces' = maxPlaces \<union> {(l, maxAlloc)}) 
\<and> (studInterests' = studInterests) 
\<and> (allocation' = allocation)))"

lemma TotalAddStudent:
"((AddStudent projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s ts)
 \<and> (SuccessMessage outcome))
\<or> (IsStudent projectalloc projectalloc' s outcome)
\<or> (IsLecturer projectalloc projectalloc' s outcome)"
sorry

lemma TotalAddLecturer:
"((AddLecturer projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' l ts maxAlloc)
 \<and> (SuccessMessage outcome))
\<or> (IsStudent projectalloc projectalloc' s outcome)
\<or> (IsLecturer projectalloc projectalloc' s outcome)"
sorry

lemma TotalAllocate:
"((Allocate projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s) \<and>
 (SuccessMessage outcome))
\<or> (NotStudent projectalloc projectalloc' s outcome)
\<or> (IsAllocated projectalloc projectalloc' s outcome)
\<or> (NoLecAvailable projectalloc projectalloc' s outcome m studentInterestS lecInterestsSup)"
sorry

lemma TotalDeAllocte:
"((DeAllocate projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s)
\<and> (SuccessMessage outcome))
\<or> (NotAllocated  projectalloc projectalloc' s outcome)"
sorry

lemma TotalRemoveLecsTopic:
"((RemoveLecsTopic projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' l t nt) \<and> (SuccessMessage outcome))
\<or> (NotLecturer projectalloc projectalloc' l outcome)
\<or> (NotListedTopic projectalloc projectalloc' l t outcome nt)"
sorry

end
end

\end{verbatim}