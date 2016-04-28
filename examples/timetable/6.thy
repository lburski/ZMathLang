theory timetable
imports 
Main 

begin 

typedecl STUDENT
typedecl TIMESLOT
typedecl ROOM
typedecl MODULE

(*primrec allPairs:: "'a list list \<Rightarrow> 'a list" where
"concat [] = []" |
"concat (x # xs) = x @ concat xs"*)

record Timetable = 
STUDENTTT :: "(STUDENT * (TIMESLOT * ROOM) set) set"
MODULETT :: "(MODULE * (TIMESLOT * ROOM) set) set"

locale zml_timetable = 
fixes studentTT :: "(STUDENT * (TIMESLOT * ROOM) set) set"
and moduleTT :: "(MODULE * (TIMESLOT * ROOM) set) set"
assumes "\<forall>r s :: (TIMESLOT * ROOM) set.
 True
(*\<and> disjoint(r, s)*)"
and "(\<forall>s m. (s \<in> Domain studentTT) \<and> (m \<in> Domain moduleTT)
\<longleftrightarrow> ((\<exists>Str Mtr. ((s, Str) \<in> studentTT) \<and> ((m, Mtr) \<in> moduleTT) 
\<and> ((Str \<inter> Mtr) \<noteq> {})
\<longrightarrow> ((Domain (Str \<inter> Mtr)) = (Domain Mtr))
)))"

begin

(*\<and> (\<exists> newPairs:: (TIMESLOT * ROOM) set. 
(Domain newPairs = Domain Mtr)
\<and> (newPairs \<subseteq> Mtr)
\<and> studentTT' = studentTT \<oplus> {(s, Str) \<union> newPairs})*)

definition InitTimetable :: 
 "Timetable \<Rightarrow> Timetable \<Rightarrow> (STUDENT * (TIMESLOT * ROOM)) set \<Rightarrow> (MODULE * (TIMESLOT * ROOM)) set => bool"
where 
"InitTimetable timetable timetable' studentTT' moduleTT' == ((
(studentTT' = {}) 
\<and> (moduleTT' =  {})))"

definition RegForModule :: 
"Timetable => Timetable => (STUDENT * (TIMESLOT * ROOM) set) set => (MODULE * (TIMESLOT * ROOM) set) set => STUDENT => MODULE => (TIMESLOT * ROOM) set \<Rightarrow> (TIMESLOT * ROOM) set => bool"
where 
"RegForModule timetable timetable' studentTT' moduleTT' s m Mtr Str ==
(
(s \<in> Domain studentTT)
\<and> (m \<in> Domain moduleTT)
\<and> ((m,Mtr) \<in> moduleTT)
\<and> (Mtr \<noteq> {})
\<and> ((s, Str) \<in> studentTT)
\<and> (((Domain Str) \<inter> (Domain Mtr)) \<noteq> {})
\<and> (\<exists> newPairs:: (TIMESLOT * ROOM) set. 
(Domain newPairs = Domain Mtr)
\<and> (newPairs \<subseteq> Mtr)
(*\<and> studentTT' = studentTT \<oplus> {(s, Str) \<union> newPairs})*)
)
\<and> (moduleTT' = moduleTT)
)"

definition AddStudent :: 
"Timetable => Timetable => (STUDENT * (TIMESLOT * ROOM) set) set => (MODULE * (TIMESLOT * ROOM) set) set \<Rightarrow> STUDENT => bool"
where 
"AddStudent timetable timetable' studentTT' moduleTT' s ==
 ((
(s \<notin> Domain studentTT)))
\<and> ((
(studentTT' = studentTT \<union> {(s, {})}) 
\<and> (moduleTT' = moduleTT)))"

definition DescheduleModule :: 
"Timetable => Timetable => (STUDENT * (TIMESLOT * ROOM) set) set => (MODULE * (TIMESLOT * ROOM) set) set => MODULE => (TIMESLOT * ROOM) set \<Rightarrow> (TIMESLOT * ROOM) set \<Rightarrow> bool"
where 
"DescheduleModule timetable timetable' studentTT' moduleTT' m Mtr Str ==
(
(m \<in> Domain moduleTT)
\<and> ((m, Mtr) \<in> moduleTT)
\<and> (Mtr \<noteq> {})
(*\<and> moduleTT' = moduleTT \<oplus> {(m, {})}*)
(*studentTT' = \<Union>{s \<in> Domain studentTT \<and> (s, Str) \<in> studentTT
\<and> {(s, (Str-Mtr))}*)
)"

definition ScheduleModule :: 
"Timetable => Timetable => (STUDENT * (TIMESLOT * ROOM) set) set => (MODULE * (TIMESLOT * ROOM) set) set => MODULE => (TIMESLOT * ROOM) set => bool"
where 
"ScheduleModule timetable timetable' studentTT' moduleTT' m Mtr ==
(m \<in> Domain moduleTT)
\<and> ((m, Mtr) \<in> moduleTT)
\<and> (Mtr = {})
\<and> (\<exists> schedule:: (TIMESLOT * ROOM) set.
True
(*\<and> (allPairs moduleTT \<inter> schedule = {})*)
(*\<and> (moduleTT' = moduleTT \<oplus> {(m, schedule)})*)
)
\<and> (studentTT' = studentTT)
"

end
end