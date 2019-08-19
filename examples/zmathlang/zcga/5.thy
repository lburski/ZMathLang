theory 5
imports 
Main 

begin 
typedecl LINES
typedecl DECLARATION 
typedecl EXPRESSION 
typedecl DEFINITION
typedecl VARS


record ZcgaState = 
Declarations :: "(VARS * EXPRESSION) set"
Expressions :: "(LINES set)"
Definitions :: "(LINES set)"
DefinedConstants :: "(VARS set)"
TERMDECLARATION :: "(VARS * EXPRESSION) set"
SETDECLARATION :: "(VARS * EXPRESSION) set"
TERMS :: "(VARS set)"
SETS :: "(VARS set)"
DVAR :: "(VARS set)"


locale ZCGa = 
fixes declarations :: "(VARS * EXPRESSION) set"
and expressions :: "(LINES set)"
and definitions :: "(LINES set)"
and definedConstants :: "(VARS set)"
and TermDeclaration :: "(VARS * EXPRESSION) set"
and SetDeclaration :: "(VARS * EXPRESSION) set"
and terms :: "(VARS set)"
and sets :: "(VARS set)"
and dvar :: "(VARS set)"
 
assumes
" TermDeclaration \<subseteq> declarations"
and "SetDeclaration \<subseteq> declarations"
and "dvars \<subset> sets \<union> terms"
and "sets \<inter> terms = {}"
begin

definition InitZcgaState :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (LINES set)\<Rightarrow> (LINES set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> bool"
where 
"InitZcgaState zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' == (declarations' = {}) 
\<and> (expressions' = {}) 
\<and> (definitions' = {}) 
\<and> (definedConstants' = {}) 
\<and> (TermDeclaration' = {}) 
\<and> (SetDeclaration' = {}) 
\<and> (terms' = {}) 
\<and> (sets' = {}) 
\<and> (dvar' = {})"

definition CorrectExpression :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (LINES set)\<Rightarrow> (LINES set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> LINES \<Rightarrow> 
(VARS set) \<Rightarrow> ((VARS set) \<rightharpoonup> LINES) \<Rightarrow>  bool"
where 
"CorrectExpression zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar'
 newExpression expressParameters expressConstant ==
 (expressParameters \<subseteq> sets \<union> terms) 
\<and> (expressParameters \<noteq> {})
\<and> (newExpression = the (expressConstant expressParameters))
\<and> (expressions' = expressions \<union> {newExpression})"

definition CorrectConstantSet :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (LINES set)\<Rightarrow> (LINES set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> VARS \<Rightarrow>
(VARS set) \<Rightarrow> ((VARS set) \<rightharpoonup> VARS) \<Rightarrow>  bool"
where 
"CorrectConstantSet zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' newset setParameters setConstant ==
(setParameters \<subseteq> sets \<union> terms)
\<and> (setParameters \<noteq> {})
\<and> (newset = the (setConstant setParameters))
\<and> (sets' = sets \<union> {newset})"

definition CorrectDefinitions :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (LINES set)\<Rightarrow> (LINES set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> 
(VARS set) \<Rightarrow> VARS \<Rightarrow> ((VARS set) \<rightharpoonup> VARS) => ((VARS set) \<rightharpoonup> LINES) \<Rightarrow> bool"
where 
"CorrectDefinitions zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' parameters newConstant definedSet newdefinition ==
 (newConstant \<notin> sets)
\<and> (parameters \<subseteq> sets \<union> terms)
\<and> (newConstant = the (definedSet parameters)) 
\<and> (definedConstants' = definedConstants \<union> {(newConstant)})
\<and> (sets' = sets \<union> {newConstant})
\<and> (definitions' = definitions \<union> {the (newdefinition parameters)})"

definition CorrectTermDeclaration :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (LINES set)\<Rightarrow> (LINES set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> 
EXPRESSION \<Rightarrow> VARS \<Rightarrow> bool"
where 
"CorrectTermDeclaration zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' dvarExpression var ==
 (var \<notin> dvar)
\<and> (TermDeclaration' = TermDeclaration \<union> {(var, dvarExpression)}) 
\<and> (terms' = terms \<union> {(var)}) 
\<and> (dvar' = dvar \<union> {(var)})"

definition CorrectConstantTerm :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (LINES set)\<Rightarrow> (LINES set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> 
(VARS set \<rightharpoonup> VARS) \<Rightarrow> VARS \<Rightarrow> VARS set \<Rightarrow> bool"
where 
"CorrectConstantTerm zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' constant newTerm parameters ==
 (parameters \<subseteq> sets \<union> terms) 
\<and> (parameters \<noteq> {})
\<and> (newTerm = the (constant parameters))
\<and> (terms' = terms \<union> {(newTerm)})"

definition CorrectSetDeclaration :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (EXPRESSION set)\<Rightarrow> (DEFINITION set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> 
EXPRESSION \<Rightarrow> VARS \<Rightarrow> bool"
where 
"CorrectSetDeclaration zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' dvarExpression var ==
 (var \<notin> dvar)
\<and> (SetDeclaration' = SetDeclaration \<union> {(var, dvarExpression)}) 
\<and> (sets' = sets \<union> {(var)}) 
\<and> (dvar' = dvar \<union> {(var)})"

definition CorrectSchemaText :: 
"(VARS * EXPRESSION) set \<Rightarrow> (EXPRESSION set)\<Rightarrow> (DEFINITION set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> 
(LINES set) \<Rightarrow> bool"
where 
"CorrectSchemaText declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' schemaText ==
(schemaText = {})
\<or> (schemaText = definitions \<union> expressions)"

lemma CorrectExpression_L1:
"(\<exists> zcgastate :: ZcgaState.
\<exists> zcgastate' :: ZcgaState.
\<exists> declarations':: (VARS * EXPRESSION) set.
 \<exists> expressions' :: (LINES set).
\<exists> definitions' :: (LINES set).
\<exists> definedConstants' :: (VARS set).
\<exists> TermDeclaration' :: (VARS * EXPRESSION) set.
\<exists> SetDeclaration' :: (VARS * EXPRESSION) set.
\<exists> terms' :: (VARS set).
\<exists> sets' :: (VARS set).
\<exists> dvar' :: (VARS set).
\<exists> newExpression :: LINES.
\<exists> expressParameters :: (VARS set).
\<exists> expressConstant :: ((VARS set) \<rightharpoonup> LINES).
 (expressParameters \<subseteq> sets \<union> terms) 
\<and> (expressParameters \<noteq> {})
\<and> (newExpression = the (expressConstant expressParameters))
\<and> (expressions' = expressions \<union> {newExpression})
\<longrightarrow> (TermDeclaration \<subseteq> declarations)
\<and> (SetDeclaration \<subseteq> declarations)
\<and> (dvars \<subset> sets \<union> terms)
\<and> (sets \<inter> terms = {}))"
sorry

lemma CorrectConstantSet_L2:
"(\<exists> zcgastate :: ZcgaState.
\<exists> zcgastate' :: ZcgaState.
\<exists> declarations':: (VARS * EXPRESSION) set.
 \<exists> expressions' :: (LINES set).
\<exists> definitions' :: (LINES set).
\<exists> definedConstants' :: (VARS set).
\<exists> TermDeclaration' :: (VARS * EXPRESSION) set.
\<exists> SetDeclaration' :: (VARS * EXPRESSION) set.
\<exists> terms' :: (VARS set).
\<exists> sets' :: (VARS set).
\<exists> dvar' :: (VARS set).
\<exists> newset:: VARS.
\<exists> setParameters :: (VARS set).
\<exists> setConstant :: ((VARS set) \<rightharpoonup> VARS).
(setParameters \<subseteq> sets \<union> terms)
\<and> (setParameters \<noteq> {})
\<and> (newset = the (setConstant setParameters))
\<and> (sets' = sets \<union> {newset})
\<longrightarrow> (TermDeclaration \<subseteq> declarations)
\<and> (SetDeclaration \<subseteq> declarations)
\<and> (dvars \<subset> sets \<union> terms)
\<and> (sets \<inter> terms = {}))"
sorry

lemma CorrectDefinitions_L3:
"(\<exists> zcgastate :: ZcgaState.
\<exists> zcgastate' :: ZcgaState.
\<exists> declarations':: (VARS * EXPRESSION) set.
\<exists> expressions' :: (LINES set).
\<exists> definitions' :: (LINES set).
\<exists> definedConstants' :: (VARS set).
\<exists> TermDeclaration' :: (VARS * EXPRESSION) set.
\<exists> SetDeclaration' :: (VARS * EXPRESSION) set.
\<exists> terms' :: (VARS set).
\<exists> sets' :: (VARS set).
\<exists> dvar' :: (VARS set).
\<exists> parameters :: (VARS set).
\<exists> newConstant :: VARS.
\<exists> definedSet :: (VARS set \<rightharpoonup> VARS).
\<exists> newdefinition :: (VARS set \<rightharpoonup> LINES).
 (newConstant \<notin> sets)
\<and> (parameters \<subseteq> sets \<union> terms)
\<and> (newConstant = the (definedSet parameters)) 
\<and> (definedConstants' = definedConstants \<union> {(newConstant)})
\<and> (sets' = sets \<union> {newConstant})
\<and> (definitions' = definitions \<union> {the (newdefinition parameters)})
\<longrightarrow> (TermDeclaration \<subseteq> declarations)
\<and> (SetDeclaration \<subseteq> declarations)
\<and> (dvars \<subset> sets \<union> terms)
\<and> (sets \<inter> terms = {})
\<and> (TermDeclaration' \<subseteq> declarations')
\<and> (SetDeclaration' \<subseteq> declarations')
\<and> (dvars' \<subset> sets' \<union> terms')
\<and> (sets' \<inter> terms' = {})
\<and> (TermDeclaration' \<subseteq> declarations')
\<and> (SetDeclaration' \<subseteq> declarations')
\<and> (dvars' \<subset> sets' \<union> terms')
\<and> (sets' \<inter> terms' = {}))"
sorry

lemma CorrectTermDeclaration_L4:
"(\<exists> zcgastate :: ZcgaState.
\<exists> zcgastate' :: ZcgaState.
\<exists> declarations':: (VARS * EXPRESSION) set.
\<exists> expressions' :: (LINES set).
\<exists> definitions' :: (LINES set).
\<exists> definedConstants' :: (VARS set).
\<exists> TermDeclaration' :: (VARS * EXPRESSION) set.
\<exists> SetDeclaration' :: (VARS * EXPRESSION) set.
\<exists> terms' :: (VARS set).
\<exists> sets' :: (VARS set).
\<exists> dvar' :: (VARS set).
\<exists> dvarExpression :: EXPRESSION.
\<exists> var :: VARS.
 (var \<notin> dvar)
\<and> (TermDeclaration' = TermDeclaration \<union> {(var, dvarExpression)}) 
\<and> (terms' = terms \<union> {(var)}) 
\<and> (dvar' = dvar \<union> {(var)})
\<longrightarrow> (TermDeclaration \<subseteq> declarations)
\<and> (SetDeclaration \<subseteq> declarations)
\<and> (dvars \<subset> sets \<union> terms)
\<and> (sets \<inter> terms = {}))"
sorry

lemma CorrectConstantTerm_L5:
"(\<exists> zcgastate :: ZcgaState.
\<exists> zcgastate' :: ZcgaState.
\<exists> declarations':: (VARS * EXPRESSION) set.
\<exists> expressions' :: (LINES set).
\<exists> definitions' :: (LINES set).
\<exists> definedConstants' :: (VARS set).
\<exists> TermDeclaration' :: (VARS * EXPRESSION) set.
\<exists> SetDeclaration' :: (VARS * EXPRESSION) set.
\<exists> terms' :: (VARS set).
\<exists> sets' :: (VARS set).
\<exists> dvar' :: (VARS set).
\<exists> constant :: (VARS set \<rightharpoonup> VARS).
\<exists> newTerm :: VARS.
\<exists> parameters :: (VARS set).
 (parameters \<subseteq> sets \<union> terms) 
\<and> (parameters \<noteq> {})
\<and> (newTerm = the (constant parameters))
\<and> (terms' = terms \<union> {(newTerm)})
\<longrightarrow> (TermDeclaration \<subseteq> declarations)
\<and> (SetDeclaration \<subseteq> declarations)
\<and> (dvars \<subset> sets \<union> terms)
\<and> (sets \<inter> terms = {}))"
sorry

lemma CorrectSetDeclaration_L6:
"(\<exists> zcgastate :: ZcgaState.
\<exists> zcgastate' :: ZcgaState.
\<exists> declarations':: (VARS * EXPRESSION) set.
\<exists> expressions' :: (LINES set).
\<exists> definitions' :: (LINES set).
\<exists> definedConstants' :: (VARS set).
\<exists> TermDeclaration' :: (VARS * EXPRESSION) set.
\<exists> SetDeclaration' :: (VARS * EXPRESSION) set.
\<exists> terms' :: (VARS set).
\<exists> sets' :: (VARS set).
\<exists> dvar' :: (VARS set).
\<exists> dvarExpression :: EXPRESSION.
\<exists> var :: VARS.
 (var \<notin> dvar)
\<and> (SetDeclaration' = SetDeclaration \<union> {(var, dvarExpression)}) 
\<and> (sets' = sets \<union> {var}) 
\<and> (dvar' = dvar \<union> {var})
\<longrightarrow> (TermDeclaration \<subseteq> declarations)
\<and> (SetDeclaration \<subseteq> declarations)
\<and> (dvars \<subset> sets \<union> terms)
\<and> (sets \<inter> terms = {}))"
sorry

end
end