'''
Created on 27 Aug 2014

This program uses the Z-CGa rules from MathLang to check a latex Z specification for correctness.
@author: lb89
'''
  
import re
global someset
global errorSet
global Vt_set
global Vs_set
global dvar
global gamma
global constant_sets
global constant_terms
global correct_sets
global definitions
global preface_constants
global defined_constants
global correct_preface_set_constants
global spec
someset = []
errorSet=[]
declaredtypes = ["\\nat", "\\nat_1", 'power', 'pfun', '\\num']
Vs_set = []
Vt_set = []
dvar = []
gamma = []
constant_sets = []
constant_terms = []
correct_sets = ["\{ \}"]
correct_terms = []
definitions = []
preface_constants = ["\\cup", "\\cap", "\\dom", "\\ran", "=", "\\subseteq", "\\mapsto","\\iseq"
"\\emptyset", "\\plus", "\\notin", "\\in", "\\#", "\\neq", "\\implies", "\semi",
"\\limg", "\\rimg", "\\rres", "\\leq", "\\vert" ]
defined_constants = []
correct_preface_set_constants = []
global no_of_errors
no_of_errors = 0
spec = []

#def emptysomset():
    #return someset

#finds all the set variables in the specification both declared and not declared
# this gives us the set V^(S) as shown in the rules
def vs_set(specification):
    global Vs_set
    for a in specification:
        var_set = re.findall(r"\\set{([!?A-Za-z\']*)}", a)
        type_set = re.findall(r"\\set{([A-Z]+)}", a)
        if var_set:
            for words in var_set:
                if words not in type_set:
                    Vs_set.append(words)
    return Vs_set

#finds all the term variables in the specification both declared and not declared
# this gives us the set V^(T) as shown in the rules
def vt_set(specification):
    global Vt_set
    #Vt_set=[]
    for a in specification:
        var_term = re.findall(r"\\term{([!?A-Za-z\']*)}", a)
        if var_term:
            for words in var_term:
                Vt_set.append(words)
    return Vt_set

#checks if the specification is empty 
def emptyspecification(specification):
    bit = r"\\specification{[ ]*}"
    checkbit = re.compile(bit)
    for a in specification:
        emptyspecification = checkbit.search(a)
        if emptyspecification:
            someset.append("Empty Specification\n")
            spec.append("")
            return True    

#checks if the schematext is empty 
def emptytext(specification):
    bit = r"\\specification{[ ]*\\text{}}"
    checkbit = re.compile(bit)
    for a in specification:
        emptytext = checkbit.search(a)
        if emptytext:
            someset.append("Empty Text\n")
            gamma.append("")
            return True

#\expression{$\forall$ \declaration{\term{t}:\expression{$\ran$ rented}} 
#$@$ \expression{\term{$\#$ \set{\set{rented} $\rres$ \set{\{\term{t}\}}}} 
#$\leq$ \term{\set{stockLevel}~\term{t}}}}}        
def binders(specification):
    global no_of_errors
    global errorSet
    binder_constants = ["$\\forall$"]
    bindercomp = re.compile(r"\\expression{((\$\\[a-z]+\$)[ ]*\\declaration{(.*)}[ ]*\$\@\$[ ]*\\expression{(.*)})")
    for eachline in specification:
        binder = bindercomp.search(eachline)
        if binder:
            cons_b = binder.group(2)
#Declaration (Z) is a correct declaration in the binder and add the variables into dvar
            decl_b = re.findall(r"(\\declaration{[ ]*\\[terms]+{([a-zA-Z]+)}[ ]*:[ ]*\\expression{.*}})[ ]*\$@\$", eachline)
            if decl_b:
                for a, b in decl_b:
                    if b not in dvar:
                        dvar.append(b)
                    if a not in gamma:
                        gamma.append(a)
#Here we check that b is in the set of defined binders B
            if cons_b not in binder_constants:
                errorSet.append(cons_b)
                someset.append(str(cons_b) + " not in binder constants\n")
                no_of_errors = no_of_errors + 1
#Since the ext_constant_expression function checks all labeled \expression, we know that the
#expression within the binder is correct.

    return binders


        
def gammacorrect(specification):
    if emptyspecification(specification) or not emptyspecification(specification):
        return True

#Looks at the declarations, adds the sets which are declared into dvar and adds the correct
#declarations into gamma        
def set_declaration(specification):
    for a in specification:
        setdec = re.findall(r"(\\declaration{[ ]*\\set{(.*)}[ ]*:[ ]*\\expression{.*}})", a)
        if setdec:
            for a, b in setdec:
                if b not in dvar:
                    dvar.append(b)
                    dvar.append(b + "'")
                    for x in dvar:
                        correct_sets.append(x)
                gamma.append(a)

#Looks at the declarations, add's the terms's which are declared into dvar and adds the correct
#declarations into gamma 
def term_declaration(specification):
    termdeclarationcomp = re.compile(r"(\\declaration{[ ]*\\term{([!\?A-Za-z]*)}[ ]*:[ ]*\\expression{.*}})")
    for a in specification:
        termdec = re.findall(r"(\\declaration{[ ]*\\term{(.*)}[ ]*:[ ]*\\expression{.*?}})", a)
        if termdec:
            termdecinterm = re.findall(r"\\term{(.*?)}", a)
            if termdecinterm:
                for eachterm in termdecinterm:
                    if eachterm not in dvar:
                        dvar.append(eachterm)
                        dvar.append(eachterm + "'")
                        for x in dvar:
                            correct_terms.append(x)
        termdeclaration = termdeclarationcomp.search(a)
        if termdeclaration:
            if termdeclaration.group(1) not in gamma:
                gamma.append(termdeclaration.group(1))
                
                

#Looks at the defined type with parameters and adds the parameters into dvar
#for example MESSAGE:== inStock | notInStock. Would add inStock and notInstock into dvar
#The rule for internal constant terms
def int_cons_term(specification):
    declaredsettypecomp = re.compile(r"\\set\{([A-Z]*)\}[ ]*::=[ ]*(\\term\{[\_a-z\\]*\} \|)+")
    for a in specification:
        int_cons_term = declaredsettypecomp.search(a)
        if int_cons_term:
            terms = re.findall(r"\\term{([\_\!\?A-Za-z\\]*)}", a)
            for word in terms:
                dvar.append(word)
                correct_terms.append(word)
    return correct_terms

#For every set variable found in the specification, it checks if it is in the declared variables
#if not it prints out a list of all the set variables found which are not declared            
def variable_set(specification):
    global no_of_errors
    global errorSet
    global dvar
    nondeclared = []
    vs_set(open(specification, "r"))
    set_declaration(open(specification, "r"))
    for a in Vs_set:
        if a not in dvar:
            if a not in defined_constants:
                if a not in nondeclared:
                    nondeclared.append(a)
                    no_of_errors = no_of_errors + 1
                    

        else:
            if a not in correct_sets:
                correct_sets.append(a)
                correct_sets.append(a + "'")
    if nondeclared:
        for n in nondeclared:
            errorSet.append(n)
        someset.append(str(nondeclared)+ " non declared sets \n")
        
    return correct_sets
#For every term variable found in the specification, it checks if it is in the declared variables 
#if not it prints out a list of all the term variables found which are not declared
def variable_term(specification):
    global no_of_errors
    global errorSet
    nondeclared = []
    vt_set(open(specification, "r"))
    term_declaration(open(specification, "r"))
    int_cons_term(open(specification, "r"))
    for a in Vt_set:
        if a not in dvar:
            if a not in nondeclared:
                nondeclared.append(a)
                no_of_errors = no_of_errors + 1
        else:
            if a not in correct_terms:
                correct_terms.append(a)
    if nondeclared:
        for n in nondeclared:
            errorSet.append(n)
        someset.append(str(nondeclared)+" non declared terms\n")
    return correct_terms

#Sometimes brackets are put around variables so we they should be allowed as well
def bracket_variables(specification):
    global no_of_errors
    global errorSet
    nondeclared = []
    for line in specification:
        bra_var = re.findall("\(([\!\?a-zA-Z]+)\)", line)
        for eachvar in bra_var:
            if eachvar not in dvar:
                if eachvar not in nondeclared:
                    nondeclared.append(eachvar)
                    no_of_errors = no_of_errors + 1
            else:
                if eachvar not in dvar:
                    dvar.append(eachvar)
    if nondeclared:
        for n in nondeclared:
            errorSet.append(n)
        someset.append(str(nondeclared)+ " not declared terms\n")
    return dvar
        

#This function finds all the defined internal constants within a specification
#it checks that only defined types are used within declarations.
def internalconstant(specification):
    global declaredtypes
    global no_of_errors
    nondeclaredtypes = []
    declaredtypecomp = re.compile(r"\[\\set\{([A-Z]*)\}\]")
    declaredsettypecomp = re.compile(r"\\set\{([A-Z]*)\} *::= *(\\term\{[\_a-z\\]*\} *\|)+")
    q = re.compile(r"\\set{([A-Z]+)} *::= *")
    declaredmanytypecomp = re.compile(r"\[\\set{[A-Z]+}[, ~ \\set{[A-Z]*}]*\]")
    declarationcomp1 = re.compile(r"\\declaration{[ ]*\\[terms]+{[!?A-Za-z]*}[ ]*:[ ]*\\expression{(.*)}}")
    definition(open(checking, "r"))
#Here we make sure gamma prime and definitions are in spec
    for eachdef in definitions:
        if eachdef not in spec:
            spec.append(eachdef)
#Here we make sure all the defined constants are of correct set
    for each_defcon in defined_constants:
        correct_sets.append(each_defcon)
    for a in specification:
        qz = q.search(a)
        declaredsettype = declaredsettypecomp.search(a)
        declaredtype = declaredtypecomp.search(a)
        declaredmanytype = declaredmanytypecomp.search(a)
        setdeclaration1 = declarationcomp1.search(a)
#this finds the declared types
        if declaredtype:
            declaredtypes.append(declaredtype.group(1))
#many times can be defined at once eg [STUDENT, MODULE] therefore this function finds all of
#these types
        elif declaredmanytype:
            x = re.findall(r"([A-Z]+)", a)
            if x:
                for word in x:
                    declaredtypes.append(word)
#This finds the declared typed which comes with parameters eg MESSAGE::= notInstock | inStock
#The constant terms which are defined are written in the rule int_cons_term
        if declaredsettype:
            declaredtypes.append(declaredsettype.group(1))
            
#This checks if the types used in declarations are defined beforehand
        if setdeclaration1:
            typeused = fixbrackets(setdeclaration1.group(1))
            if typeused not in declaredtypes:
                madetype1 = re.findall(r"\$\\power\$ *(.*)", typeused)
                madetype2 = re.findall(r"(.*) +\$.*\$ +(.*?)", typeused)
                madetype3 = re.findall(r"((.*) ?([a-z]+)?)}} \$\@\$", typeused)
                madetype4 = re.findall(r"([a-zA-Z]+)}*", typeused)
                if madetype3:
                    for correct_set, cons, var in madetype3:
                        if cons not in preface_constants:
                            errorSet.append(cons)
                            someset.append( str(cons) + " constant not in preface")
                            no_of_errors = no_of_errors + 1
                        elif var not in correct_sets:
                            errorSet.append(var)
                            someset.append(str(var) + " variable not declared")
                            no_of_errors = no_of_errors + 1
                        else:
                            correct_sets.append(correct_set)
                elif madetype1:
                    for eachtype in madetype1:
                        eachtype = fixbrackets(eachtype)
                        if eachtype not in declaredtypes:
                            nondeclaredtypes.append(eachtype)
                            no_of_errors = no_of_errors + 1
                elif madetype2:
                    for a, b in madetype2:
                        if a not in declaredtypes:
                            nondeclaredtypes.append(a)
                            no_of_errors = no_of_errors + 1
                        if fixbrackets(b) not in declaredtypes:
                            nondeclaredtypes.append(fixbrackets(b))
                            no_of_errors = no_of_errors + 1
                elif madetype4:
                    for eachset in madetype4:
                        if (eachset not in declaredtypes):
                            if eachset not in dvar:
                                nondeclaredtypes.append(eachset)
                                no_of_errors = no_of_errors + 1 
                else:
                    nondeclaredtypes.append(typeused)
                    no_of_errors = no_of_errors + 1   
    if nondeclaredtypes:
        for n in nondeclaredtypes:
            errorSet.append(n)
        someset.append(str(nondeclaredtypes)+ " types not declared\n")
    return declaredtypes

#sometimes when i find a set in a line there is not enough paranthesis because when i search for
# .*? it only finds the first paranthesis. This function adds the full amount of parenthesis so that
#they are balanced.
def fixpanthesis(a_word):
    somemadeset = (re.compile(r"(\\{\\term{.*)")).search(a_word)
    amountopen = a_word.count("{")
    amountclosed = a_word.count("}")
    if somemadeset:
        while amountclosed < amountopen:
            a_word = a_word + "}\\}"
            amountclosed = amountclosed + 2
    else:                                                   
        if amountclosed < amountopen:
            while amountclosed < amountopen:
                a_word = a_word + "}"
                amountclosed = amountclosed + 1
    return a_word


def ext_constant_set(specification):
    global no_of_errors
    set_declaration(open(checking, "r")) 
    internalconstant(open(checking, "r"))
    for line in specification:
        sett = re.findall(r"\\set\{(.*?)\}", line)
        madeset = re.findall(r"\\set{(\\{.*\\})}", line)
        twoset = re.findall(r"\\set\{(\\set\{.*?\} .*? \\set\{.*?\})\}", line)
        madeset_dec_ex = re.findall(r"(\\set{\\{ *\\declaration{.*}[ ]*:[ ]*\\expression{.*}})[ ]*\$\\vert\$[ ]*(\\expression{.*}}) *\\}", line)

#finds all the sets joined by a constant which needs two parameters. Checks if the parameters
#is defined in the preface
        if twoset:
            twosetconstant = re.findall(r"\\set\{\\set\{.*?\} (.*?) \\set\{.*?\}\}", line)
            for a in twosetconstant:
                if a in preface_constants:
                    correct_preface_set_constants.append(a)
                    for everyset in twoset:
                        correct_sets.append(everyset)
#the madeset are binders (eg \{something\}), so this rule will be found in the binder section.
#However it adds the made sets into the correct sets so they can be used with the constants                    
        if madeset:
            for eachmadeset in madeset:
                correct_sets.append(eachmadeset)
#finds all the annotated sets in the specification
        if madeset_dec_ex:
            for first, expres in madeset_dec_ex:
                dec = re.findall(r"(\\declaration{\\term{([\!\?a-zA-Z]+)}:\\expression{(.*?)}})", first)
                if dec:
                    for decl, var, exp in dec:
                        if exp in declaredtypes or exp in dvar:
                            gamma.append(decl)
                            dvar.append(var)
                            correct_terms.append(var)
                if expres:
                    ters = re.findall(r"\\term{(.*)} .* \\term{(.*?)}", expres)
                    for c, d in ters:
                        if c not in correct_terms:
                            correct_terms.append(c) 
                        if d not in correct_terms:
                            correct_terms.append(d)
        if sett:
            for word in sett:
#ignore word if the set is a declared type
                if word in declaredtypes:
                    pass
#ignore word if the set is a declared variable
                elif word in dvar:
                    pass
                else:
#this checks if the constant on the left of the set is in the preface
                    onesetconstant = re.findall(r"(\$.*\$ \\set\{[a-z]*\})", fixpanthesis(word))
                    rightonesetconstant = re.findall(r"([a-z]+ .*)", fixpanthesis(word))
#checks the constants which only take one parameter if it is in the preface such a dom student.
                    if onesetconstant:
                        setconstant = re.findall(r"(\$.*\$) \\set\{[a-z]*\}", fixpanthesis(word))
                        for a in setconstant:
                            if a in preface_constants:
                                correct_preface_set_constants.append(a)
                                for eachset in onesetconstant:
                                    correct_sets.append(eachset)
#this checks if the constant on the right of the set is in the preface
                    elif rightonesetconstant:
                        setconstant = re.findall(r"[a-z]* (\$.*\$)", fixpanthesis(word))
                        for a in setconstant:
                            if a in preface_constants:
                                correct_preface_set_constants.append(a)
                                correct_sets.append(word)
    return correct_sets
      
    
def ext_constant_term(specification):
    global no_of_errors
    nonprefcons = []
    expressionlabel = re.compile(r"\\expression{(.*)}")
    termlabel = re.compile(r"\\term{(.*?})}")
    setermlabel = re.compile(r"(\\set{.+}\(\\term{.+}\))")
    expinexpcomp  = re.compile(r"\\expression{.*\\expression{(.*)}}")
    for line in specification:
        expression = expressionlabel.search(line)
        seterm = setermlabel.search(line)
        expinexp = expinexpcomp.search(line)
        if expinexp:
            seterm = setermlabel.search(expinexp.group(1))
            if seterm:
                if seterm.group(1) not in correct_terms:
                    correct_terms.append(seterm.group(1))
        if expression:
            seterm = setermlabel.search(line)
            if seterm:
                if seterm not in correct_terms:
                    correct_terms.append(seterm.group(1))
            constanterm = termlabel.search(expression.group(1))
            if constanterm:
                cons_term = constanterm.group(1)
                twosetconstant = re.findall(r"\\term{.*} *(\$\\[a-z]+\$) *\\term{.*}" , cons_term)
                onesetconstant= re.findall(r"(\$\\#\$) *\\set{.*}", cons_term)
                set_applied_term= re.findall(r"\\set{.+}[ ~\(]*\\term{.+}[\)]?", cons_term)
#If the constant in between two terms is not in the preface add it to the set of non preface constants
#else add the term into the set of correct terms
                if twosetconstant:
                    for everyconstant in twosetconstant:
                        if everyconstant not in preface_constants:
                            nonprefcons.append(everyconstant)
                            no_of_errors = no_of_errors + 1
                        else:
                            if cons_term not in correct_terms:
                                correct_terms.append(cons_term)
#If the constant before the set is not in the preface then add it to the set of non preface constants
#else add the term into the set of correct terms
                elif onesetconstant:
                    for everyconstant in onesetconstant:
                        if everyconstant not in preface_constants:
                            nonprefcons.append(everyconstant)
                            no_of_errors = no_of_errors + 1
                        else:
                            if cons_term not in correct_terms:
                                correct_terms.append(cons_term)
                elif set_applied_term:
                    for cons_term in set_applied_term:
                        if cons_term not in correct_terms:
                            correct_terms.append(cons_term)
    #if nonprefcons:
        #print nonprefcons, " constants not in preface"   
    return correct_terms
      
#The fix brackets function takes away any extra parenthesis which sometimes occurs in a string.             
def fixbrackets(someword):
    someword_bracket = (re.compile(r"^([\_a-zA-Z?\\\(\)\{\}]*)(})")).search(someword)
    somemadeset = (re.compile(r"^({.*})(\\})")).search(someword)
    if somemadeset:
        newWord = somemadeset.group(1)
    if someword_bracket:
        newWord = someword_bracket.group(1)
    else:
        newWord = someword
    return newWord

#The externaltospec function comapres each constant and makes sure it is not already defined.
#This rule is used in the ext-cons rule of the Z-CGa
def externaltospec(a, b):
    global errorSet
    for each_constant in a:
        if each_constant in b:
            errorSet.append(each_constant)
            someset.append(str(each_constant) + " constant already in spec\n")
        else:
            return True
        
#This function checks the definitions of the specification
def definition(specification):
    global no_of_errors
    global errorSet
    non_declared_variables = []
#We make sure that a set is declared after the let
    defintiontypecomp = re.compile(r"\\definition{\(?\$\\LET\$ *\\set\{([a-z]+)}")
    for line in specification:
        definitionline = defintiontypecomp.search(line)
        if definitionline:
            defcon = definitionline.group(1)
            x = re.findall(r"\\set{\(?([a-z]+)}", line)
            y = re.findall(r"\\set{([a-z]+)\$.*\$}", line)
#We make sure that all variables x_1, ..., x_n are in dvar
            if x and not defcon:
                for every_variable in x:
                    if every_variable not in dvar:
                        no_of_errors = no_of_errors + 1
                        if every_variable not in non_declared_variables:
                            non_declared_variables.append(every_variable)                            
            elif y and not defcon:
                for every_made_variable in y:
                    if every_made_variable not in dvar:
                        no_of_errors = no_of_errors + 1
                        if every_made_variable not in non_declared_variables:
                            non_declared_variables.append(every_made_variable)
#If constant set is not in preface constants union defined constants
            if defcon:
#Check that c is not in prefcons union defcons
                if defcon not in set(preface_constants).union(set(defined_constants)):
                    defined_constants.append(defcon)
                    definitions.append(line)
    if non_declared_variables:
        for n in nondeclared_variables:
            errorSet.append(n)
        someset.append( str(non_declared_variables)+ " non declared sets\n")
    return definitions

#The ext_constant_expression makes sure all the constants used in expressions have been defined
#in the preface
def ext_constant_expression(specification):
    global no_of_errors
    global errorSet
    notinpreface = []
    correct_expressions = []
    ext_constant_term(open(checking, "r"))
    ext_constant_set(open(checking, "r"))
    variable_set(checking)
    variable_term(checking)
    bracket_variables(open(checking, "r"))
#here we call a function to check that c is external to spec
    externaltospec(preface_constants, declaredtypes)
    for line in specification:
        expr_cons = re.findall(r"\\expression{\\set{.*} *.* *\\set{.*}}", line)
        ss = re.findall(r"\\expression{(\\set{.*} *.* *\\set{.*})}", line)
        ts = re.findall(r"(\\expression{\\term{.*} *.* *\\set{.*}})", line)
        tt = re.findall(r"\\expression{\\term{(.*)} *(=) *\\term{(.*)}}", line)
        z = re.findall(r"\$\\[a-z]+\$|=", line)
# here we have to find if the expression is a set and set, term and set, or term and term
        if ss:
# here we are checking if parameters to the constants are legal
            x = re.findall(r"\\set{(.*?)}", line)
            for a in x:
                a = fixpanthesis(a)
                if a not in correct_sets:
                    x = re.findall(r"\\set{(.*)}", a)
                    y =  re.findall(r"\\set{(\\{.*\\})}", a)
                    if y:
                        pass
                    elif x:
                        for a in x:
                            a = fixpanthesis(a)
                            if a not in correct_sets:
                                errorSet.append(a)
                                someset.append(str(a) +  " - not a correct set\n")
                                no_of_errors = no_of_errors + 1
                            else:
#before we append expressions to correct expressions we check if c external to spec
                                for cons in z:
                                    if cons in preface_constants:
                                        correct_expressions.append(line)
                                    else:
                                        if cons not in notinpreface:
                                            notinpreface.append(cons)
                                            no_of_errors = no_of_errors + 1
# again we check if parameters are legal, then constant is external to spec, which is what the set
#preface_expression_constant is
                else:
                    for expres in expr_cons:
                        z = re.findall(r"\$\\[a-z]+\$|=", expres)
                        for cons in z:
                            if cons in preface_constants:
                                correct_expressions.append(expres)
                            else:
                                if cons not in notinpreface:
                                    notinpreface.append(cons)
                                no_of_errors = no_of_errors + 1
#now we do the same for expressions where there is a valid term and a valid set
        if ts:
            for expression in ts:
                exp = expression
            x = re.findall(r"\\set{(.*?)}", exp)
            z = re.findall(r"\$\\[a-z]+\$", exp)
            for sett in x:
                newset = fixpanthesis(sett)
                if newset not in correct_sets:
                    newx = re.findall(r"\\set{(.*?)}", newset)
                    if newx:
                        for eachset in newx:
                            if eachset not in correct_sets:
                                errorSet.append(eachset)
                                someset.append(str(eachset) + " not a correct set\n")
                                no_of_errors = no_of_errors + 1
                    else:
                        errorSet.append(newset)
                        someset.append(str(newset) + " not a correct set\n")
                        no_of_errors = no_of_errors + 1
            for cons in z:
                if cons not in preface_constants:
                    if cons not in notinpreface:
                        errorSet.append(cons)
                        notinpreface.append(cons)
                    no_of_errors = no_of_errors + 1
                else:
                    correct_expressions.append(exp)
#now we do the same for all expressions which include two terms
        if tt:
            for a,b,c in tt:
                if a not in correct_terms:
                    findtermsinterms = re.findall(r"\\term{(.*?)}", a)
                    if findtermsinterms:
                        for eachterms in findtermsinterms:
                            if eachterms not in correct_terms:
                                errorSet.append(a)
                                someset.append(str(a) + " not a correct term\n")
                                no_of_errors = no_of_errors + 1
                    else:
                        errorSet.append(a)
                        someset.append(str(a) + " not a correct term\n")
                        no_of_errors = no_of_errors + 1
                if c not in correct_terms:
                    c = fixbrackets(c)
                    if c not in correct_terms:
                        d = re.findall(r"\\term{([a-zA-Z\_\?\!\\]+)}", c)
                        for eachterm in d:
                            if eachterm not in correct_terms:
                                errorSet.append(c)
                                someset.append(str(c) + " not a correct term\n")
                                no_of_errors = no_of_errors + 1
                if b not in preface_constants:
                    if b not in notinpreface:
                        notinpreface.append(b)
                        no_of_errors = no_of_errors + 1
                else:
                    correct_expressions.append(line)
    if notinpreface:
        errorSet.append(notinpreface)
        someset.append(str(notinpreface)+ "constants not in preface")
    return correct_expressions
      
#The assumption function adds all correct expressions to the context, gamma.                
def assumption(specification):
    for each_expression in ext_constant_expression(specification):
        if each_expression not in gamma:
            gamma.append(each_expression)

def spec_ext(specification):
    for each_line in gamma:
        if each_line not in spec:
            spec.append(each_line)

#The doall method calls all functions together
def doall(someinput):
    emptyspecification(open(someinput, "r"))
    emptytext(open(someinput, "r"))
    assumption(open(someinput, "r"))
    spec_ext(open(someinput, "r"))
    binders(open(someinput, "r"))
    schemaNames((open(someinput, "r")))

#Calls do all on the input, counts the amount of errors, if not errors then prints spec is correct
#and gamma, if there are errors then spec is incorrect    
def specCorrect(something):
    global no_of_errors
    global errorSet
    global someset
    global checking
    checking=something
    cleanValues()
    doall(something)
    if no_of_errors == 0:
        someset.append( "Spec Grammatically Correct\n")
        #print "spec = ", spec
    else:
        someset.append("Spec Grammatically Incorrect\n")
        someset.append("Number of errors "+ str(no_of_errors))
    
#Sets the initial values of the variables,
#making sure that everything's been cleaned when the function is run again.                
def cleanValues():
    global no_of_errors
    global someset
    global errorSet
    global checking
    global Vt_set
    global Vs_set
    global dvar
    global declaredtypes
    global gamma
    global constant_sets
    global constant_terms
    global correct_sets
    global definitions
    global preface_constants
    global defined_constants
    global correct_preface_set_constants
    global spec
    no_of_errors=0
    someset=[]
    errorSet=[]
    Vt_set=[]
    Vs_set=[]              
    dvar=[]
    declaredtypes = ["\\nat", "\\nat_1", 'power', 'pfun', '\\num']
    gamma = []
    constant_sets = []
    constant_terms = []
    correct_sets = ["\{ \}"]
    correct_terms = []
    definitions = []
    preface_constants = ["\\cup", "\\cap", "\\dom", "\\ran", "=", "\\subseteq", "\\mapsto",
    "\\emptyset", "\\plus", "\\notin", "\\in", "\\#", "\\neq", "\\implies", "\semi","\\iseq"
    "\\limg", "\\rimg", "\\rres", "\\leq", "\\vert" ]
    defined_constants = []
    correct_preface_set_constants = []
    spec = []
    
          
#check schemaNamesdef emptyspecification(specification):
def schemaNames(specification):
    global no_of_errors
    global errorSet
    setNames = []
    declaredschemaName = r"\\begin\{schema\}\{(.+)\}"
    namesInText = r"\\text\{((\\Delta|\\Xi)?[ ]*([\_\\a-zA-Z0-9]+))[ ]*\}"
    checkName = re.compile(declaredschemaName)
    checkNameInText = re.compile(namesInText)
    for a in specification:
        declaredSname = checkName.search(a)
        nameInText = checkNameInText.search(a)
#Adds all schemaNames into a list
        if declaredSname:
            setNames.append(declaredSname.group(1))
#Adds the prime schema to the defined schemas
            setNames.append(declaredSname.group(1) + "'")
#Checks if all called schemas in schematext are actual defined schemas
        if nameInText:
            calledName = nameInText.group(3)
            if calledName not in setNames:
                no_of_errors = no_of_errors + 1
                errorSet.append(calledName)
                someset.append(str(calledName) + " not a defined Schemas\n")
            else:
                gamma.append(nameInText.group(1))
def printoutput():
    outputmessage = " ".join(someset)
    return outputmessage
    
def errors():
    global errorSet
    return errorSet

     


#checking = raw_input("Please type the specification which you would like to check: ")
#checking = "zcga_vendingmachine.tex"
#specCorrect(checking)


