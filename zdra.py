'''
Created on 4 May 2015
@author: Lavinia Burski
The ZDRa checks for Document Rhetorical correctness and produces a ProofPower Proof Skeleton
'''


import zdracheck
import re
from tempfile import mkstemp
from shutil import move
from os import remove, close


        
def outputsPre(a):
    edgeswithnames = zdracheck.goto_edges
    for (k, l) in edgeswithnames:
        if (k == a) and ("PRE" in l):
            return l
def outputsPo(a):
    edgeswithnames = zdracheck.goto_edges
    for (k, l) in edgeswithnames:
        if (k == a) and ("PO" in l):
            return l
def outputsO(a):
    edgeswithnames = zdracheck.goto_edges
    for (k, l) in edgeswithnames:
        if (k == a) and ("O" in l):
            return l
def preallowspo(a):
    edgeswithnames = zdracheck.goto_edges
    for (k,l) in edgeswithnames:
        if (a == k) and (zdracheck.goto_edges[(k, l)] == "allows"):
            return l
def outputsSi(a):
    edgeswithnames = zdracheck.goto_edges
    for (k, l) in edgeswithnames:
        if (k == a) and ("SI" in l):
            return l

def createPPZskel(somename):
    middlename = zdracheck.creatname(somename)
    newname = "gpsa"+ middlename+ ".doc"
    gpsa = open(newname, "w")
    schemastovalue = []
    addedtoppzkel = []
    

    zdracheck.createskeleton_set()

    gpsa.write("repeat drop_main_goal;\n")
    gpsa.write("open_theory \"z_library\";\n")
    gpsa.write("set_pc \"z_library\";\n")
    gpsa.write("set_flags [(\"z_type_check_only\", false), (\"z_use_axioms\", false)];\n")
    gpsa.write("\n")
    gpsa.write("new_theory \""+newname+"\";\n")
    gpsa.write("\n")
            
    for (a, b) in zdracheck.orderofgraph:
        if b == "stateSchema" and a not in addedtoppzkel:
            if outputsSi(a):
                gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("%BV% (*DECLARATIONS*)\n")
                gpsa.write("%BV% (*" + outputsSi(a) + "*) \n")
                gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("\n")
                if a not in addedtoppzkel:
                    addedtoppzkel.append(a)
                if outputsSi(a) not in addedtoppzkel:
                    addedtoppzkel.append(outputsSi(a))
                if a not in schemastovalue:
                    schemastovalue.append(a)
            elif a not in addedtoppzkel:
                gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("%BV% (*DECLARATIONS*)\n")
                gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("\n")
                if a not in addedtoppzkel:
                    addedtoppzkel.append(a)
                if a not in schemastovalue:
                    schemastovalue.append(a)
        if b == "changeSchema" and a not in addedtoppzkel:
            if outputsPre(a):
                if preallowspo(outputsPre(a)):
                    gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                    gpsa.write("%BV% (*DECLARATIONS*)\n")
                    gpsa.write("%BV% (*" + outputsPre(a) + "*) \n")
                    gpsa.write("%BV% (*" + preallowspo(outputsPre(a)) + "*) \n")
                    gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                    gpsa.write("\n")
                    if a not in addedtoppzkel:
                        addedtoppzkel.append(a)
                    if outputsPre(a) not in addedtoppzkel:
                        addedtoppzkel.append(outputsPre(a))
                    if (preallowspo(outputsPre(a))) not in addedtoppzkel:
                        addedtoppzkel.append(preallowspo(outputsPre(a)))
                    if a not in schemastovalue:
                        schemastovalue.append(a)
                else:
                    gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                    gpsa.write("%BV% (*DECLARATIONS*)\n")
                    gpsa.write("%BV% (*" + outputsPre(a) + "*) \n")
                    gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                    gpsa.write("\n")
                    if a not in addedtoppzkel:
                        addedtoppzkel.append(a)
                    if (outputsPre(a)) not in addedtoppzkel:
                        addedtoppzkel.append(outputsPre(a))
                    if a not in schemastovalue:
                        schemastovalue.append(a)
            elif outputsPo(a):
                gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("%BV% (*DECLARATIONS*)\n")
                gpsa.write("%BV% (*" + outputsPo(a) + "*) \n")
                gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("\n")
                if a not in addedtoppzkel:
                    addedtoppzkel.append(a)
                if outputsPo(a) not in addedtoppzkel:
                    addedtoppzkel.append(outputsPo(a))
                if a not in schemastovalue:
                    schemastovalue.append(a)
            elif a not in addedtoppzkel:
                gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("%BV% (*DECLARATIONS*)\n")
                gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("\n")
                if a not in addedtoppzkel:
                    addedtoppzkel.append(a)
                if a not in schemastovalue:
                    schemastovalue.append(a)
        if b == "outputSchema" and a not in addedtoppzkel:
            if outputsPre(a):
                if preallowspo(outputsPre(a)):
                    gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                    gpsa.write("%BV% (*DECLARATIONS*)\n")
                    gpsa.write("%BV% (* " + outputsPre(a) + "*) \n")
                    gpsa.write("%BV% (*" + preallowspo(outputsPre(a)) + "*) \n")
                    gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                    gpsa.write("\n")
                    if a not in addedtoppzkel:
                        addedtoppzkel.append(a)
                    if outputsPre(a) not in addedtoppzkel:
                        addedtoppzkel.append(outputsPre(a))
                    if (preallowspo(outputsPre(a))) not in addedtoppzkel:
                        addedtoppzkel.append(preallowspo(outputsPre(a)))
                    if a not in schemastovalue:
                        schemastovalue.append(a)
                else:
                    gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                    gpsa.write("%BV% (*DECLARATIONS*)\n")
                    gpsa.write("%BV% (*" + outputsPre(a) + "*) \n")
                    gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                    gpsa.write("\n")
                    if a not in addedtoppzkel:
                        addedtoppzkel.append(a)
                    if outputsPre(a) not in addedtoppzkel:
                        addedtoppzkel.append(outputsPre(a))
                    if a not in schemastovalue:
                        schemastovalue.append(a)
            elif outputsO(a):
                gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("%BV% (*DECLARATIONS*)\n")
                gpsa.write("%BV% (*" + outputsO(a) + "*) \n")
                gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("\n")
                if a not in addedtoppzkel:
                    addedtoppzkel.append(a)
                if outputsO(a) not in addedtoppzkel:
                    addedtoppzkel.append(outputsO(a))
                if a not in schemastovalue:
                    schemastovalue.append(a)
            elif a not in addedtoppzkel:
                gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("%BV% (*DECLARATIONS*)\n")
                gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("\n")
                if a not in addedtoppzkel:
                    addedtoppzkel.append(a)
                if a not in schemastovalue:
                    schemastovalue.append(a)
        elif b == "postcondition":
            if a not in addedtoppzkel:
                gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("%BV% (*DECLARATIONS*)\n")
                gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("\n")
                if a not in addedtoppzkel:
                    addedtoppzkel.append(a)
                if a not in schemastovalue:
                    schemastovalue.append(a)
        elif b == "precondition":
            if a not in addedtoppzkel:
                gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("%BV% (*DECLARATIONS*)\n")
                gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("\n")
                if a not in addedtoppzkel:
                    addedtoppzkel.append(a)
                if a not in schemastovalue:
                    schemastovalue.append(a)
        if b == "totaliseSchema" and a not in addedtoppzkel:
            if outputsPre(a):
                gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("%BV% (*DECLARATIONS*)\n")
                gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("\n")
                if a not in addedtoppzkel:
                    addedtoppzkel.append(a)
                if outputsPre(a) not in addedtoppzkel:
                    addedtoppzkel.append(outputsPre(a))
                if a not in schemastovalue:
                    schemastovalue.append(a)
            elif a not in addedtoppzkel:
                gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("%BV% (*DECLARATIONS*)\n")
                gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("\n")
                if a not in addedtoppzkel:
                    addedtoppzkel.append(a)
                if a not in schemastovalue:
                    schemastovalue.append(a)
        elif b == "output":
            if a not in addedtoppzkel:
                gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("%BV% (*DECLARATIONS*)\n")
                gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("\n")
                if a not in addedtoppzkel:
                    addedtoppzkel.append(a)
                if a not in schemastovalue:
                    schemastovalue.append(a)
        if b == "initialSchema" and a not in addedtoppzkel:
            if outputsPo(a):
                gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("%BV% (*DECLARATIONS*)\n")
                gpsa.write("%BV% (*" + outputsPo(a) + "*)\n")
                gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("\n")
                if a not in addedtoppzkel:
                    addedtoppzkel.append(a)
                if outputsPo(a) not in addedtoppzkel:
                    addedtoppzkel.append(outputsPo(a))
                if a not in schemastovalue:
                    schemastovalue.append(a)
            elif a not in addedtoppzkel:
                gpsa.write("%SZS% " +a+ " %BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("%BV% (*DECLARATIONS*)\n")
                gpsa.write("%EZ%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH%%BH% \n")
                gpsa.write("\n")
                addedtoppzkel.append(a)
                if a not in addedtoppzkel:
                    addedtoppzkel.append(a)
                if a not in schemastovalue:
                    schemastovalue.append(a)
                

        
    for allvalues in schemastovalue:
        gpsa.write("val "+ allvalues +" = z_get_spec %SZT%("+ allvalues +")%>%;\n")
        

#createPPZskel("zdra_birthdaybook.tex")
        
'''''''''''''''''''''''''''Isabelle Skeleton'''''''''''''''''''''''''''    
        

            
def createIsaskel(somename):
    printedinisaskel = []

    midname = zdracheck.creatname(somename)    
    newname = "gpsa"+ midname+ ".thy"
    isa_ps = open(newname, "w")

    zdracheck.createskeleton_set()
    

    isa_ps.write("theory " + "gpsa"+ midname + "\n")
    isa_ps.write("imports \n")
    isa_ps.write("Main \n")
    isa_ps.write("\n")
    isa_ps.write("begin \n")
    isa_ps.write("\n")
            
    for (a, b) in zdracheck.orderofgraph:
        if b == "stateSchema" and a not in printedinisaskel:
            if a == "SS1":
                if outputsSi(a):
                    isa_ps.write("record " +a+ " = \n")
                    isa_ps.write("(*DECLARATIONS*)\n")
                    isa_ps.write("\n")
                    isa_ps.write("locale " + midname + " = \n")
                    isa_ps.write("fixes (*GLOBAL DECLARATIONS*) \n")
                    isa_ps.write("assumes " + outputsSi(a) + "\n")
                    isa_ps.write("begin\n")
                    isa_ps.write("\n")
                    if a not in printedinisaskel:
                        printedinisaskel.append(a)
                    if outputsSi(a) not in printedinisaskel:
                        printedinisaskel.append(outputsSi(a))
                elif not outputsPre(a):
                    isa_ps.write("record " +a+ " = \n")
                    isa_ps.write("(*DECLARATIONS*)\n")
                    isa_ps.write("\n")
                    isa_ps.write("locale " + midname + " = \n")
                    isa_ps.write("fixes (*GLOBAL DECLARATIONS*) \n")
                    isa_ps.write("begin\n")
                    isa_ps.write("\n")
                    if a not in printedinisaskel:
                        printedinisaskel.append(a)
                elif a not in printedinisaskel:
                    isa_ps.write("record " +a+ " = \n")
                    isa_ps.write("(*DECLARATIONS*)\n")
                    isa_ps.write("\n")
                    isa_ps.write("locale " + midname + " = \n")
                    isa_ps.write("fixes (*GLOBAL DECLARATIONS*) \n")
                    isa_ps.write("begin\n")
                    isa_ps.write("\n")
                    if a not in printedinisaskel:
                        printedinisaskel.append(a)
                    if midname not in printedinisaskel:
                        printedinisaskel.append(midname)        
        if b == "changeSchema" and a not in printedinisaskel:
            if outputsPre(a):
                if preallowspo(outputsPre(a)):
                    isa_ps.write("definition "+ a + " :: \n")
                    isa_ps.write("\"(*"+a+"_TYPES*) => bool\"\n")
                    isa_ps.write("where \n")
                    isa_ps.write("\""+ a+ " (*"+a+"_VARIABLES*) ==\n " + "(" + outputsPre(a)+ ")" + "\n")
                    isa_ps.write("\\<and> " +"(" + preallowspo(outputsPre(a))+ ")" +  "\"\n")
                    isa_ps.write("\n")
                    if a not in printedinisaskel:
                        printedinisaskel.append(a)
                    if outputsPre(a) not in printedinisaskel:
                        printedinisaskel.append(outputsPre(a))
                    if (preallowspo(outputsPre(a))) not in printedinisaskel:
                        printedinisaskel.append(preallowspo(outputsPre(a)))
                else:
                    isa_ps.write("definition " +  a + " :: \n")
                    isa_ps.write( "\"(*"+a+"_TYPES*) => bool\"\n")
                    isa_ps.write("where \n")
                    isa_ps.write("\""+ a+ " (*"+a+"_VARIABLES*) == " + "(" + outputsPre(a)+ ")" + "\"\n")
                    isa_ps.write("\n")
                    if a not in printedinisaskel:
                        printedinisaskel.append(a)
                    if (outputsPre(a)) not in printedinisaskel:
                        printedinisaskel.append(outputsPre(a))
            elif outputsPo(a) and a not in printedinisaskel:
                isa_ps.write("definition " + a + " :: \n")
                isa_ps.write( " \"(*"+a+"_TYPES*) => bool\"\n")
                isa_ps.write("where \n")
                isa_ps.write("\""+ a+ " (*"+a+"_VARIABLES*) == " + "(" + outputsPo(a) + ")"+ "\"\n")
                isa_ps.write("\n")
                if a not in printedinisaskel:
                    printedinisaskel.append(a)
                if outputsPo(a) not in printedinisaskel:
                    printedinisaskel.append(outputsPo(a))
            elif a not in printedinisaskel:
                isa_ps.write("definition " + a + " :: \n")
                isa_ps.write( "\"(*"+a+"_TYPES*) => bool\"\n")
                isa_ps.write("where \n")
                isa_ps.write("\""+ a+ " (*"+a+"_VARIABLES*) == True\"\n")
                isa_ps.write("\n")
                if a not in printedinisaskel:
                    printedinisaskel.append(a)
        if b == "outputSchema" and a not in printedinisaskel:
            if outputsPre(a):
                if preallowspo(outputsPre(a)):
                    isa_ps.write("definition " + a + " :: \n")
                    isa_ps.write(" \"(*"+a+"_TYPES*) => bool\"\n")
                    isa_ps.write("where \n")
                    isa_ps.write("\""+ a+ " (*"+a+"_VARIABLES*) == " + "(" +outputsPre(a) + ")" + "\n")
                    isa_ps.write("\\<and> " + "(" + preallowspo(outputsPre(a)) + ")" + "\"\n")
                    isa_ps.write("\n")
                    if a not in printedinisaskel:
                        printedinisaskel.append(a)
                    if outputsPre(a) not in printedinisaskel:
                        printedinisaskel.append(outputsPre(a))
                    if (preallowspo(outputsPre(a))) not in printedinisaskel:
                        printedinisaskel.append(preallowspo(outputsPre(a)))
                else:
                    isa_ps.write("definition " + a + " :: \n")
                    isa_ps.write(" \"(*"+a+"_TYPES*) => bool\"\n")
                    isa_ps.write("where \n")
                    isa_ps.write("\""+ a+ " (*"+a+"_VARIABLES*) == " + "(" +outputsPre(a) + ")" + "\"\n")
                    isa_ps.write("\n")
                    if a not in printedinisaskel:
                        printedinisaskel.append(a)
                    if outputsPre(a) not in printedinisaskel:
                        printedinisaskel.append(outputsPre(a))
            elif outputsO(a) and a not in printedinisaskel:
                isa_ps.write("definition " + a + " :: \n")
                isa_ps.write( " \"(*"+a+"_TYPES*) => bool\"\n")
                isa_ps.write("where \n")
                isa_ps.write("\""+ a+ " (*"+a+"_VARIABLES*) == " + "(" +outputsO(a) + ")" + "\"\n")
                isa_ps.write("\n")
                if a not in printedinisaskel:
                    printedinisaskel.append(a)
                if outputsO(a) not in printedinisaskel:
                    printedinisaskel.append(outputsO(a))
            elif a not in printedinisaskel:
                isa_ps.write("definition " + a + " :: \n")
                isa_ps.write( "\"(*"+a+"_TYPES*) => bool\"\n")
                isa_ps.write("where \n")
                isa_ps.write("\""+ a+ " (*"+a+"_VARIABLES*) == True\"\n")
                isa_ps.write("\n")
                if a not in printedinisaskel:
                    printedinisaskel.append(a)
        elif b == "postcondition":
            if a not in printedinisaskel:
                isa_ps.write("definition " + a + " :: \n")
                isa_ps.write( "\"(*"+a+"_TYPES*) => bool\"\n")
                isa_ps.write("where \n")
                isa_ps.write("\""+ a+ " (*"+a+"_VARIABLES*) == (*POSTCONDITION*) \"\n")
                isa_ps.write("\n")
                if a not in printedinisaskel:
                    printedinisaskel.append(a)
        elif b == "precondition":
            if a not in printedinisaskel:
                isa_ps.write("definition " + a + " :: \n")
                isa_ps.write( " \"(*"+a+"_TYPES*) => bool\"\n")
                isa_ps.write("where \n")
                isa_ps.write("\""+ a+ " (*"+a+"_VARIABLES*) == (*PRECONDITION*) \"\n")
                isa_ps.write("\n")
                if a not in printedinisaskel:
                    printedinisaskel.append(a)
        if b == "totaliseSchema" and a not in printedinisaskel:
            if outputsPre(a):
                isa_ps.write("lemma " + a + ": \n")
                isa_ps.write("\"("+ outputsPre(a) + ")\"\n" )
                isa_ps.write("sorry")
                isa_ps.write("\n")
                if a not in printedinisaskel:
                    printedinisaskel.append(a)
                if outputsPre(a) not in printedinisaskel:
                    printedinisaskel.append(outputsPre(a))
            else:
                isa_ps.write("lemma " + a + ": \n")
                isa_ps.write("\"(*"+a+"_EXPRESSION*)\"\n")
                isa_ps.write("sorry")
                isa_ps.write("\n\n")
                if a not in printedinisaskel:
                    printedinisaskel.append(a)
        elif b == "output" and a not in printedinisaskel:
            if a not in printedinisaskel:
                isa_ps.write("definition " + a + " :: \n")
                isa_ps.write( " \"(*"+a+"_TYPES*) => bool\"\n")
                isa_ps.write("where \n")
                isa_ps.write("\""+ a+ " (*"+a+"_VARIABLES*) == (*EXPRESSION*) \"\n")
                isa_ps.write("\n")
                if a not in printedinisaskel:
                    printedinisaskel.append(a)
        if b == "initialSchema" and a not in printedinisaskel:
            if outputsPo(a):
                isa_ps.write("definition " + a + " :: \n")
                isa_ps.write(" \"(*"+a+"_TYPES*) => bool\"\n")
                isa_ps.write("where \n")
                isa_ps.write("\""+ a+ " (*"+a+"_VARIABLES*) == " + "(" +outputsPo(a) + ")" +"\"\n")
                isa_ps.write("\n")
                if a not in printedinisaskel:
                    printedinisaskel.append(a)
                if outputsPo(a) not in printedinisaskel:
                    printedinisaskel.append(outputsPo(a))
            elif a not in printedinisaskel:
                isa_ps.write("definition " + a + " :: \n")
                isa_ps.write( "\"(*"+a+"_TYPES*) => bool\"\n")
                isa_ps.write("where \n")
                isa_ps.write("\""+ a+ " (*"+a+"_VARIABLES*) == True\"\n")
                isa_ps.write("\n")
                if a not in printedinisaskel:
                    printedinisaskel.append(a)
    isa_ps.write("end\n")            
    isa_ps.write("end")


class fillIn:
    datatypes = []
    schemaText = []
    stateDeclarations = []
    newtypes = []
    defintionVarType = []
    allnodes = []
    nodesNnames = []
    ntypeset = dict()
    schemaVarTypes = []
    expressionSet = []
    StateDecs = []
    postcondition = []
    globalTypesvars = []
    stateInvarients = []
    state_variables = []
    newtpleset = []
    
    def cleanstring(self, somestring):
        if "\{" in somestring:
            somestring = re.sub('\\\{', ' openSet ', somestring)
        if "\}" in somestring:
            somestring = re.sub('\\\}', ' closeSet', somestring)
        if "\\" in somestring:
            somestring = re.sub('\\\\', '', somestring)
        if "text" in somestring:
            somestring = re.sub('text', '', somestring)
        if "{" in somestring:
            somestring = re.sub('{', '', somestring)
        if "}" in somestring:
            somestring = re.sub('}', '', somestring)
        if "Delta" in somestring:
            somestring = re.sub('Delta', '', somestring)
        if "?" in somestring:
            somestring = re.sub('\?', '', somestring)
        if "!" in somestring:
            somestring = re.sub('\!', '', somestring)
        if "#" in somestring:
            somestring = re.sub('\#', 'card', somestring)
        if "term" in somestring:
            somestring = re.sub('term', '', somestring)
        if "set" in somestring:
            somestring = re.sub('set', '', somestring)
        if "declaration" in somestring:
            somestring = re.sub('declaration', '', somestring)
        if "expression" in somestring:
            somestring = re.sub('expression', '', somestring)
        if "openSet" in somestring:
            somestring = re.sub(' openSet ', '{(', somestring)
        if "closeSet" in somestring:
            somestring = re.sub(' closeSet', ')}', somestring)
        if "empty" in somestring:
            somestring = re.sub('empty', '{}', somestring)
        if "cup" in somestring:
            somestring = re.sub('cup', '\<union>', somestring)
        if "neq" in somestring:
            somestring = re.sub('neq', '\<noteq>', somestring)
        if " inv" in somestring:
            somestring = re.sub(' inv', '^-1', somestring)
        if "cat" in somestring:
            somestring = re.sub('cat', 'concat', somestring)
       # if "@" in somestring:
        #    somestring = re.sub('@', '\\\\<bullet>', somestring)
        if "limg" in somestring:
            somestring = re.sub('limg', '\<lparr>', somestring)
        if "rimg" in somestring:
            somestring = re.sub('rimg', '\<rparr>', somestring)
        if "dres" in somestring:
            somestring = re.sub('dres', 'lhd', somestring)
        if "head~" in somestring:
            somestring = re.sub('head~', 'hd ', somestring)
        if "cross" in somestring:
            somestring = re.sub('cross', '\<times>', somestring)
        if "minus" in somestring:
            somestring = re.sub('minus', '-', somestring)
        if "geq" in somestring:
            somestring = re.sub('geq', '\<ge>', somestring)
        if "nat_1" in somestring:
            somestring = re.sub('nat\_1', 'nat', somestring)
        if "lhd" in somestring:
            somestring = re.sub('lhd', '\<lhd>', somestring)
        if "rhd" in somestring:
            somestring = re.sub('rhd', '\<rhd>', somestring)
        if "nrres" in somestring:
            somestring = re.sub('nrres', '\<unlhd>', somestring)
        if "forall" in somestring:
            somestring = re.sub('forall ', '\<forall>', somestring)
        if "exists" in somestring:
            somestring = re.sub('exists ', '\<exists>', somestring)
        if "implies" in somestring:
            somestring = re.sub('implies', '\<longrightarrow>', somestring)
        if " notin " in somestring:
            somestring = re.sub('notin', '\<notin>', somestring)
        elif " in " in somestring:
            somestring = re.sub(' in ', ' \<in> ', somestring)
        if " subeq " in somestring:
            somestring = re.sub(' subeq ', ' \<subseteq> ', somestring)
        if " mapsto " in somestring:
            somestring = re.sub(' mapsto ', ', ', somestring)
        if "( )" in somestring:
            somestring = re.sub('\( \)', '', somestring)
        if "()" in somestring:
            somestring = re.sub('\(\)', '', somestring)
        if " = " in somestring:
            pass
        elif "=" in somestring:
            somestring = re.sub('=', ' = ', somestring)
        if "~" in somestring:
            somestring = re.sub('~', ' ', somestring)
        somestring = self.isabelle_symbols(somestring)
        somestring = self.bindersyntax(somestring)
        somestring = somestring.lstrip()
        return somestring
    
    def bindersyntax(self, somestring):
        if " @" in somestring:
            somestring = somestring.replace("@", "\<longrightarrow")
        if ":" in somestring:
            somestring = somestring.replace(":", ".")
        if "," in somestring:
            somestring = somestring.replace(",", " ")
        return somestring
    
    def isabelle_symbols(self,string):
        if "land" in string:
            string = string.replace("land", "\<and>\n")
        if "lor" in string:
            string = string.replace("lor", "\<or>\n")
        if "dom" in string:
            string = string.replace("dom", "Domain")
        if "leq" in string:
            string = string.replace("leq", r"\<le>")
        if "minus" in string:
            string = string.replace("minus", "- ")
        if "langle " in string:
            string = string.replace("langle ", "\<langle> ")
        if "rangle " in string:
            string = string.replace("rangle ", "\<rangle> ")
        elif "ran" in string:
            string = string.replace("ran", "Range")
        return string
    
    def findNewTypes(self, somepath):
        newtypes_comp = re.compile(r".*\[\\set\{([a-zA-Z]+)\}\].*")
        manytypes_comp = re.compile(r".*\[(.*)\].*")
        set_comp = re.compile(r"\\set\{([A-Z0-9]+)\}")
        gendef_comp = re.compile(r"([A-Z0-9]+)")
        datatype_ccomp = re.compile(r"\\[terms]+\{([A-Z0-9]+)\} *::=((.|\n)*?)\\end\{zed\}")
        entire_document = ""
        labelledspec = open(somepath, 'r')
        for eachLine in labelledspec:
            entire_document+=eachLine
            newtype = newtypes_comp.findall(entire_document);
            manytype = manytypes_comp.findall(entire_document);
            datatype = datatype_ccomp.findall(entire_document);
        for each in newtype:
            if each not in self.newtypes:
                self.newtypes.append(each)
        if manytype:
            for allmanytypes in manytype:
                if "|" not in allmanytypes:
                    sett = set_comp.findall(allmanytypes);
                    gendef = gendef_comp.findall(allmanytypes);
                    if sett:
                        for allTypes in sett:
                            if allTypes not in self.newtypes:
                                self.newtypes.append(allTypes)
                    elif gendef:
                        for eachDef in gendef:
                            if eachDef not in self.newtypes:
                                self.newtypes.append(eachDef)    
        if datatype:
            for datatype_name, datatypebody, space in datatype:
                newdatatype = "datatype "+datatype_name+ " = "+ self.cleanstring(datatypebody) + "\n"
                if newdatatype not in self.datatypes:
                    self.datatypes.append(newdatatype)      
        labelledspec.close()
    
    def find_zcga_info(self, pathname):
        schemaVars = []
        schemaTypes = []
        decsToPrint = dict()
        labelspec = open(pathname, 'r')        
        multidefsend_comp = re.compile(r"\\draschema\{([a-zA-Z0-9]+)\}{([a-zA-Z0-9]+) *\\defs *\\text\{(.*)\}\}\}\}")
        draschema_comp = re.compile(r"(\\draschema\{([A-Z0-9]+)\}\{(.|\n)\\begin\{schema\}\{([a-zA-z0-9\_]*)\}(.|\n)*?\\end\{schema\})")
        globedec_comp = re.compile(r"(\\begin\{zed\}(.|\n)*?\\end\{zed\})")
        axdef_comp = re.compile(r"(\\draschema\{([a-zA-Z0-9]+)\}\{((.|\n)*?)\\where((.|\n)*?)\\end\{axdef\})")
        postcondition_comp = re.compile(r"\\draline\{(PO[0-9]+)\}\{((.|\n)*?)(\\end\{schema\}|\\end\{zed\})")
        outputcomp_comp = re.compile(r"\\draline\{(O[0-9]+)\}\{((.|\n)*?)\\end\{schema\}")
        precondition_comp = re.compile(r"\\draline\{(PRE[0-9]+)\}\{((.|\n)*?)(\\end\{schema\}|\\draline)")
        dec_comp = (r"\\declaration\{.*\}")
        expres_comp = (r"\\expression\{(\\[terms]+\{.*\}.*\\[terms]+\{.*\})\}")
        text_comp = (r"\\text\{(\\Delta|\\Xi) *([a-zA-Z0-9\_\\]+)\}")
        prime_comp = (r"\\text\{[a-zA-Z0-9\_\\]+'\}")
        othertext_comp = (r"\\text\{ *([a-zA-Z0-9\_\\]+).*\}")
        #dobequals_comp = re.compile(r"\\draschema\{([a-zA-Z0-9]+)}\{.*==(.*)\\\\")
        dobequals_comp = re.compile(r"\\draschema\{([a-zA-Z0-9]+)\}\{[a-zA-Z0-9]+ ==(.*)((.|\n)*?)")
        defs_comp = re.compile(r"\\draschema\{([A-Z0-9]+)\}{(.|\n)\\begin\{zed\}(.|\n)*?[a-zA-Z0-9\_\\]+ *\\defs((.|\n)*?)\\end{zed}")
        entire_document = ""
        for  each_line in labelspec:
            entire_document+=each_line
        axdef = axdef_comp.findall(entire_document);
        draschema = draschema_comp.findall(entire_document);
        globe_dec = globedec_comp.findall(entire_document);
        globe_deca = globedec_comp.findall(entire_document);
        post_dec = postcondition_comp.findall(entire_document);
        output_dec = outputcomp_comp.findall(entire_document);
        precon_dec = precondition_comp.findall(entire_document);
        defs = defs_comp.findall(entire_document);
        double_equals = dobequals_comp.findall(entire_document);
        multidefsend = multidefsend_comp.findall(entire_document);
        #find all post conditions and add them to postcondition set
        for po_a, po_b, po_c, po_d in post_dec:
            poSet = []
            po_expres = re.findall(expres_comp, po_b)
            for eachpo_expres in po_expres:
                eachpo_expres = self.cleanstring(eachpo_expres)
                poSet.append(eachpo_expres)
            self.postcondition.append((po_a, poSet))
        for o_a, o_b, o_c in output_dec:
            o_set = []
            o_expres = re.findall(expres_comp, o_b)
            for each_o in o_expres: 
                each_o = self.cleanstring(each_o)
                o_set.append(each_o)
            self.postcondition.append((o_a, o_set))
        for pre_a, pre_b, pre_c, pre_d in precon_dec:
            pre_set = []
            pre_expres = re.findall(expres_comp, pre_b)
            for each_pre in pre_expres:
                each_pre = self.cleanstring(each_pre)
                pre_set.append(each_pre)
            self.postcondition.append((pre_a, pre_set))
        for l, m, n, o, p, q in axdef:
            ax_dec = re.findall(r"\\declaration\{.*\}", n)
            ax_exp = re.findall(r"\\expression\{.*\}", p)
            for ab in ax_dec:
                varType_dec = re.findall(r"\\[terms]+\{(.*?)\} *: *\\expression\{(.*?)\}", ab)
                for var, var_ttype in varType_dec:
                    var_ttype = self.cleanstring(var_ttype)
                    self.stateDeclarations.append((var, var_ttype))
                    
            for ab in ax_exp:
                ab = self.cleanstring(ab)
                if (m, ab) not in self.stateInvarients:
                    self.stateInvarients.append((m, ab))
        for g, h, i, j, k in draschema:
            #g is whole schema, h is ZDRa name, i is space, j is actual name
            decl = re.findall(dec_comp, g)
            express = re.findall(expres_comp, g)
            #finding expressions in the schemas
            if express:
                for each_express in express:
                    each_express = self.cleanstring(each_express)
                self.expressionSet.append((self.cleanstring(h), each_express))
            
            #StateTypes and Declarations
            if "SS1" in h:
                for eachdec in decl:
                    if "@" not in eachdec:
                        vars = re.findall(r"\\[terms]+\{(.*?)\}", eachdec)
                        expression = re.findall(r"\\expression\{(.*?)\}", eachdec)
                        if vars > 1:
                            setOfVars = []
                            for eachVars in vars:
                                setOfVars.append(eachVars)
                            for eachExpression in expression:
                                newExpression = self.cleanstring(eachExpression)
                            for everyVar in setOfVars:
                                self.stateDeclarations.append((everyVar, newExpression))
                                self.state_variables.append(everyVar)
                        else:
                            for eachVar in vars:
                                eachVar = eachVar
                                for eachExpres in expression:
                                    if "\\power " in eachExpres:
                                        eachExpres = re.sub('\\\\power ', "", eachExpres)
                                        eachExpres = eachExpres + " set"
                                    if "\\pfun" in eachExpres:
                                        eachExpres = re.sub('\\\\pfun ', "* ", eachExpres)
                                        eachExpres = "(" + eachExpres + ") set"
                                    if "\\fun" in eachExpres:
                                        eachExpres = re.sub('\\\\fun ', "* ", eachExpres)
                                        eachExpres = "(" + eachExpres + ") set"
                                    if "\\rel" in eachExpres:
                                        eachExpres = re.sub('\\\\rel ', "* ", eachExpres)
                                        eachExpres = "(" + eachExpres + ") set"
                                self.stateDeclarations.append((eachVar, eachExpres))
                                self.state_variables.append(eachVar)
                #Check for state invariants
                #TODO if there are more then 1 state invarient
                si = re.findall(r"\{(SI[0-9]+)\}\{((.|\n)*?)\\end\{schema\}", g)
                if si:
                    for (si_num, si_expres, si_space) in si:
                        find_expressions = re.findall(r"\\expression\{(.*)\}", si_expres) 
                        for each_si_expression in find_expressions:
                            clean_si = self.cleanstring(each_si_expression)
                            if (si_num, clean_si) not in self.stateInvarients:
                                self.stateInvarients.append((si_num, clean_si))
            elif "SS" in h:
                for eachdec in decl:
                    vars = re.findall(r"\\[terms]+\{(.*?)\}", eachdec)
                    expression = re.findall(r"\\expression\{(.*?)\}", eachdec)
                    if vars > 1:
                        setOfVars = []
                        for eachVars in vars:
                            setOfVars.append(eachVars)
                        for eachExpression in expression:
                            newExpression = self.cleanstring(eachExpression)
                        for everyVar in setOfVars:
                            self.stateDeclarations.append((everyVar, newExpression))
                            self.state_variables.append(everyVar)
                    else:
                        for eachVar in vars:
                            eachVar = eachVar
                        for eachExpres in expression:
                            if "\\power " in eachExpres:
                                eachExpres = re.sub('\\\\power ', "", eachExpres)
                                eachExpres = eachExpres + " set"
                            if "\\pfun" in eachExpres:
                                eachExpres = re.sub('\\\\pfun ', "* ", eachExpres)
                                eachExpres = "(" + eachExpres + ") set"
                            if "\\fun" in eachExpres:
                                eachExpres = re.sub('\\\\fun ', "* ", eachExpres)
                                eachExpres = "(" + eachExpres + ") set"
                        self.stateDeclarations.append((eachVar, eachExpres))
                        self.state_variables.append(eachVar)
                #Check for state invariants
                #TODO if there are more then 1 state invarient
                si = re.findall(r"\{(SI[0-9]+)\}\{((.|\n)*?)\\end\{schema\}", g)
                if si:
                    for (si_num, si_expres, si_space) in si:
                        find_expressions = re.findall(r"\\expression\{(.*)\}", si_expres) 
                        for each_si_expression in find_expressions:
                            clean_si = self.cleanstring(each_si_expression)
                    if (si_num, clean_si) not in self.stateInvarients:
                        self.stateInvarients.append((si_num, clean_si))
                                
                

                        
            #If not a stateschema    
            else:
                decs_vars = []
                decs_types = []
                decl = re.findall(dec_comp, g)
                text = re.findall(text_comp, g)
                othertex = re.findall(othertext_comp, g)
                primetext = re.findall(prime_comp, g)
                
                if primetext:
                    for eachone in primetext:
                        eachone = self.cleanstring(eachone)
                    for (zdra_name, act_name) in self.nodesNnames:
                        if eachone == act_name+"'":
                            if "SS" in zdra_name:
                                for stateVars in self.state_variables:
                                    decs_vars.append((stateVars+"'"))
                                    for (k, m) in self.stateDeclarations:
                                        if stateVars == k:
                                            decs_types.append(self.setSyntax(m))
                    self.schemaVarTypes.append((h, decs_types, decs_vars))
                
                elif text:
                    decs_vars = []
                    decs_types = []
                    for (abc, eachone) in text:
                        if abc == "\\Delta":
                            eachone = self.cleanstring(eachone)
                            for (zdra_name, act_name) in self.nodesNnames:
                                if eachone == act_name:
                                    if ("SS" in zdra_name) and (zdra_name != "SS1"):
                                        zdra_name = "SS1"
                                    if not (schemaTypes.count(zdra_name)) == 2:
                                        decs_types.append(zdra_name)
                                        decs_types.append(zdra_name)
                                    if (eachone.lower()) not in decs_vars:
                                        decs_vars.append(eachone.lower())             
                                    if ((eachone.lower()+"'")) not in decs_vars:
                                        decs_vars.append((eachone.lower()+"'"))
                                    for (state_variables, state_types) in self.stateDeclarations:
                                        isabelleSyntax =  self.setSyntax(state_types)
                                        if "set" in isabelleSyntax:
                                            decs_vars.append(state_variables+ "'")
                                            decs_types.append(isabelleSyntax)
                                            
                        else:
                            eachone = self.cleanstring(eachone)
                            for (zdra_name, act_name) in self.nodesNnames:
                                if eachone == act_name:
                                    if ("SS" in zdra_name) and (zdra_name != "SS1"):
                                        zdra_name = "SS1"
                                    if not (schemaTypes.count(zdra_name)) == 2:
                                        decs_types.append(zdra_name)
                                        decs_types.append(zdra_name)
                                    if (eachone.lower()) not in decs_vars:
                                        decs_vars.append(eachone.lower())
                                    if ((eachone.lower()+"'")) not in decs_vars:
                                        decs_vars.append((eachone.lower()+"'"))
                        
                    for alldecs in decl:
                        if "@" not in alldecs and "|" not in alldecs and ";" not in alldecs:
                            vars = re.findall(r"\\[terms]+\{(.*?)\}", alldecs)
                            expression = re.findall(r"\\expression\{(.*?)\}", alldecs)
                            if len(vars) > 1:
                                for aVars in vars:
                                    if self.cleanstring(aVars) not in decs_vars:
                                        decs_vars.append(self.cleanstring(aVars))
                                for aTypes in expression:
                                    for i in range(len(vars)):
                                        decs_types.append(self.cleanstring(aTypes))
                            else:
                                for aVars in vars:
                                    if self.cleanstring(aVars) not in decs_vars:
                                        decs_vars.append(self.cleanstring(aVars))
                                for aTypes in expression:
                                    aTypes = self.cleanstring(aTypes)
                                    aTypes = self.setSyntax(aTypes)
                                    decs_types.append(aTypes)
                        self.schemaVarTypes.append((h, decs_types, decs_vars))
                    
 #If a schema uses another schema that is not the state then import its types and variables                   
                elif othertex:
                    DecsforSchema = []
                    VarsforSchema = []
                    for everyone in othertex:
                        everyone = self.cleanstring(everyone)
                        for (node_name, actual_name) in self.nodesNnames:
                            if actual_name in everyone:
                                if "SS" in node_name:
                                    for (stateVars, stateExp) in self.stateDeclarations:
                                        stateExp = self.setSyntax(stateExp)
                                        if "set" in stateExp:
                                            VarsforSchema.append(stateVars+ "\'")
                                            DecsforSchema.append(self.setSyntax(stateExp))
                                else:
                                    for t_n, t_t, t_v in self.schemaVarTypes:
                                        if node_name == t_n:
                                            VarsforSchema =  t_v
                                            DecsforSchema = t_t
                    for alldecs in decl:
                        vars = re.findall(r"\\[terms]+\{(.*?)\}", alldecs)
                        expression = re.findall(r"\\expression\{(.*?)\}", alldecs)
                        if len(vars) > 1:
                            for aVars in vars:
                                if self.cleanstring(aVars) not in VarsforSchema:
                                    VarsforSchema.append(self.cleanstring(aVars))
                            for aTypes in expression:
                                for i in range(len(vars)):
                                    aTypes = self.cleanstring(aTypes)
                                    aTypes = self.setSyntax(aTypes)
                                    DecsforSchema.append(aTypes)
                        else:
                            for aVars in vars:
                                aVars = self.cleanstring(aVars)
                                if aVars not in self.state_variables:
                                    if aVars not in VarsforSchema:
                                        VarsforSchema.append(aVars)
                                    for aTypes in expression:
                                        aTypes = self.cleanstring(aTypes)
                                        aTypes = self.setSyntax(aTypes)
                                        DecsforSchema.append(aTypes)
                    #Get rid of duplicates                    
                    newlist = list(set(zip(DecsforSchema, VarsforSchema)))
                    if newlist:
                        DecsforSchema, VarsforSchema = zip(*newlist)
                    self.schemaVarTypes.append((h, DecsforSchema, VarsforSchema))
                    
                    
                else:
                    newVars = []
                    newDecs = []
                    for alldecls in decl:
                        nvars = re.findall(r"\\[terms]+\{(.*?)\}", alldecls)
                        nexpression = re.findall(r"\\expression\{(.*?)\}", alldecls)
                        if len(nvars) > 1:
                            for anvars in nvars:
                                newVars.append(self.cleanstring(anvars))
                            for nTypes in nexpression:
                                for ni in range(len(nvars)):
                                    newDecs.append(self.cleanstring(nTypes))
                        else:
                            for anvars in nvars:
                                newVars.append(self.cleanstring(anvars))
                            for anTypes in nexpression:
                                newDecs.append(self.cleanstring(anTypes))
                    self.schemaVarTypes.append((h, newDecs, newVars))
                    
                
        #This adds schemas with \defs in to the set of expressions, and variables and types set
        if defs:
            for defs_a, defs_b, defs_c, defs_d, defs_e in defs:
                dexpression = re.findall(r"\\expression\{(\\[termsx]+\{.*\}( *(.*) *\\[termsx]+\{.*\})*)\}", defs_d)
                schemaTextfind = re.findall(r"\[(.*)\]", defs_d)
                allnameset = []
                setofallvartypes = []
                setofVarTypes = []
                varrs = []
                for schemaText in schemaTextfind:
                    defsVars = []
                    defsType = []
                    defs_dec = re.findall(r"\\declaration\{\\[terms]+\{(.*?)\}", schemaText)
                    defs_expression = re.findall(r": *\\expression\{(.*?)\} *\|", schemaText)
                    if defs_dec:
                        for ab in defs_dec:
                            ab = self.cleanstring(ab)
                            defsVars.append(ab)
                    if defs_expression:
                        for ab in defs_expression:
                            ab = self.cleanstring(ab)
                            defsType.append(ab)
                    self.schemaVarTypes.append((defs_a, defsType, defsVars))
                for defs_expresssion, agh, jkl in dexpression:
                    texts = re.findall(r"\{([\_a-zA-Z0-9\!\?\\]+)\}", defs_expresssion)
                    for allnames in texts:
                        allnames = self.cleanstring(allnames)
                        for zdraname, actuaname in self.nodesNnames:
                            if allnames == actuaname:
                                allnames = zdraname
                                allnameset.append(allnames)
                for sch_nam, sch_ty, sch_var in self.schemaVarTypes:
                    for ab in allnameset:
                        if ab == sch_nam:
                            setofVarTypes.append((zip(sch_ty, sch_var)))
                for ak in setofVarTypes:
                    for (ao,bo) in ak:
                        if (ao,bo) not in setofallvartypes:
                            setofallvartypes.append((ao,bo))
                sch_types = []
                sch_vars = []
                for (sch_t, sch_v) in setofallvartypes:
                    sch_types.append(sch_t)
                    sch_vars.append(sch_v)
                self.schemaVarTypes.append((defs_a, sch_types, sch_vars))
                clean_defs_expression = self.cleanstring(defs_expresssion)
                newNodeNames = self.reversTuples(self.nodesNnames)
                dictOfNames = dict(newNodeNames)
                new_expressions = self.replace_all(clean_defs_expression, dictOfNames)
                namesWithVars = dict()
                for d_name, d_type, d_var in self.schemaVarTypes:
                    if d_name in new_expressions:
                        namesWithVars[d_name] = d_name+ " " + " ".join(d_var)
                finalExpression = self.replace_all_with_brackets(new_expressions, namesWithVars)
                newsymbols = self.cleanstring(finalExpression)
                self.expressionSet.append((defs_a, newsymbols))
        

        
        #Find all global declarations within the specification, and findall datatypes in specification   
        elif globe_dec:
            for l, m in globe_dec:
                decl = re.findall(dec_comp, l)
                for eachdec in decl:
                    globe_vars = re.findall(r"\\[terms]+\{(.*?)\}", eachdec)
                    globe_expression = re.findall(r"\\expression\{(.*?)\}", eachdec) 
                    for n in globe_vars:
                        globe_vars = self.cleanstring(n)
                        for ht in globe_expression:
                            ht = self.cleanstring(ht)
                    self.globalTypesvars.append(("global", ht, globe_vars))
            #Finds all daatypes in the specification and adds its to globaltypes
                if "::=" in l:
                    l = self.cleanstring(l)
                    if "beginzed" in l:
                        q = re.sub('beginzed', '', l)
                        s = re.sub('endzed', '', q)
                        t = re.sub(':: ', '', s)
                        u = re.sub('  ', ' ', t)
                        l = 'datatype ' +(re.sub('\n', '', u))
                        m = re.sub('  ', ' ', l)
                    if l not in self.datatypes:
                        self.datatypes.append(m)


# findsall in double equals
# Adds all types and variables to schema.var.types for double equal schema
        if double_equals:
            for (name_of_line, body_of_line, k, kl) in double_equals:
                if "TS" in name_of_line:
                    body_of_line = self.cleanstring(body_of_line)
                    clean_body = self.cleanstring(body_of_line)
                    for (theNode, theName) in self.nodesNnames:
                        if theName in clean_body:
                            clean_body = clean_body.replace(theName, theNode)
                    for (name, types, vars) in self.schemaVarTypes:
                        if name in clean_body:
                            newnamee = "(" +name + " " + (" ".join(vars)) + ")"
                            clean_body = clean_body.replace(name, newnamee)
                    self.expressionSet.append((name_of_line, clean_body))
                else:
                    t_types = []
                    t_vars = []
                    setOf_v = []
                    allDaNames = []
                    allDaNamesSet = []
                    schematexts = re.findall(r"\\text\{([a-zA-Z\_\\]+)", body_of_line)
                    if schematexts:
                        for eachSchema in schematexts:
                            for zdra, actname in self.nodesNnames:
                                if eachSchema == actname:
                                    eachSchema = zdra
                                    allDaNames.append(eachSchema)
                    for s_n, s_t, s_v in self.schemaVarTypes:
                        for sn in allDaNames:
                            if sn == s_n:
                                setOf_v.append((zip(s_t, s_v)))
                    for sk in setOf_v:
                        for (ai, bi) in sk:
                            if (ai, bi) not in allDaNamesSet:
                                allDaNamesSet.append((ai, bi))
                    for (sc_t, sc_v) in allDaNamesSet:
                        t_types.append(sc_t)
                        t_vars.append(sc_v)
                        self.schemaVarTypes.append((name_of_line, t_types, t_vars))
# Adds expression to expression set for the double equals schema
                    clean_body = self.cleanstring(body_of_line)
                    for (z_name, a_name) in self.nodesNnames:
                        if a_name in clean_body:
                            clean_body = re.sub(a_name, z_name, clean_body)
                    for (svt_n, svt_t, svt_v) in self.schemaVarTypes:
                        if svt_n in clean_body:
                            new_schema_name = "(" +svt_n + " " + (" ".join(svt_v)) + ")"
                            clean_body = self.cleanstring(re.sub(svt_n, new_schema_name, clean_body))
                    self.expressionSet.append((name_of_line, clean_body))
        
        if multidefsend:
            multiexp = []
            newlist = []
            dicofnames = dict()
            for nameof, typeof, varof in self.namedSetVar():
                dicofnames[nameof] = nameof + " " + (" ".join(varof))
            for nameofdefs, actnamedefs, bodyofdefs in multidefsend:
                finalexpression = self.replace_all(bodyofdefs, dicofnames)
                self.expressionSet.append((nameofdefs, self.cleanstring(finalexpression)))
                
        return decsToPrint
  
        labelspec.close()
    
    #Creates a new set, where the first element is a name of the schema,
    #second element is the types of that schema, third element is the variables
    #of that schema
    def namedSetVar(self):
        newset = []
        for a,b in self.nodesNnames:
            for c, d, e in self.schemaVarTypes:
                if e:
                    if c == a:
                        newset.append((b, d, e))
        return newset
        
    def replace_all(self, text, dic):
        for i, j in dic.iteritems():
            text = text.replace(i, j)
        return text
    
    
    def replace_all_with_brackets(self, text, dic):
        for i, j in dic.iteritems():
            text = text.replace(i, "(" + j +")\n")
        return text
        
    def reversTuples(self, setOfTuples):
        set = []
        for (i,j) in setOfTuples:
            set.append((j,i))
        return set

    #This function replaces all the ZDRa information and labels with the ZCGa information
    def findallnodes(self, pathname):
        #Creates a set of couples with the first couple being the node and second being
        # the actual name
        labelspec = open(pathname, 'r')
        entire_document = ""
        for  each_line in labelspec:
            entire_document+=each_line
        draschema_comp = re.compile(r"(\\draschema\{([A-Z0-9]+)\}\{(.|\n)\\begin\{schema\}\{([a-zA-z0-9\_]*)\}(.|\n)*?\\end\{schema\})")
        defs1_comp = re.compile(r"(\\draschema\{([A-Z0-9]+)\}{(.|\n))(\\begin\{zed\}(.|\n)*?)([a-zA-Z0-9\_\\]+) \\defs")
        defs2_comp = re.compile(r"\\draschema\{([a-zA-Z0-9]+)\}\{([a-zA-Z0-9]+) *==(.*)((.|\n)*?)")
        multidefs_comp = re.compile(r"(\\draschema\{([a-zA-Z0-9]+)\}\{([a-zA-Z0-9\_\'\\]+) *\\defs((.|\n)*?)}) \\")
        draschema = draschema_comp.findall(entire_document);
        defs1 = defs1_comp.findall(entire_document);
        defs2 = defs2_comp.findall(entire_document);
        multidefs = multidefs_comp.findall(entire_document);
        self.nodesNnames1 = []
        self.nodesNnames2 = []
        for a, b, c, d, e in multidefs:
            self.nodesNnames.append((b, c))
        for a, b, c, d, e in draschema:
            self.allnodes.append(b)
            d = self.cleanstring(d)
            self.nodesNnames.append((b,d))
        for h, i, j, k, l, m in defs1:
            if (i, m) not in self.nodesNnames:
                m = self.cleanstring(m)
                self.nodesNnames.append((i, m))
        for n, o, p, q, r in defs2:
            o = self.cleanstring(o)
            self.nodesNnames.append((n, o))
        
        #Creates a set with all the nodes and their types                
        schemacomp = re.compile(r"\\draschema{([a-zA-Z0-9]+)}")
        linecomp = re.compile(r"\\draline{([a-zA-Z0-9]+)}")
        for z in labelspec:
            schema = schemacomp.search(z)
            line = linecomp.search(z)
            if schema:
                self.allnodes.append((schema.group(1), "draschema"))
            if line:
                self.allnodes.append((line.group(1), "draline"))
        labelspec.close()
    

    
    def replace(self, file_path, pattern, subst):
        #Create temp file
        fh, abs_path = mkstemp()
        with open(abs_path,'w') as new_file:
            with open(file_path) as old_file:
                for line in old_file:
                    new_file.write(line.replace(pattern, subst))
        close(fh)
    #Remove original file
        remove(file_path)
    #Move new file
        move(abs_path, file_path)
                
    
    def replacea(self, file_path, pattern, subst):
        pass
        
    
    def setSyntax(self, string):
        if "power" in string:
            string = string.replace("power", "")
            string = string + " set"
        if "pfun" in string:
            string = string.replace("pfun", "*")
            string = "(" + string + ")" + " set"
        if "rel" in string:
            string = string.replace("rel", "*")
            string = "(" + string + ")" + " set"
        if "iseq" in string:
            string = string.replace("iseq", "")
            string = string + " list"

        return string
    
    def fillinIsa(self, zcgazdra, isaskel):
        allStateinvarients = []
        self.findNewTypes(zcgazdra)
        entire_document = ""
        definition_comp = re.compile(r"((definition *([a-zA-Z\_0-9]+) *:: *(.|\n)*?)\(\*TYPES\*\)( *=> *bool))")
        Openskel = open(isaskel, "r+")
        self.findallnodes(zcgazdra)
        self.nodesNnames = list(set(self.nodesNnames))
        setofdecs = self.find_zcga_info(zcgazdra)
        recordset = []
        if self.newtypes:
            for eachType in self.newtypes:
                newAddedType = ("typedecl " + eachType + "\n")
                if newAddedType not in recordset:
                    recordset.append(newAddedType)
        if self.datatypes:
            for eachdatatype in self.datatypes:
                if eachdatatype not in recordset:
                    recordset.append(eachdatatype)
        for each_line in Openskel:
            entire_document+=each_line
            defin = definition_comp.findall(entire_document);
            if "record" in each_line:
                if recordset:
                    recordline = "".join(recordset) + "\n\n" +each_line
                    if recordline not in entire_document:
                        self.replace(isaskel, each_line, recordline)

            if "SS" in each_line and "TYPES" in each_line:
                typeLine = []
                for theVar, theType in self.stateDeclarations:
                    typeLine.append(theType)
                lineOfTypes = " => ".join(typeLine)
                boolindex = each_line.index(" => bool")
                newline = "\" " + lineOfTypes + each_line[boolindex:]
                self.replace(isaskel, each_line, newline)

            elif "(*DECLARATIONS*)" in each_line and self.stateDeclarations:
                statedecs = []
                for (var, v_type) in self.stateDeclarations:
                    v_type = self.setSyntax(v_type)
                    if ("set" in v_type) or ("list" in v_type) or ("Range" in v_type) or ("Domain" in v_type):
                        v_type = "\"" + v_type + "\""
                    newStateDec =  var.upper() + " :: " + v_type + "\n"
                    if newStateDec not in statedecs:
                        statedecs.append(newStateDec)
                joinStateDecs = "".join(statedecs)
                self.replace(isaskel, each_line, joinStateDecs)
            if "(*GLOBAL DECLARATIONS*)" in each_line and self.globalTypesvars:
                SetOfGlobeDecs = []
                for (var_a, var_b, var_c) in self.globalTypesvars:
                    globeDecs = var_c + " :: " + var_b + "\n"
                    if globeDecs not in SetOfGlobeDecs:
                        SetOfGlobeDecs.append(globeDecs)
                for (vari, types) in self.stateDeclarations:
                    convertToIsa = self.setSyntax(types)
                    if "set" in convertToIsa:
                        new_state_dec = vari + " :: " + "\"" +convertToIsa + "\"\n"
                    else:
                        new_state_dec = vari + " :: "  +convertToIsa + "\n"
                    SetOfGlobeDecs.append(new_state_dec)
                newGlobeDecs = "and ".join(SetOfGlobeDecs)
                self.replace(isaskel, "(*GLOBAL DECLARATIONS*)"  , newGlobeDecs)
            elif "(*GLOBAL DECLARATIONS*)" in each_line and not self.globalTypesvars:
                fixes_declarations = []
                if self.stateDeclarations:
                    for (vari, types) in self.stateDeclarations:
                        convertToIsa = self.setSyntax(types)
                        new_state_dec = vari + " :: " + "\"" +convertToIsa + "\"\n"
                        fixes_declarations.append(new_state_dec)
                newFixesLine = "fixes " + ("and ".join(fixes_declarations))
                self.replace(isaskel, each_line, newFixesLine)
            if "assumes SI" in each_line and self.stateInvarients:
                for (si_number, si_expression) in self.stateInvarients:
                    if si_expression not in allStateinvarients:
                        allStateinvarients.append("\"" +si_expression+ "\"")
                newSiline = " \n and ".join(allStateinvarients)
                newSiline = "assumes " + newSiline + "\n"
                self.replace(isaskel, each_line, newSiline)
                                                  
            elif "(*GLOBAL DECLARATIONS*)" in each_line:
                self.replace(isaskel, each_line , "\n")               
            if "TYPES" in each_line:
                for var_a, var_b, var_c in self.schemaVarTypes:
                    types_line = "(*"+var_a+"_TYPES*)"
                    if types_line in each_line:
                        if var_b:
                            new_types_line = " => ".join(var_b)
                            self.replace(isaskel, types_line, new_types_line)
                        else:
                            arrowindex = each_line.index("=>")
                            replaceThis = each_line[:arrowindex + 2]
                            self.replace(isaskel, replaceThis, "\"")
            elif "VARIABLES" in each_line:
                for var_a, var_b, var_c in self.schemaVarTypes:
                    variable_line = "(*"+var_a+"_VARIABLES*)"
                    if variable_line in each_line:
                        new_variable_line = " ".join(var_c)
                        self.replace(isaskel, variable_line, new_variable_line)          
                
            #add expressions to skeleton
            if ("(*PRECONDITION*)" in each_line) or ("(*EXPRESSION*)" in each_line):
                for (exprs_a, expres_b) in self.expressionSet:
                    if (exprs_a in each_line) and ("(*PRECONDITION*)" in each_line):
                        equalindex = each_line.index("=")
                        firsthalf = each_line[:equalindex+1]
                        newstring = firsthalf + " (" + expres_b + ") \"\n"
                        self.replace(isaskel, each_line, newstring)
                        
                    elif(exprs_a in each_line) and ("(*EXPRESSION*)" in each_line):
                        equalindex = each_line.index("=")
                        firsthalf = each_line[:equalindex+1]
                        newstring = firsthalf + " (\n" + expres_b + ") \"\n"
                        self.replace(isaskel, each_line, newstring)
            
            #this part fills in the lemmas for the totalsing schemas
            elif "EXPRESSION" in each_line:
                for (expres_name, expres_line) in self.expressionSet:
                    toReplace = "(*"+expres_name+"_EXPRESSION*)"
                    if toReplace in each_line:
                        self.replace(isaskel, toReplace, expres_line)
            
            for (po_name, po_expression) in self.postcondition:
                if po_name in each_line:
                    allPoExp = []
                    for alPoExpressions in po_expression:
                        allPoExp.append("(" + alPoExpressions + ")")
                    newPo ="(\n"+(" \n\<and> ".join(allPoExp)) + ")"
                    newPo = self.expressionSyntax(newPo)
                    self.replace(isaskel, po_name, newPo)

            
        Openskel.close()

        return zcgazdra, isaskel
    
    #This function changes the syntax for tuple sets which are 
    #applied to somethign for example "date = birthday~name"
    def expressionSyntax(self, expression):
        if "~" in expression and "=" in expression:
            tildaIndex = expression.index("~")
            if "(" == expression[tildaIndex + 1]:
                closindex = expression.index(")")
                application = expression[tildaIndex + 2: closindex]
                expression = re.sub(application, "", expression)
                expression = re.sub("\~\(\)", "", expression)
                expression = re.sub(" =", ", "+application+ " \<in>", expression)
                for  fulltuple, a, b in re.findall("(([\_A-Za-z0-9]+), ([\_A-Za-z0-9]+))", expression):
                    oldtuple = fulltuple
                    newtuple = b + ", " + a
                expression = re.sub(oldtuple, "(" + newtuple + ")", expression)
            return expression
        else:
            return expression
    
    
    def fillInNames(self, isaskel):
        sorteda = []
        Openskel = open(isaskel, "r+")
        for each_line in Openskel:
            for a, b in self.nodesNnames:
                if a not in sorteda:
                    sorteda.append(a)
                abc = (sorted(sorteda, key=self.alphanum_key))[::-1]
        for k in abc:
            for j, l in self.nodesNnames:
                if k ==j:
                    self.newtpleset.append((k, l))
        Openskel.close()
        return self.newtpleset
        
    def fillNames(self, isaskel):
        self.fillInNames(isaskel)
        Openskel = open(isaskel, "r+")
        for each_line in Openskel:
            for (draname, actname) in self.newtpleset:
                if draname in each_line:
                    self.replace(isaskel, draname, actname)
        Openskel.close()
        
    def tryint(self, s):
        try:
            return int(s)
        except:
            return s
     
    def alphanum_key(self, s):
        return [ self.tryint(c) for c in re.split('([0-9]+)', s) ]
    
    
x = fillIn()

#TheLabeledSpec= ("/home/lb89/workspace/zdra/curries/zml_clubstate.tex")
#TheIsaSkel = ("/home/lb89/workspace/zdra/curries/gpsazml_clubstate.thy")

#TheLabeledSpec= ("/home/jeff/lavinias_workspace/zdra/curries/zml_clubstate2.tex")
#TheIsaSkel = ("/home/jeff/lavinias_workspace/zdra/curries/gpsazml_clubstate2.thy")

##########
#Create IsaSkeleton to use without interface
#zdracheck.totalcheck(TheLabeledSpec)
#zdracheck.createskeleton_set()
#createIsaskel(TheLabeledSpec)

#########

#x.fillinIsa(TheLabeledSpec, TheIsaSkel)
#x.fillinIsa(TheLabeledSpec, TheIsaSkel)
#x.fillNames(TheIsaSkel)