'''
Created on 11 Jun 2015
@author: lb89
'''

import re
#import zdracheck

#The set of all totalised preconditions
totalisedPre = []

#All preconditions that exist
precon = {}

#All preconditions which have not been totalised
nontoalised = {}

#This function checks if all preconditioins have been totalised
def totalcheck(document):
    totalise_comp = re.compile(r"\\totalises\{([a-zA-Z0-9]*)\}\{([a-zA-Z0-9]*)\}")
    uses_comp = re.compile(r"\\uses\{([a-zA-Z0-9]*)\}\{([a-zA-Z0-9]*)\}")
    draline_comp = re.compile(r"\\draline\{(PRE[0-9]*)\}")
    draschema_comp = re.compile(r"(\\draschema\{(PRE[0-9]*)\}\{(.|\n)*?\\end\{schema\}\})")
    entire_document = ""
    for  each_line in document:
        entire_document+=each_line
        totalise_op = totalise_comp.search(each_line)
        draline = draline_comp.search(each_line)
        uses_op = uses_comp.search(each_line)
#If precondiotions is in a line then save the number of the preconditions
        if totalise_op:
            totalpre = totalise_op.group(2)
            totalisedPre.append(totalpre)
        if uses_op:
            usedpre = uses_op.group(2)
            totalisedPre.append(usedpre)
        if draline:
            zdraPre = draline.group(1)
            precon[zdraPre] = each_line
#Check preconditions as entire precondition schemas
    draschema = draschema_comp.findall(entire_document);
    for i in draschema:
        entire_schema = (i[0]+"\n")
        for x, y, z in draschema:
            if y not in precon:
                precon[y] = x
            
#If the precondition has been totalised then add it to the set of totalised preconditions
#If a precondition has not been totalised 
    for a in precon.keys():
        if a not in totalisedPre:
            nontoalised[a] = precon[a]
    if nontoalised:
        return "Warning! Specification not correctly totalised \n"
        #checkfortotalising(document, proofskeleton)
    else:
        return "Specification Correctly Totalised \n"
        #return ("\n Specification correctly totalised")

        
def findgpsa(somestring):
    if "/" in somestring:
        indexsofslash = [i for i, ltr in enumerate(somestring) if ltr == "/"]
        indexsofdot = [i for i, ltr in enumerate(somestring) if ltr == "."]
        lastindexslash = max(indexsofslash)
        lastindexdot = max(indexsofdot)
        mainName = somestring[lastindexslash + 1:lastindexdot]
        gpsaDirectory = somestring[:lastindexslash + 1]
        someothername = gpsaDirectory + "gpsa" + mainName +".doc"
        newname = someothername
    else:
        newname = "gpsa" +somestring+".doc"
    return newname

def findisagpsa(somestring):
    if "/" in somestring:
        indexsofslash = [i for i, ltr in enumerate(somestring) if ltr == "/"]
        indexsofdot = [i for i, ltr in enumerate(somestring) if ltr == "."]
        lastindexslash = max(indexsofslash)
        lastindexdot = max(indexsofdot)
        mainName = somestring[lastindexslash + 1:lastindexdot]
        gpsaDirectory = somestring[:lastindexslash + 1]
        someothername = gpsaDirectory + "gpsa" + mainName +".thy"
        newname = someothername
    else:
        newname = "gpsa" +somestring+".thy"
    return newname

def find_dp_name(somestring):
    if "/" in somestring:
        indexsofslash = [i for i, ltr in enumerate(somestring) if ltr == "/"]
        indexsofdot = [i for i, ltr in enumerate(somestring) if ltr == "."]
        lastindexslash = max(indexsofslash)
        lastindexdot = max(indexsofdot)
        mainName = somestring[lastindexslash + 1:lastindexdot]
        gpsaDirectory = somestring[:lastindexslash + 1]
        someothername = gpsaDirectory + "dp_" + mainName +".png"
        newname = someothername
    else:
        newname = "dp_" +somestring+".png"
    return newname

def find_goto_name(somestring):
    if "/" in somestring:
        indexsofslash = [i for i, ltr in enumerate(somestring) if ltr == "/"]
        indexsofdot = [i for i, ltr in enumerate(somestring) if ltr == "."]
        lastindexslash = max(indexsofslash)
        lastindexdot = max(indexsofdot)
        mainName = somestring[lastindexslash + 1:lastindexdot]
        gpsaDirectory = somestring[:lastindexslash + 1]
        someothername = gpsaDirectory + "goto_" + mainName +".png"
        newname = someothername
    else:
        newname = "goto_" +somestring+".png"
    return newname

    
    