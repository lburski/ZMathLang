'''
Created on 5 May 2015

@author: lb89
'''
import re
import totalise
import networkx as nx
import matplotlib.pyplot as plt
from networkx.algorithms.cycles import cycle_basis, simple_cycles
from networkx.drawing.nx_agraph import graphviz_layout
import pylab
from networkx.drawing.layout import _rescale_layout

someset = []
goto_graph = nx.DiGraph()
dep_graph = nx.DiGraph()
isthereloops = 0
goto_edges = dict()
dep_edges = dict()
orderofgraph = []
allnodesandtypes = []
allNodesInGraph = []
gotoName = ""
depName = ""

def totalcheck(somedoc):
    global isthereloops

    toCheck = open(somedoc, "r")

    uses_comp = re.compile(r"\uses{([a-zA-Z0-9]+)}{([a-zA-Z0-9]+)}")
    initial_comp = re.compile(r"\initialof{([a-zA-Z0-9]+)}{([a-zA-Z0-9]+)}")
    allows_comp = re.compile(r"\\allows{([a-zA-Z0-9]+)}{([a-zA-Z0-9]+)}")
    requires_comp = re.compile(r"\\requires{([a-zA-Z0-9]+)}{([a-zA-Z0-9]+)}")
    total_comp = re.compile(r"\\totalises{([a-zA-Z0-9]+)}{([a-zA-Z0-9]+)}")
    draline_comp = re.compile(r"\\draline{([a-zA-Z0-9]+)}")
    draschema_comp = re.compile(r"\\draschema{([a-zA-Z0-9]+)}")
    for eachline in toCheck:
    #Check if there are any totalising schemas
        uses = uses_comp.search(eachline)
        initialof = initial_comp.search(eachline)
        allows = allows_comp.search(eachline)
        requires = requires_comp.search(eachline)
        total = total_comp.search(eachline)
        draline = draline_comp.search(eachline)
        draschema = draschema_comp.search(eachline)
        if draline:
            dep_graph.add_node(draline.group(1))
            goto_graph.add_node(draline.group(1))
        elif draschema:
            dep_graph.add_node(draschema.group(1))
            goto_graph.add_node(draschema.group(1))
#Gets all of the nodes and put's it in the graph
        if initialof:
            dranode = initialof.group(2)
            drachild = initialof.group(1)
            #Adds to the dependency graph
            dep_graph.add_edge(drachild, dranode)
            dep_edges[(drachild, dranode)] = "initialOf"
            #Adds to the goTograph
            goto_graph.add_edge(dranode, drachild)
            goto_edges[(dranode, drachild)] = "initialOf"
        if uses:
            dranode = uses.group(2)
            drachild = uses.group(1)
            #Adds to the dependency graph
            dep_graph.add_edge(drachild, dranode)
            dep_edges[(drachild, dranode)] = "uses"
            #Adds to the goTograph
            goto_graph.add_edge(dranode, drachild)
            goto_edges[(dranode, drachild)] = "uses"
        if allows:
            dranode = allows.group(1)
            drachild = allows.group(2)
            #Adds to the dependency graph
            dep_graph.add_edge(dranode, drachild)
            dep_edges[(dranode, drachild)] = "allows"
            #Adds to the goTograph
            goto_graph.add_edge(dranode, drachild)
            goto_edges[(dranode, drachild)] = "allows"
        if requires:
            dranode = requires.group(1)
            drachild = requires.group(2)
            #Adds to the dependency graph
            dep_graph.add_edge(drachild, dranode)
            dep_edges[(drachild, dranode)] = "requires"
            #Adds to the goTograph           
            goto_graph.add_edge(dranode, drachild)
            goto_edges[(dranode, drachild)] = "requires"
        if total:
            dranode = total.group(2)
            drachild = total.group(1)
            #Adds to the dependency graph
            dep_graph.add_edge(drachild, dranode)      
            dep_edges[(drachild, dranode) ] = "totalises"    
            #Adds to the goTograph             
            goto_graph.add_edge(dranode, drachild)
            goto_edges[(dranode, drachild)] = "totalises"
    
    #Check if specification is correctly totalised
    toCheckforTotalise = open(somedoc, "r")
    someset.append(totalise.totalcheck(toCheckforTotalise))
    toCheckforTotalise.close() 
    
    #list of loops shows all the loop paths within the graph
    listofloops = list(nx.simple_cycles(goto_graph))

    if listofloops:
        isthereloops = isthereloops + 1
        someset.append("Error! Circular Reasoning: \n")
        someset.append( "Path of loop: " + str(listofloops) +  " \n")
    else:
        someset.append("Specification is Rhetorically Correct\n")
    toCheck.close()

#find the name of the theory so it can be added to the title of the graphs    
def findtheory(somedoc):
    toCheck = open(somedoc, "r")
    theory_comp = re.compile(r"\\dratheory{([a-zA-Z0-9]+)}")
    for each_line in toCheck:
        theoryName = theory_comp.search(each_line)
        if theoryName:
            return theoryName.group(1)
    toCheck.close()
    
    #Created the dependency graph and names in path+ specname    
def createplot(somedoc):
    newname = "goto_" + creatname(somedoc) +".png"
    #draws the dependency graph
    pos=nx.graphviz_layout(goto_graph,prog='dot')
    nx.draw_networkx_edge_labels(goto_graph, pos, goto_edges, font_size=7)
    nx.draw(goto_graph, pos, node_size = 250, node_color = '#FFC0FF', arrows=True, with_labels=True, font_size=7)
    #nx.draw_networkx(goto_graph, node_size = 999, node_color = 'm', arrows=True)
    plt.title('GoTo graph of ' + findtheory(somedoc) )
    plt.axis('off')
    plt.savefig(newname)
    plt.close()
    return plt

def showplot(someplot):
    someplot.show()

def creatdepgraphplot(somedoc):
    newname = "dp_" + creatname(somedoc) +".png"
    #draws the dependency graph
    pos=nx.graphviz_layout(dep_graph, prog='fdp')
    nx.draw_networkx_edge_labels(dep_graph, pos, dep_edges, font_size=7)
    nx.draw(dep_graph, pos, node_size = 250, node_color = '#A0CBE2', arrows=True, with_labels=True, font_size=7)
    A = nx.to_agraph(dep_graph)
    A.edge_attr.update(len=5)
    A.layout()
    A.draw(newname)

    plt.figure(1,figsize=(2000,2000))
    plt.savefig(newname, dpi = 1000)
    plt.show()
    #plt.title('Dependency Graph of ' + findtheory(somedoc) )
    #plt.axis('off')
    #plt.savefig(newname)
    #plt.close()
    return plt

def dependencygraph():
    return goto_graph
    
def creatname(doctoconvert):
    if "/" in doctoconvert:
        indexsofslash = [i for i, ltr in enumerate(doctoconvert) if ltr == "/"]
        indexsofdot = [i for i, ltr in enumerate(doctoconvert) if ltr == "."]
        lastindexslash = max(indexsofslash)
        lastindexdot = max(indexsofdot)
        someothername = doctoconvert[lastindexslash + 1:lastindexdot] 
        newname = someothername
    elif "." in doctoconvert:
        indexsofdot = [i for i, ltr in enumerate(doctoconvert) if ltr == "."]
        lastindexdot = max(indexsofdot)
        newname = doctoconvert[:lastindexdot]
    else:
        newname = doctoconvert  
    return newname

def printoutput():
    outputmessage = "".join(someset)
    return outputmessage

def appendtoset(k, someset):
    if k not in someset:
        someset.append(k)
        
def isthereanyloops():
    if isthereloops:
        return True
    else:
        return False
    
def hasNumbers(inputString):
    return re.findall(r'\d', inputString)


                    
    
#This function uses the GoTo graph to create a ProofSketch for the given schema
def createskeleton_set():
    fromnodes = []
    tonodes = []
    numbersInNopdes = []
    numbers_in_nodes = []
    CSset = []
#If a node is dependent on something add it to the set fromnodes
#if a node has a dependency add it to the set tonodes
    for a,b  in dependencygraph().edges():
        tonodes.append(b)
        fromnodes.append(a)
    allNodesInGraph = list(set(dependencygraph().nodes()))
    allNodesInGraph = sorted(allNodesInGraph)
    #print dependencygraph().edges()
#The order of the graph will start with all the nodes which are not
#dependent on anything
    

    for allnodes in fromnodes:
        if allnodes not in tonodes:
            if ("SS1" in allnodes) and (allnodes not in orderofgraph):
                orderofgraph.append(allnodes)
            else:
                numberinNode = hasNumbers(allnodes)
                if numberinNode:
                    for eachNumber in numberinNode:
                        numbersInNopdes.append((eachNumber, allnodes))
    for (TheNumber, theNode) in sorted(numbersInNopdes):
        if theNode not in orderofgraph:
            if "DA" in theNode:
                pass
            elif "SS1" in theNode or "A" in theNode:
                orderofgraph.append(theNode)
            
#Remove the nodes which are not dependent on anything from the
#set of all nodes
    for thenodes in allNodesInGraph:
        if thenodes in orderofgraph:
            allNodesInGraph.remove(thenodes)
        
            
#Loops through all the nodes, if the nodes parents are printed in
#orderofgraph then add the node to the order and remove from the set
#of all nodes
    while allNodesInGraph:
        for gfd in orderofgraph:
            if gfd in allNodesInGraph:
                allNodesInGraph.remove(gfd)
        for k in set(allNodesInGraph):
            l = set(goto_graph.predecessors(k))
            if l.issubset(set(orderofgraph)):
                for (c, d) in goto_edges:
                    if (goto_edges[(c, d)] == "initialOf") and (c in orderofgraph):
                        appendtoset(d, orderofgraph)
                        if d in allNodesInGraph:
                            allNodesInGraph.remove(d)
                    elif (goto_edges[(c, d)] == "requires") and (c in orderofgraph):
                        appendtoset(d, orderofgraph)
                        if d in allNodesInGraph:
                            allNodesInGraph.remove(d)
                    else:
                        appendtoset(k, orderofgraph)
                        if k.startswith("CS"):
                            appendtoset(k, CSset)
                        for CSnode in CSset:
                            Number_in_node = hasNumbers(CSnode)
                            for each_number in Number_in_node:
                                appendtoset((each_number, CSnode), numbers_in_nodes)
                        for (the_number, the_node) in sorted(numbers_in_nodes):
                            appendtoset(the_node, orderofgraph)
                        if k in allNodesInGraph:
                            allNodesInGraph.remove(k)
    #print sorted(numbers_in_nodes)
                
    for eachpart in orderofgraph:
        indexofnode = orderofgraph.index(eachpart)
        if "SS" in eachpart:
            orderofgraph[indexofnode] = (eachpart, "stateSchema")
        elif "OS" in eachpart:
            orderofgraph[indexofnode] = (eachpart, "outputSchema")
        elif "PO" in eachpart:
            orderofgraph[indexofnode] = (eachpart, "postcondition")
        elif "O" in eachpart:
            orderofgraph[indexofnode] = (eachpart, "output")
        elif "PRE" in eachpart:
            orderofgraph[indexofnode] = (eachpart, "precondition")
        elif "IS" in eachpart:
            orderofgraph[indexofnode] = (eachpart, "initialSchema")
        elif "CS" in eachpart:
            orderofgraph[indexofnode] = (eachpart, "changeSchema")
        elif "TS" in eachpart:
            orderofgraph[indexofnode] = (eachpart, "lemma")
        elif "SI" in eachpart:
            orderofgraph[indexofnode] = (eachpart, "stateInvarients")
        elif "DA" in eachpart:
            orderofgraph[indexofnode] = (eachpart, "defintionAxiom")
        elif "A" in eachpart:
            orderofgraph[indexofnode] = (eachpart, "axiom")
    return orderofgraph

#This function creates the txt file in which to hold the proof skeleton
def createskeleton(somedoc):
    createskeleton_set()
                   
    ProofSkeleton = open(findskeleton(somedoc), "w")
    
    for thenode, thename in orderofgraph:
        ProofSkeleton.write(thename + " " + thenode + " \n\n")
    ProofSkeleton.close()

    return ProofSkeleton

def findskeleton(somestring):
    if "/" in somestring:
        indexsofslash = [i for i, ltr in enumerate(somestring) if ltr == "/"]
        indexsofdot = [i for i, ltr in enumerate(somestring) if ltr == "."]
        lastindexslash = max(indexsofslash)
        lastindexdot = max(indexsofdot)
        mainName = somestring[lastindexslash + 1:lastindexdot]
        gpsaDirectory = somestring[:lastindexslash + 1]
        someothername = gpsaDirectory + "skeleton_" + mainName +".txt"
        newname = someothername
    else:
        newname = "skeleton_" +somestring+".txt"
    return newname

#somedoc = "fullexample.tex"
#somedoc = "text.tex"

somedoc= ("/home/lb89/workspace/zdra/1n2.tex")
totalcheck(somedoc)
creatdepgraphplot(somedoc)
#createplot(somedoc)
#print creatname(somedoc)
#print createskeleton_set()
