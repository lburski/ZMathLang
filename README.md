======================================================================
\zmathlang
This is the README file for Z-MathLang 
Authors: Lavinia Burski

This folder contains:
1) "README" This current file
2) "zcga.py" The python zcga type checking program
3) "zmathlang.sty" The style file needed to label Latex Z Specification
4) "zed.sty" The style file needed to draw the specifications when latex
	is compiled
5) "totalise.py" The python program which checks if the specification has
	been correctly totalised.
6) "zdra.py" The python program which generates the proof skeleton for 
	Isabelle/Hol and fills it in.
7) "zdracheck.py" The python program which checks for loops in the reasoning
	and produces the dependency graphs.
8) "interface.py" The python program which brings all the ZDRa modules
	together into a user friendly interface.
9) "Examples" This directory contains a set of examples which have been
	translated from LaTeX specification to Isabelle syntax using the
	MathLang steps.
======================================================================
NOTE: The python program, examples and style files must all be in the 
same directory you are working in.
ZCGa

The ZCGa is a weak type checker for Z-specifications written in latex
format. Knowledge of some Latex is assumed.

1. WHAT YOU WILL NEED
a) Latex
b) Python 2.*

2. WHAT YOU DO
You can either create your own Z-Specification and label it in ZCGa or
practice on any of the existing ones contained in this folder. If 
creating your own please read a) and b). If practicing on existing then
please go straight to c).

Please refer to: "https://spivey.oriel.ox.ac.uk/mike/fuzz/refcard.pdf"
to write the zed specifications.

Please use zmathlang.sty when writing your own specifications as this 
package already calls upon zed.sty.

a) Once the specification is written up then you may annotate it using
the commands found in "zmathlang.sty". These are:

"\set{...}" for sets
"\term{...}" for terms
"\expression{...}" for expressions
"\declaration{...}" for declarations
"\text{....}" for schematext
"\definition{...}" for definitions
"\specification{...}" if using more than 1 specification in a document.

An example of a declaration is "birthday : NAME \pfun DATE". The 
ZCGa annotation for this would be 
\declaration{\set{birthday} : \expression{NAME \pfun DATE}}

Schema text only annotates the declarations, expressions 
and definitions.

For fully annotated example please refer to the examples found in this 
directory.

b) Once the specification has been fully annotated, one may compile
the document using pdflatex. Note the colours now appear around each 
part of the specification. The output clarifies the different 
grammatical parts and is now ready to be type checked by the 
automated type checker.

c) Open up a terminal and run the program by inputting "python zcga.py".
The program will then ask which specification to be checked. Type in 
the specification including the whole extention. An example of this 
would be to input "zcga_tea.tex".

The program will then output if the specification is correct or not
and if its not it will output any errors.

======================================================================

======================================================================
ZDRa

The ZDRa is a checks Z-specifications written in latex format for 
Rhetorical Correctness. Knowledge of some Latex is assumed.

1. WHAT YOU WILL NEED
a) Latex
b) Python 2.*
c) Python Package NetworkX installed
d) Python Package TkInter installed

2. WHAT YOU DO
You can either create your own Z-Specification and label it in ZDRa or
practice on any of the existing ones contained in this folder. If 
creating your own please read a) and b) and c). If practicing on existing then
please go straight to d).

Please refer to: "https://spivey.oriel.ox.ac.uk/mike/fuzz/refcard.pdf"
to write the zed specifications.

Please use zmathlang.sty when writing your own specifications as this 
package already calls upon zed.sty and ZCGa.sty

a) Once the specification is written up then you may annotate it using
the commands found in "zdra.sty". These are:

"\dratheory{T#}{scaleoftheory}{...}"

"\draline{L#}{...}" for lemmas

"\draschema{SS#}}{...}" for state schemas

"\draschema{IS#}{...}" for initialising schemas

"\draschema{CS#}{...}" for schemas that change the state

"\draschema{OS#}{...}" for schemas that give an output

"\draschema{TS#}{...}" for totalising schemas

"\draschema{A#}{...}" for axiomatic definitions

\draline{SI#}{...}" for state invariants

"\draline{PRE#}{...}" for preconditions

"\draline{PO#}{...}" for postconditions

"\draline{O#}{...}" for outputs

Where "#" is a number and {...} is where you put the instance. In the
dratheory the specification is sometimes to large to fit onto one page
therefore it usually need to be scaled down which is why there is an
extra argument (scaleoftheory) in which a number between 0 and 1 has to
be added.

For example if we take the precondition "name? \notin known" It would
be labeled in ZDRa as "\draline{PRE1}{name? \notin known}"

b) When the instances are labeled one must then add the relationships
between them anywhere before end of document using the following:

"\initialOf{instance1}{\instance2}" for a schema being initial of 
another

"\uses{instance1}{\instance2}" if a schema uses another

"\requires{instance1}{\instance2}" if a schema requires another

"\allows{instance1}{\instance2}" if a precondition allows something to 
happen.

For example, we have the precondition 
"\draline{PRE1}{name? \notin known}" which allows 
"\draline{PO3}{birthday' = birthday \cup \{name? \mapsto date?\}}"
We can then add the relationship \allows{PRE1}{PO3} to the document.

Please look at the examples which have already been annotated with zdra
to get a better understanding.

c) Once the specification has been fully annotated, one may compile
the document using pdflatex. Now the boxes appear around chunks of the
specification and the arrows show the relationships. The document
is now ready to be checked with the type checker.

d) Open up a terminal and run the program by inputting "python interface.py".
The program will then show the zdra interface. You may now click on file and
then open in the top left corner. An example of this would be 
to input "zdra_tea.tex". Then you may click on "ZDRa" and "ZDRa check"

The program will then output if the specification is rhetorically 
correct or not and will give a warning if it has not been totalised.
In the top right box called "Messages"

It will also create 2 different files:
1) Dependency Graph
This graph shows the relationships you have annotated the specification in.
A graph version of all the relationships.

2)GoTo Graph
This is a graph showing which instances are dependent on other instances.

After the ZDRa check you may now create 2 different types of proof skeletons.

1) General Proof Skeleton
This is a plain txt file which uses the GoTo graph and outputs the order
of the graph which is created.

2) Isabelle Proof Skeleton
This uses the GoTo graph to create a Isabelle skeleton which is an outline
if one wishes to prove the specification in Isabelle.

To fill in the Isabelle skeleton,  you may now click on the GPSa button in 
the top menu and scroll down and click FillInIsaSkeleton. This will then
fill in the entire skeleton with the ZCGa information available.
Note the file must be labeled with ZCGa and ZDRa annotations for the skeleton
to be filled in correctly.


