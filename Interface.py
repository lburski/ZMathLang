
'''
Created on 17 Jun 2015

@author: lb89
'''
from Tkinter import *
import Tkinter as tk
import tkFileDialog
import tkMessageBox
from ScrolledText import *
import zdracheck
import zdra
import totalise
import os.path
#from PIL import *
import zcga
import re
import os
from os import path
import sys
import subprocess
import tempfile
import shutil
import json
global radioVar
global theoryC
global stateSchC
global initSchC                
global changeSchC
global outputSchC
global totaliseC
global axiomC
global stateInvC
global preconC
global postconC
global outputC
global checkValue #needed for right-click menu (diappearing too fast in Linux, see killClicker fn)
checkValue=0 
def combine_funcs(*funcs):
    def combined_func(*args, **kwargs):
        for f in funcs:
            f(*args, **kwargs)
        return combined_func
 
class Example(Frame):
    global master
    global toolbarZ
    global toolbarZcga
    global toolbarZdra

    def __init__(self, master):
        Frame.__init__(self,master)
        self.master = master
        self.initUI()
            

    def initUI(self):
        global radioVar
        global m1
        global master
        self.master.title("Z Specification")
        self.pack(fill=BOTH, expand=1, side=LEFT)             
        m1 = PanedWindow(self.master,width=600)
        m1.pack(fill=BOTH, expand=1)
        
        scrollbar = Scrollbar(self)
        scrollbar.pack( side = RIGHT, fill=Y )
        menubar = Menu(self.master)
        self.master.config(menu=menubar)
        fileMenu = Menu(menubar)
        editMenu=Menu(menubar)
        zedMenu = Menu(menubar)
        zcgaMenu = Menu(menubar)
        zdraMenu = Menu(menubar)
        gpsaMenu = Menu(menubar)
        fileMenu.add_command(label="New",command=self.newFile)
        fileMenu.add_command(label="Open", command=self.onOpen)
        fileMenu.add_command(label="Save", command=self.saveMenu)
        fileMenu.add_command(label="Save As", command=self.save_asMenu)
        fileMenu.add_command(label="Exit",command=self.exitMenu)
        editMenu.add_command(label="Undo          Ctrl+Z", command=self.undo)
        editMenu.add_command(label="Redo           Ctrl+Y", command=self.redo)
        editMenu.add_command(label="Cut              Ctrl+X", command=self.cut)
        editMenu.add_command(label="Copy           Ctrl+C", command=self.copy)
        editMenu.add_command(label="Paste           Ctrl+V", command=self.paste)
        editMenu.add_command(label="Search         Ctrl+F", command=self.searchWindowMenu)
        editMenu.add_command(label="Select All     Ctrl+A", command=self.select_all_menu)
        zedMenu.add_command(label="Generate a Z PDF",command=self.zedPdfCheck)
        zcgaMenu.add_command(label = "ZCGa Check", command=self.zcgacheckMenu)
        zcgaMenu.add_command(label = "ZCGa Check and PDF", command=self.checkAndPdf) 
        zdraMenu.add_command(label = "ZDRa Check", command=self.zdracheck)
        #zdraMenu.add_command(label = "Totalise Spec", command=self.totalisespec)
        zdraMenu.add_command(label = "ZDRa PDF", command=self.zdraPdfCheck)
        gpsaMenu.add_command(label = "Proof Skeleton", command=self.createskeleton)
        gpsaMenu.add_command(label = "ProofPower-Z Skeleton", command=self.createppgpsa)
        gpsaMenu.add_command(label = "Isabelle Skeleton", command=self.createIsaPS)
        gpsaMenu.add_command(label = "FillInIsaSkeleton", command=self.fillInIsa)
        menubar.add_cascade(label="File", menu=fileMenu)
        menubar.add_cascade(label="Edit", menu=editMenu)
        menubar.add_cascade(label="Z Specification", menu=zedMenu)
        menubar.add_cascade(label="ZCGa", menu=zcgaMenu)
        menubar.add_cascade(label= "ZDRa", menu=zdraMenu)
        menubar.add_cascade(label="GPSa", menu=gpsaMenu)
        self.txt = Text(self, yscrollcommand = scrollbar.set, undo=True)
        self.txt.pack(fill=BOTH, expand=1)
        self.content=self.txt.get(1.0,END)
        self.txt.bind("<Control-Key-a>", self.select_all)
        self.txt.bind("<Control-Key-A>", self.select_all)
        self.txt.bind("<Control-Key-f>", self.searchWindowButton)
        self.txt.bind("<Control-Key-F>", self.searchWindowButton)
        
        
        self.m2 = PanedWindow(m1, orient=VERTICAL)
        m1.add(self.m2)
        
        toplabel = Label(self.m2, text= "Messages")
        toplabel.pack()
        
        self.top = ScrolledText(self.m2, wrap=WORD, state=DISABLED,height=13,width=400)
        self.m2.add(self.top)
        self.top.pack()            
        #bottomlabel = Label(self.m2, text = "User input")
        #bottomlabel.pack()
        #self.bottom = ScrolledText(self.m2, wrap=WORD, height=13,width=400)
        #self.m2.add(self.bottom)
        #self.bottom.pack()
        scrollbar.config(command = self.txt.yview)
        self.txt.insert(END, "Please choose a specification by clicking on file then open") 
        #b = Button(self.m2, text = "Submit",borderwidth=1,bg='ghostwhite', command = self.submitbutton)          #testpasss
        #b.pack()
        radioVar = IntVar()
        radioFrame=Frame(m1,bd=0, relief='flat', width=400,bg='black')                                                            # Frame containing the radiobuttons
        radioFrame.place(x=1, y=550)
           
        zedRadio = Radiobutton(radioFrame, text='Z', variable=radioVar, width=7,  value=1,command=self.selected)
        zedRadio.grid(row=0,column=1)
        zcgaRadio = Radiobutton(radioFrame, text='ZCGa', variable=radioVar, width=7, value=2,command=self.selected)
        zcgaRadio.grid(row=0,column=2)
        zdraRadio = Radiobutton(radioFrame, text='ZDRa', variable=radioVar, width=7, value=3,command=self.selected)       
        zdraRadio.grid(row=0,column=3)
        zedRadio.invoke()
        
        self.txt.tag_config('green', background='green', foreground='black')                              # declaring the colour tags which will be used later for colouring diff parts of the text (for zcga)
        self.txt.tag_config('red', background='red', foreground='black')
        self.txt.tag_config('blue', background='deep sky blue', foreground='white')
        self.txt.tag_config('orange', background='tan1', foreground='black')
        self.txt.tag_config('pale', background='bisque2', foreground='black')
        self.txt.tag_config('gray', background='#778999', foreground='white')
        self.txt.tag_config('pink', background='#FFBDCA', foreground='black')
        self.txt.tag_configure("bt", font=("Georgia", "10", "bold"))
        self.txt.tag_configure("bt1", font=("Georgia", "12", "bold"))
        self.txt.tag_configure("bt2", font=("Georgia", "13", "bold"))
        self.txt.tag_configure('errorLine', background='lemon chiffon', foreground='black')
        
            
#########################################################################################
    
    def totalisespec(self):
        self.gpsalocation = totalise.findgpsa(self.fl)
        if os.path.isfile(self.gpsalocation):
            self.top.config(state=NORMAL)
            self.top.delete(1.0, END)
            self.top.insert(END, "Found Specifications")
            self.top.config(state=DISABLED)
        else:
            self.top.config(state=NORMAL)
            self.top.delete(1.0, END)
            self.top.insert(END, "Please convert specification into GPSa first")
            self.top.config(state=DISABLED)
            
        
    def zdracheck(self):
        zdracheck.totalcheck(self.fl)
        #zdracheck.createplot(self.fl)
        #zdracheck.creatdepgraphplot(self.fl)
        self.top.config(state=NORMAL)
        self.top.delete(1.0, END)
        self.top.insert(END, zdracheck.printoutput())
        self.top.config(state=DISABLED)
        self.depbutton = Button(self.m2, text = "Show Dependency", command = self.showDependency)
        self.depbutton.pack()
        self.gotobutton = Button(self.m2, text = "Show GoTo", command = self.showGoTo)
        self.gotobutton.pack()
        
    def showGoTo(self):
        self.goto_location = totalise.find_goto_name(self.fl)
        gotoWindow = Toplevel()
        gotoWindow.title("GoTo Graph")
        canvas = Canvas(gotoWindow, width=600, height=600)
        canvas.pack()
        #photoimage = ImageTk.PhotoImage(file=self.goto_location)
       # canvas.create_image(300, 300, image=photoimage)
        gotoWindow.pack()
        #zdracheck.showplot(self.thegoto)
    
    def showDependency(self):
        self_dep_location = totalise.find_dp_name(self.fl)
        gotoWindow = Toplevel()
        gotoWindow.title("Dep Graph")
        canvas = Canvas(gotoWindow, width=600, height=600)
        canvas.pack()
     #   photoimage = ImageTk.PhotoImage(file=self_dep_location)
       # canvas.create_image(300, 300, image=photoimage)
        gotoWindow.pack()
        #zdracheck.showplot(self.thedepgraph)
    
    def showgpsa(self):
        self.gpsalocation = totalise.findgpsa(self.fl)
        if os.path.isfile(self.gpsalocation):
            gpsawindow = Toplevel()
            gpsawindow.title("ProofPower Skeleton")
            gpsaspec = ScrolledText(gpsawindow, wrap=WORD)
            gpsaspec.pack()
            gpsaspecif = self.readFile(self.gpsalocation)
            gpsaspec.config(state=NORMAL)
            gpsaspec.insert(END, gpsaspecif)
            gpsaspec.config(state=DISABLED)
        else:
            self.top.config(state=NORMAL)
            self.top.delete(1.0, END)
            self.top.insert(END, "Please convert specification into GPSa first")
            self.top.config(state=DISABLED)
            
    def showIsaSkel(self):
        self.Isalocation = totalise.findisagpsa(self.fl)
        if os.path.isfile(self.Isalocation):
            isawindow = Toplevel()
            isawindow.title("Isabelle Skeleton")
            isaspec = ScrolledText(isawindow, wrap=WORD)
            isaspec.pack()
            isaspecif = self.readFile(self.Isalocation)
            isaspec.config(state=NORMAL)
            isaspec.insert(END, isaspecif)
            isaspec.config(state=DISABLED)
        else:
            self.top.config(state=NORMAL)
            self.top.delete(1.0, END)
            self.top.insert(END, "Please convert specification into Isabelle Skeleton first")
            self.top.config(state=DISABLED)
            
    def fillInIsa(self):
        self.Isalocation = totalise.findisagpsa(self.fl)
        if os.path.isfile(self.Isalocation):
            if ('\\usepackage{zmathlang}' in open(self.fl).read()) or ('\\usepackage{zmathlang}' in open(self.fl).read()):
                self.Isalocation = totalise.findisagpsa(self.fl)
                zdra.x.fillinIsa(self.fl, self.Isalocation)
                zdra.x.fillinIsa(self.fl, self.Isalocation)
                zdra.x.fillNames(self.Isalocation)
                self.top.config(state=NORMAL)
                self.top.delete(1.0, END)
                self.top.insert(END, "Isabelle Skeleton successfully filled in ")
                self.top.config(state=DISABLED)
            else:
                self.top.config(state=NORMAL)
                self.top.delete(1.0, END)
                self.top.insert(END, "Please select your isabelle skeleton:")
                self.top.config(state=DISABLED)
                filename = tkFileDialog.askopenfilename(**self.file_opt)
                zdra.x.fillinIsa(self.fl, filename)
                zdra.x.fillinIsa(self.fl, filename)
                zdra.x.fillNames(filename)
                self.top.config(state=NORMAL)
                self.top.delete(1.0, END)
                self.top.insert(END, "Isabelle Skeleton successfully filled in ")
                self.top.config(state=DISABLED)
        else:
            self.top.config(state=NORMAL)
            self.top.delete(1.0, END)
            self.top.insert(END, "Please convert specification into Isabelle Skeleton first")
            self.top.config(state=DISABLED)
            
    def askopenfilename(self):
        self.filename = tkFileDialog.askopenfilename(**self.file_opt)
        if filename:
            return filename
        
    def createppgpsa(self):
        zdra.createPPZskel(self.fl)
        self.top.config(state=NORMAL)
        self.top.delete(1.0, END)
        self.top.insert(END, "ProofPower-Z Skeleton Created")
        self.top.config(state=DISABLED)
        self.gpsabutton = Button(self.m2, text ="Show PP Skeleton", command = self.showgpsa)
        self.gpsabutton.pack()
        
    def createIsaPS(self):
        zdra.createIsaskel(self.fl)
        self.top.config(state=NORMAL)
        self.top.delete(1.0, END)
        self.top.insert(END, "Isabelle Skeleton Created")
        self.top.config(state=DISABLED)
        self.gpsabutton = Button(self.m2, text ="Show Isabelle Skeleton", command = self.showIsaSkel)
        self.gpsabutton.pack()
        
    def showskeleton(self):
        self.skel_location = zdracheck.findskeleton(self.fl)
        if os.path.isfile(self.skel_location):
            skelwindow = Toplevel()
            skelwindow.title("Generalised Skeleton")
            skelspec = ScrolledText(skelwindow, wrap=WORD)
            skelspec.pack()
            skelspecif = self.readFile(self.skel_location)
            skelspec.insert(END, skelspecif)
            skelspec.config(state=DISABLED)
            
        else:
            self.top.config(state=NORMAL)
            self.top.delete(1.0, END)
            self.top.insert(END, "Please convert specification into GPSa first")
            self.top.config(state=DISABLED)
        
    def createskeleton(self):
        if zdracheck.isthereanyloops() == False:
            zdracheck.createskeleton(self.fl)
            self.top.config(state=NORMAL)
            self.top.delete(1.0, END)
            self.top.insert(END, "Skeleton Created")
            self.top.config(state=DISABLED)
            self.skelbutton = Button(self.m2, text ="Show Skeleton", command = self.showskeleton)
            self.skelbutton.pack()
        else:
            self.top.config(state=NORMAL)
            self.top.delete(1.0, END)
            self.top.insert(END, "Loops in reasoning \nCan not create Skeleton")
            self.top.config(state=DISABLED)
        
    
    def submitbutton(self):
        #content = self.txt.selection_get()
        #print content
        print self.bottom.get("1.0", "end-1c")
         
        

###################################OPEN~~~~~~~~~~~~Note that self.fl line is changed from tkFileDialog.Open to askopenfilename            
    def onOpen(self):
        global master
        global pdfDirectory
        global mainName
        global currentFile
        ftypes = [ ('Tex files', '*.tex'),('All Files', '*')]
        self.fl= tkFileDialog.askopenfilename(filetypes = ftypes)
        if self.fl != "":             
            currentFile = open(self.fl,"r")
            self.txt.delete(1.0,END)
            self.txt.insert(1.0,currentFile.read())
            self.top.config(state=NORMAL)
            self.top.delete(1.0,END)
            self.top.config(state=DISABLED)
            fileTitle=self.getName(self.fl)
            self.master.title("Z Specification - %s"%fileTitle)            
            
                               

################################################
#reads a file
    def readFile(self, filename):
        f = open(filename, "r+")
        text = f.read()
        return text

################## ZED PANEL, containing z labelling buttons
    def zedPanel(self):
        global toolbarZ
        toolbarZ = Frame(m1,bd=30, relief='flat',width=550,height=400)                                                            
        toolbarZ.place(x=0,y=600)
        label1=Label(toolbarZ,text='Z Labels:')
        label1.place( relx=0, rely=0.05, anchor=SW)
        button1=Button(toolbarZ, text = "SCH BOX ",height=1,width=8,borderwidth=1,bg='ghostwhite', command = self.addSchemaBox )
        button1.place( relx=0, rely=0.16, anchor=SW)
        button2=Button(toolbarZ, text = "WHERE",height=1,width=8,borderwidth=1,bg='ghostwhite', command = self.addLine)
        button2.place( relx=0.175, rely=0.16, anchor=SW)
        button3=Button(toolbarZ, text = "DEF",height=1,width=8,borderwidth=1,bg='ghostwhite', command = self.addSetDef)
        button3.place( relx=0.35, rely=0.16, anchor=SW)
        button4=Button(toolbarZ, text = "Z FRAME ",height=1,borderwidth=1,width=8, bg='ghostwhite',command = self.addZedFrame)
        button4.place(relx=0, rely=0.24, anchor=SW)
        button5=Button(toolbarZ, text = "AX DESC",height=1,borderwidth=1,width=8,bg='ghostwhite',command = self.addAxiomDesc )
        button5.place( relx=0.175, rely=0.24, anchor=SW)
        button6=Button(toolbarZ, text = "GEN DEF",height=1,borderwidth=1,width=8,bg='ghostwhite', command = self.addGenDef )
        button6.place( relx=0.35, rely=0.24, anchor=SW)
                          
                    
###########ZCGA PANEL, containing zcga labelling buttons
    def zcgaPanel(self):
        global toolbarZcga
        toolbarZcga = Frame(m1,bd=30, relief='flat',width=550,height=400)
        toolbarZcga.place(x=0,y=600)
        label1=Label(toolbarZcga,text='ZCGa Labels:')
        label1.place( relx=0, rely=0.05, anchor=SW)
        button1=Button(toolbarZcga, text="TERM", height=1,width=8,borderwidth=1, bg='blue', fg='white', command = self.addTerm)
        button1.place( relx=0, rely=0.16, anchor=SW)
        button2=Button(toolbarZcga, text="SET", height=1,width=8,borderwidth=1, bg='red', command = self.addSet)
        button2.place( relx=0.19, rely=0.16, anchor=SW)
        button3=Button(toolbarZcga, text="DECL", height=1,width=8,borderwidth=1, bg='gray49', command = self.addDeclaration)
        button3.place( relx=0.38, rely=0.16, anchor=SW)
        button4=Button(toolbarZcga, text="SPEC", height=1,width=8,borderwidth=1, bg='peach puff',command = self.addSpecification)
        button4.place(relx=0.57, rely=0.16, anchor=SW)
        button5=Button(toolbarZcga, text="TEXT", height=1 ,width=8,borderwidth=1, bg='gray70', command = self.addText)
        button5.place(relx=0.095, rely=0.24, anchor=SW)
        button6=Button(toolbarZcga, text="EXPR", height=1 ,width=8,borderwidth=1, bg='forest green', command = self.addExpression)
        button6.place(relx=0.285, rely=0.24, anchor=SW)
        button7=Button(toolbarZcga, text="DEF", height=1,width=8,borderwidth=1, bg='LightYellow3', command = self.addDefinition)
        button7.place(relx=0.475, rely=0.24, anchor=SW)
        label2=Label(toolbarZcga,text='Options:')
        label2.place( relx=0, rely=0.48, anchor=SW)
        button8=Button(toolbarZcga, text="Check & PDF", height=1,width=10,borderwidth=1,bg='ghostwhite',command = self.checkAndPdf)
        button8.place(relx=0.04, rely=0.58, anchor=SW)
        button9=Button(toolbarZcga, text="Check", height=1,width=10,borderwidth=1,bg='ghostwhite',command=self.zcgacheckMenu)
        button9.place(relx=0.285, rely=0.58, anchor=SW)
        button10=Button(toolbarZcga, text="ZCGa Pack", height=1,width=10,borderwidth=1,bg='ghostwhite',command=self.searchZcgaPackButton)
        button10.place(relx=0.530, rely=0.58, anchor=SW)
        
                    
            

    ################## ZDRA PANEL, containing zdra labelling buttons            
    def zdraPanel(self):
        global toolbarZdra       
        toolbarZdra = Frame(m1,bd=20, relief='flat', width=550, height=400)
        toolbarZdra.place(x=0,y=600)

        label1=Label(toolbarZdra,text='ZDRa Labels:')
        label1.place( relx=0, rely=0.05, anchor=SW)
        #Row1
        button1=Button(toolbarZdra, text = "THEORY",height=1,width=10,borderwidth=1, bg='ghostwhite',command=self.addTheory)
        button1.place( relx=0, rely=0.16, anchor=SW)
        button2=Button(toolbarZdra, text = "STATE SCH",height=1,width=10,borderwidth=1,bg='ghostwhite',command = self.addStateSchema)
        button2.place( relx=0.21, rely=0.16, anchor=SW)
        button3=Button(toolbarZdra, text = "INIT SCH",height=1,width=10,borderwidth=1,bg='ghostwhite', command = self.addInitSchema)
        button3.place( relx=0.42, rely=0.16, anchor=SW)
        button4=Button(toolbarZdra, text = "CHANGE SCH",height=1,width=10,borderwidth=1,bg='ghostwhite',command = self.addChangeSchema)
        button4.place(relx=0.63, rely=0.16, anchor=SW)
        #Row2
        button6=Button(toolbarZdra, text = "AXIOM",height=1,width=10,borderwidth=1,bg='ghostwhite',  command = self.addAxiom)
        button6.place( relx=0.21, rely=0.24, anchor=SW)
        button7=Button(toolbarZdra, text = "OUTPUT",height=1,width=10,borderwidth=1,bg='ghostwhite',command = self.addOutput)
        button7.place( relx=0.42, rely=0.24, anchor=SW)
        button11=Button(toolbarZdra, text = "TOTALISE",height=1,width=10,borderwidth=1,bg='ghostwhite', command=self.totalise)
        button11.place( relx=0.63, rely=0.24, anchor=SW)
        
        #Row3
        button5=Button(toolbarZdra, text = "OUTPUT SCH",height=1,width=10,borderwidth=1,bg='ghostwhite',  command = self.addOutputSchema)
        button5.place(relx=0, rely=0.24, anchor=SW)      
        button8=Button(toolbarZdra, text = "STATE INV",height=1,width=10,borderwidth=1,bg='ghostwhite',  command = self.addStateInvariants)
        button8.place(relx=0.11, rely=0.32, anchor=SW)
        button9=Button(toolbarZdra, text = "PRECON",height=1,width=10,borderwidth=1,bg='ghostwhite', command = self.addPrecondition)
        button9.place( relx=0.32, rely=0.32, anchor=SW)
        button10=Button(toolbarZdra, text = "POSTCON",height=1,width=10,borderwidth=1,bg='ghostwhite',  command = self.addPostcondition)
        button10.place(relx=0.53, rely=0.32, anchor=SW)
       

        label2=Label(toolbarZdra,text='Relations:')
        label2.place(relx=0, rely=0.48, anchor=SW)
        button12=Button(toolbarZdra, text = "INITIAL OF",height=1,width=10,borderwidth=1,bg='ghostwhite', command = self.addInitialOf)
        button12.place( relx=0, rely=0.60, anchor=SW)
        button13=Button(toolbarZdra, text = "USES",height=1,width=10,borderwidth=1,bg='ghostwhite', command=self.addUses)
        button13.place( relx=0.21, rely=0.60, anchor=SW)
        button14=Button(toolbarZdra, text = "REQUIRES",height=1,width=10,borderwidth=1,bg='ghostwhite', command = self.addRequires)
        button14.place( relx=0.42, rely=0.60, anchor=SW)
        button15=Button(toolbarZdra, text = "ALLOWS",height=1,width=10,borderwidth=1,bg='ghostwhite', command = self.addAllows)
        button15.place( relx=0.63, rely=0.60, anchor=SW)
        button17=Button(toolbarZdra, text = "Submit REL",height=1,width=10,borderwidth=1,bg='ghostwhite', command = self.submitRel)
        button17.place( relx=0.32, rely=0.68, anchor=SW)         

    def submitRel(self):
        relations=self.bottom.get("1.0", "end-1c")
        self.txt.insert(END, '\n'+relations)    

    def selected(self):
        global toolbarZ
        global toolbarZcga
        global toolbarZdra
        global radioVar
        
        if radioVar.get()==1:
            self.zedPanel()
                                                          
        elif radioVar.get()==2:
             self.zcgaPanel()
            

        else:
            self.zdraPanel()

                                      
#######ZCGA Panel functions *Adding ZCGA labels to a selected piece of text*
       
    def addTerm(self):
        
        self.txt.insert(tk.SEL_FIRST,'\\term{')
        self.txt.insert(tk.SEL_LAST,'}' )
        self.txt.tag_configure("term", foreground="blue")
        self.txt.tag_add('term', tk.SEL_FIRST + '-6c', tk.SEL_FIRST)
        self.txt.tag_add('term', tk.SEL_LAST, tk.SEL_LAST + '+1c')
        self.txt.tag_add('bt', tk.SEL_FIRST + '-6c', tk.SEL_FIRST)
        self.txt.tag_add('bt', tk.SEL_LAST, tk.SEL_LAST + '+1c')
        
        
    def addSet(self):
        self.txt.insert(tk.SEL_FIRST,'\\set{')
        self.txt.insert(tk.SEL_LAST,'}' )
        self.txt.tag_configure("set", foreground="red")
        self.txt.tag_add('set', tk.SEL_FIRST + '-5c', tk.SEL_FIRST)
        self.txt.tag_add('set', tk.SEL_LAST, tk.SEL_LAST + '+1c')
        self.txt.tag_add('bt', tk.SEL_FIRST + '-5c', tk.SEL_FIRST)
        self.txt.tag_add('bt', tk.SEL_LAST, tk.SEL_LAST + '+1c')
            
    def addDeclaration(self):
        self.txt.insert(tk.SEL_FIRST,'\\declaration{')
        self.txt.insert(tk.SEL_LAST,'}' )
        self.txt.tag_configure('declaration', foreground='purple')
        self.txt.tag_add('declaration', tk.SEL_FIRST + '-13c', tk.SEL_FIRST)
        self.txt.tag_add('declaration', tk.SEL_LAST, tk.SEL_LAST + '+1c')
        self.txt.tag_add('bt', tk.SEL_FIRST + '-13c', tk.SEL_FIRST)
        self.txt.tag_add('bt', tk.SEL_LAST, tk.SEL_LAST + '+1c' )
        self.txt.tag_add('bt1', tk.SEL_FIRST + '-1c', tk.SEL_FIRST)
        self.txt.tag_add('bt1', tk.SEL_LAST, tk.SEL_LAST + '+1c')

    def addExpression(self):
        self.txt.insert(tk.SEL_FIRST,'\\expression{')
        self.txt.insert(tk.SEL_LAST,'}' )
        self.txt.tag_configure("expression", foreground="forest green")
        self.txt.tag_add('expression', tk.SEL_FIRST +'-12c' , tk.SEL_FIRST)
        self.txt.tag_add('expression', tk.SEL_LAST, tk.SEL_LAST + '+1c')
        self.txt.tag_add('bt', tk.SEL_FIRST + '-12c', tk.SEL_FIRST)
        self.txt.tag_add('bt', tk.SEL_LAST, tk.SEL_LAST + '+1c')
        
    def addDefinition(self):
        self.txt.insert(tk.SEL_FIRST,'\\definition{')
        self.txt.insert(tk.SEL_LAST,'}' )
        self.txt.tag_configure("definition", foreground="pink3")
        self.txt.tag_add('definition', tk.SEL_FIRST+'-12c' , tk.SEL_FIRST)
        self.txt.tag_add('definition', tk.SEL_LAST, tk.SEL_LAST + '+1c')
        self.txt.tag_add('bt', tk.SEL_FIRST + '-12c', tk.SEL_FIRST)
        self.txt.tag_add('bt', tk.SEL_LAST, tk.SEL_LAST + '+1c')
       
            
    def addText(self):
        self.txt.insert(tk.SEL_FIRST,'\\text{')
        self.txt.insert(tk.SEL_LAST,'}' )
        self.txt.tag_configure("text", foreground="DarkOrange2")
        self.txt.tag_add('text', tk.SEL_FIRST+'-6c' , tk.SEL_FIRST)
        self.txt.tag_add('text', tk.SEL_LAST, tk.SEL_LAST + '+1c')
        self.txt.tag_add('bt', tk.SEL_FIRST + '-6c', tk.SEL_FIRST)
        self.txt.tag_add('bt', tk.SEL_LAST, tk.SEL_LAST + '+1c')
        self.txt.tag_add('bt2', tk.SEL_FIRST + '-1c', tk.SEL_FIRST)
        self.txt.tag_add('bt2', tk.SEL_LAST, tk.SEL_LAST + '+1c')
            
    def addSpecification(self):
        self.txt.insert(tk.SEL_FIRST,'\\specification{')
        self.txt.insert(tk.SEL_LAST,'}' )
        self.txt.tag_configure("specification", foreground="hot pink")
        self.txt.tag_add('specification', tk.SEL_FIRST + '-15c', tk.SEL_FIRST)
        self.txt.tag_add('specification', tk.SEL_LAST, tk.SEL_LAST + '+1c')
        self.txt.tag_add('bt', tk.SEL_FIRST + '-15c', tk.SEL_FIRST)
        self.txt.tag_add('bt', tk.SEL_LAST, tk.SEL_LAST + '+1c')


    def searchZcgaPackButton(self):        
        start = '1.0'
        while True:
            idx = self.txt.search('\usepackage{zcga}', start, END)
            if not idx:
                zcgaPackCheck=True   
                break
            else:
                zcgaPackCheck=False
                break
        if zcgaPackCheck==True:
            self.txt.insert('2.5 linestart','\\usepackage{zcga}\n')
        else:
            tkMessageBox.showwarning("ZCGa Pack","The ZCGa Pack has already been added to your file.")
            
            
            
        
            

####################ZED Panel functions *Adding Z labels to a selected piece of text*

    def addZedFrame(self):
        self.txt.insert(tk.SEL_FIRST,'\\documentclass{article}\n\\usepackage{zed}\n\\begin{document}\n\n')
        self.txt.insert(tk.SEL_LAST,'\n\\end{document}')

            
    def addLine(self):
        self.txt.insert(self.txt.index(INSERT), "\\where\n")
                           
        
    def addSetDef(self):
        self.txt.insert(tk.SEL_FIRST,'\\begin{zed} \n')
        self.txt.insert(tk.SEL_LAST,'\n\\end{zed}')
            
            
    def addSchemaBox(self):
        self.txt.insert(tk.SEL_FIRST,'\\begin{schema}{}\n')
        self.txt.insert(tk.SEL_LAST,'\n\\end{schema}')
            
    def addAxiomDesc(self):
        self.txt.insert(tk.SEL_FIRST,'\\begin{axdef} \n')
        self.txt.insert(tk.SEL_LAST,'\n\\end{axdef}')
            
    def addGenDef(self):
        self.txt.insert(tk.SEL_FIRST,'\\begin{gendef} \n')
        self.txt.insert(tk.SEL_LAST,'\n\\end{gendef}')
        
######################## ZDRA Panel functions  *Adding zdra labels to a selected piece of text*      
      
    def addTheory(self):
        global theoryC
        self.txt.insert(tk.SEL_FIRST,'\\dratheory{T%s}{scaleOfTheory}{\n'%theoryC)
        self.txt.insert(tk.SEL_LAST,'\n }')
        theoryC+=1

            
    def addStateSchema(self):
        global stateSchC
        self.txt.insert(tk.SEL_FIRST,'\\draschema{SS%s}{\n'%stateSchC)
        self.txt.insert(tk.SEL_LAST,'\n }')
        stateSchC+=1                   
        
    def addInitSchema(self):
        global initSchC                
        self.txt.insert(tk.SEL_FIRST,'\\draschema{IS%s}{\n'%initSchC)
        self.txt.insert(tk.SEL_LAST,'\n}')
        initSchC+=1    
            
    def addChangeSchema(self):
        global changeSchC
        self.txt.insert(tk.SEL_FIRST,'\\draschema{CS%s}{\n'%changeSchC)
        self.txt.insert(tk.SEL_LAST,'\n}')
        changeSchC+=1
            
    def addOutputSchema(self):
        global outputSchC
        self.txt.insert(tk.SEL_FIRST,'\\draschema{OS%s}{\n'%outputSchC)
        self.txt.insert(tk.SEL_LAST,'\n}')
        outputSchC+=1
            
    def totalise(self):
        global totaliseC
        self.txt.insert(tk.SEL_FIRST,'\\draschema{TS%s}{\n'%totaliseC)
        self.txt.insert(tk.SEL_LAST,'\n}')
        totaliseC+=1

    def addAxiom(self):
        global axiomC
        self.txt.insert(tk.SEL_FIRST,'\\draschema{A%s}{\n'%axiomC)
        self.txt.insert(tk.SEL_LAST,'\n}')
        axiomC+=1
            
    def addStateInvariants(self):
        global stateInvC
        self.txt.insert(tk.SEL_FIRST,'\\draline{SI%s}{\n'%stateInvC)
        self.txt.insert(tk.SEL_LAST,'\n}')
        stateInvC+=1                   
        
    def addPrecondition(self):
        global preconC
        self.txt.insert(tk.SEL_FIRST,'\\draline{PRE%s}{\n'%preconC)
        self.txt.insert(tk.SEL_LAST,'\n}')
        preconC+=1    
            
    def addPostcondition(self):
        global postconC
        self.txt.insert(tk.SEL_FIRST,'\\draline{PO%s}{\n'%postconC)
        self.txt.insert(tk.SEL_LAST,'\n}')
        postconC+=1
        
    def addOutput(self):
        global outputC  
        self.txt.insert(tk.SEL_FIRST,'\\draline{O %s}{\n'%outputC)
        self.txt.insert(tk.SEL_LAST,'\n}')
        outputC+=1

    def addInitialOf(self):
        self.bottom.insert(END,'\\initialof{}{}\n')
        
    def addUses(self):
        self.bottom.insert(END,'\\uses{}{}\n')
        
    def addRequires(self):
        self.bottom.insert(END,'\\requires{}{}\n')
        
    def addAllows(self):
        self.bottom.insert(END,'\\allows{}{}\n')
        

    
       
        

####################################################SAVE FUNCTION
    
#saves the changes in a file    
    def saveMenu(self):

        self.txt.tag_remove("found",  "1.0", 'end')
        try:
            
            fileName=self.fl
            fl = open(fileName, 'w')
            textoutput = self.txt.get(1.0, END)
            fl.write(textoutput)
                                       
        except:
            self.save_asMenu()
                                    
#asks the user for a title of the file (if it has not been saved yet)
    def save_asMenu(self):
        global mainName
        global pdfDirectory
        global master
        self.txt.tag_remove("found",  "1.0", 'end')
        contents = self.txt.get(1.0,"end-1c")
        self.f = tkFileDialog.asksaveasfilename(   
            defaultextension=".tex",                
            filetypes = (("tex file", "*.tex"),    
                         ("txt", "*.txt")))
        try:
            
            with open(self.f, 'w') as outputFile:
                outputFile.write(contents)
            self.fl=self.f
            fileTitle=self.getName(self.fl)
            self.master.title("Z Specification - %s"%fileTitle)
        except:
            pass
 
    def exitMenu(self):
        win=tkMessageBox.askyesno("Quit", "Are you sure you want to quit?")
        if win:
            root.destroy()
        else:
            pass

############################## NEW FILE
    def newFile(self):
        global newWin
        newWin = Toplevel()
        newWin.geometry("350x100+100+100")
        newWin.resizable(0,0)
        newWin.title("Save")
        try:
            if self.fl!='':
                if mainName!='Untitled':
                
                    labelQuestion=Label(newWin, text = "Do you want to save changes to %s?"%mainName)
                    labelQuestion.pack(side=TOP)
                    label0=Label(newWin, text = " ")
                    label0.pack(side=LEFT)
                    buttonSave=Button(newWin, text = "Save",height=1,width=8,command=self.saveAndClose)
                    buttonSave.pack(side=LEFT)
                    label1=Label(newWin, text = " ")
                    label1.pack(side=LEFT)
                    buttonDontSave=Button(newWin, text = "Don't Save",height=1,width=8,command=self.openNewFile)
                    buttonDontSave.pack(side=LEFT)
                    label2=Label(newWin, text = " ")
                    label2.pack(side=LEFT)
                    buttonCancel=Button(newWin,text = "Cancel",height=1,width=8,command=self.closenewWin)
                    buttonCancel.pack(side=LEFT)
                    label3=Label(newWin, text = " ")
                    label3.pack(side=LEFT)
                    newWin.wm_attributes("-topmost", 1)
                    center(newWin)


                else:
                    labelQuestion=Label(newWin, text = "Do you want to save changes to %s?"%mainName)
                    labelQuestion.pack(side=TOP)
                    label0=Label(newWin, text = " ")
                    label0.pack(side=LEFT)
                    buttonSave=Button(newWin, text = "Save",height=1,width=8,command=self.saveAndCloseUntitled)
                    buttonSave.pack(side=LEFT)
                    label1=Label(newWin, text = " ")
                    label1.pack(side=LEFT)
                    buttonDontSave=Button(newWin, text = "Don't Save",height=1,width=8,command=self.openNewFile)
                    buttonDontSave.pack(side=LEFT)
                    label2=Label(newWin, text = " ")
                    label2.pack(side=LEFT)
                    buttonCancel=Button(newWin,text = "Cancel",height=1,width=8,command=self.closenewWin)
                    buttonCancel.pack(side=LEFT)
                    label3=Label(newWin, text = " ")
                    label3.pack(side=LEFT)
                    newWin.wm_attributes("-topmost", 1)
                    center(newWin)

                
        except:
            labelQuestion=Label(newWin, text = "Do you want to save changes to Untitled?")
            labelQuestion.pack(side=TOP)
            label0=Label(newWin, text = " ")
            label0.pack(side=LEFT)
            buttonSave=Button(newWin, text = "Save",height=1,width=8,command=self.saveAndClose)
            buttonSave.pack(side=LEFT)
            label1=Label(newWin, text = " ")
            label1.pack(side=LEFT)
            buttonDontSave=Button(newWin, text = "Don't Save",height=1,width=8,command=self.openNewFile)
            buttonDontSave.pack(side=LEFT)
            label2=Label(newWin, text = " ")
            label2.pack(side=LEFT)
            buttonCancel=Button(newWin,text = "Cancel",height=1,width=8,command=self.closenewWin)
            buttonCancel.pack(side=LEFT)
            label3=Label(newWin, text = " ")
            label3.pack(side=LEFT)
            newWin.wm_attributes("-topmost", 1)
            center(newWin)

#saves the previous file and closes the pop-up window        
    def saveAndClose(self):
        global pdfDirectory
        global mainName
        newWin.destroy()
        self.saveMenu()
        try:                
                global currentFile
                currentFile.close()
                currentFile=open("Untitled.tex","r+")
                self.fl='%s/Untitled.tex'%pdfDirectory
                self.getName(self.fl)
                self.txt.delete(1.0,END)
                self.txt.insert(1.0,currentFile.read())
                self.top.config(state=NORMAL)
                self.top.delete(1.0,END)
                self.top.config(state=DISABLED)
                self.master.title("Z Specification - Untitled")
                       
        except:
            
                currentFile=open("Untitled.txt","r+")
                self.fl='%s/Untitled.tex'%pdfDirectory
                self.getName(self.fl)
                self.txt.delete(1.0,END)
                self.txt.insert(1.0,currentFile.read())
                self.top.config(state=NORMAL)
                self.top.delete(1.0,END)
                self.top.config(state=DISABLED)
                self.master.title("Z Specification - Untitled")
            



    def saveAndCloseUntitled(self):
        global pdfDirectory
        global mainName
        global currentFile
        newWin.destroy()
        self.save_asMenu()
        try:
            currentFile.close()
            self.txt.delete(1.0,END)
            self.txt.insert(1.0,currentFile.read())
            self.top.config(state=NORMAL)
            self.top.delete(1.0,END)
            self.top.config(state=DISABLED)
            currentFile=open("Untitled.tex","r+")
            self.fl='%s/Untitled.tex'%pdfDirectory
            self.getName(self.fl)
            self.master.title("Z Specification - Untitled")
            
            
        except:     
            currentFile=open("Untitled.tex","r+")
            self.fl='%s/Untitled.tex'%pdfDirectory
            self.getName(self.fl)
            self.txt.delete(1.0,END)
            self.txt.insert(1.0,currentFile.read())
            self.top.config(state=NORMAL)
            self.top.delete(1.0,END)
            self.top.config(state=DISABLED)
            self.master.title("Z Specification - Untitled")            

#closes the pop-up window        
    def closenewWin(self):
        global newWin
        newWin.destroy()

#opens a new file Without saving the changes on the previous file, closes the pop-up window
    def openNewFile(self):
        try:
            global currentFile
            global newWin
            newWin.destroy()
            currentFile.close()
            currentFile=open("Untitled.txt","r+")
            self.fl='%s/Untitled.tex'%pdfDirectory
            self.txt.delete(1.0,END)
            self.txt.insert(1.0,currentFile.read())
            self.top.config(state=NORMAL)
            self.top.delete(1.0,END)
            self.top.config(state=DISABLED)
            self.master.title("Z Specification - Untitled")
        except:
            newWin.destroy()
            f=open("Untitled.txt","r+")
            self.txt.delete(1.0,END)
            self.txt.insert(1.0,f.read())
            self.top.config(state=NORMAL)
            self.top.delete(1.0,END)
            self.top.config(state=DISABLED)
            self.master.title("Z Specification - Untitled")
#############################################GENERATE PDF

#checks for the necessary latex commands which allow generating a Z PDF
    def zedPdfCheck(self):
        zedList=['\\documentclass{article}','\\usepackage{zed}','\\begin{document}','\\end{document}']
        start = '1.0'
        count=0
        for i in zedList:
            while True:
                idx = self.txt.search(i, start, END)
                if idx:
                    count=count+1
                    break
                else:
                    break                
        if count==4:
            self.generate_pdf()
                
        else:        
            tkMessageBox.showwarning('Warning','Z Frame required for generating a Z PDF.\n Please add using the Z Label Menu.')

#checks if the file has the necessary LaTeX commands for generating ZDRa pdf, deletes the \usepackage{zcga} as an error occurs when both zdra and zcga packs are included
            
    def zdraPdfCheck(self):
        zdraList=['\usepackage{zdra}','\usepackage{zcga}','\usepackage{multicol}','\usepackage[margin=1.0in]{geometry}']
        zdraListMissing=[]
        start = '1.0'
        count=0
        for i in zdraList:
            while True:
                idx = self.txt.search(i, start, END)
                if idx:
                    if i=='\\usepackage{zcga}':
                        self.txt.delete('%s linestart'%idx, '%s lineend'%idx)
                        break    
                    else:
                        count+=1
                        break
                else:
                    if i!='\\usepackage{zcga}':
                        zdraListMissing.append(i)
                    break                           
        if count==3:
            self.generate_pdf()
        else:
            if tkMessageBox.askyesno('Warning','ZDRa LaTeX commands missing.\n They are required for generating ZDRa PDF.\n Would you like to add them?'):
                for i in zdraListMissing:
                     self.txt.insert('2.5 linestart',i+'\n')    
                self.generate_pdf()   
            
#generates a pdf of the spec          
    def generate_pdf(self):
        global mainName
        global pdfDirectory
        name=self.getName(self.fl)
        f = open('%s.tex'%name,'w')
        tex = self.txt.get(1.0,"end-1c")
        f.write(tex)
        f.close()
        proc=subprocess.Popen(['pdflatex','-output-directory', pdfDirectory,'%s.tex'%name])
        proc.communicate()
        self.open_file(name)
               
       
#opens the pdf using OS specific commands     
    def open_file(self,filename):
         
        if sys.platform == "win32":
            os.startfile('%s.pdf'%filename)
          
        else:
            opener ="open" if sys.platform == "darwin" else "xdg-open"
            openVar=subprocess.call([opener, '%s.pdf'%filename])   

              
    
# This function 'extracts' the title of the file out of the path name                
    def getName(self, somestring):                                                  
        global mainName
        global pdfDirectory
        if "/" in somestring:
            indexsofslash = [i for i, ltr in enumerate(somestring) if ltr == "/"]
            indexsofdot = [i for i, ltr in enumerate(somestring) if ltr == "."]
            lastindexslash = max(indexsofslash)
            lastindexdot = max(indexsofdot)
            mainName = somestring[lastindexslash + 1:lastindexdot]
            pdfDirectory = somestring[:lastindexslash + 1]
            someothername = pdfDirectory +  mainName
            newname = someothername
        else:
            newname = somestring 
        return newname
        
  
   

##############################################ZCGACHECK and ZCGAPACK FUNCTIONS

#combines the zcgacheck fn (which checks for grammatical correctness) and generate_pdf fn (which generates pdf with the spec)
    def checkAndPdf(self):    
        self.zcgacheckMenu()
        self.generate_pdf()      
        
#checks for grammatical correctness of the spec        
    def zcgacheckMenu(self):
        global fl
        global mainName
        global pdfDirectory
        self.txt.tag_remove("found",  "1.0", 'end')          #this removes the tags which have been attached to the duplicates of words after they've been found by the search fn
        self.txt.tag_remove("errorLine",  "1.0", 'end')
        self.searchPack()
        v=''
        name=self.getName(self.fl)
        lastSaved = open('%s.tex'%name,'w')
        tex = self.txt.get(1.0,"end-1c")
        lastSaved.write(tex)
        lastSaved.close()
        v=self.fl
        zcga.specCorrect(v)
        self.top.config(state=NORMAL)
        self.top.delete(1.0, END)
        self.top.insert(END, zcga.printoutput())
        self.top.config(state=DISABLED)
        listErrors=zcga.errors()
        if listErrors==[]:
            pass
        else:
            for i in listErrors:
                self.searchError(i)
        
                    
#puts tags on the lines containing any of the problematic words            
    def searchError(self, keyword):
        pos = '1.0'
        while True:
            idx = self.txt.search(keyword, pos, END)
            if not idx:
                break
            pos = '{0}+{1}c'.format(idx, len(keyword))
            self.txt.tag_add('errorLine', '%s linestart'%idx, '%s lineend'%idx)
            self.txt.tag_raise(SEL)
            self.txt.tag_raise("found")

#Checks whether \usepackage{zcga} has been added to the text, if not it offers the user to add it to the text                        
    def searchPack(self):
        start = '1.0'
        while True:
            idx = self.txt.search('\usepackage{zcga}', start, END)
            if not idx:
                existCheck=True   
                break
            else:
                existCheck=False
                break
        if existCheck:                
            message=tkMessageBox.askokcancel("Warning", "The ZCGa Latex package\n has not been added to\n your .tex file.\n This will be needed for \n generating the ZCGa PDF.\n Would you like to add it?\n")
            if message:
                self.txt.insert('2.5 linestart','\\usepackage{zcga}\n')
            else:
                pass            
             
#SELECT ALL, CUT, COPY, PASTE, UNDO, REDO - the funcs defining these action.
    def select_all_menu(self):
        self.txt.tag_add(SEL, "1.0", END)
        self.txt.mark_set(INSERT, "1.0")
        self.txt.see(INSERT)
        return 'break'

#defines the select all fn when the user has used the ctrl+A combination
#note that we need separate fns for the two cases since the function used
#when ctrl+A is used has a second argument 'event' which is required when a function is bound to a comb of keys     

    def select_all(self, event):
        self.txt.tag_add(SEL, "1.0", END)
        self.txt.mark_set(INSERT, "1.0")
        self.txt.see(INSERT)
        return 'break'


    def cut(self):
        self.txt.event_generate("<<Cut>>")

#Defines copy method

    def copy(self):
        self.txt.event_generate("<<Copy>>")

#Defines paste method
    def paste(self):
        self.txt.event_generate("<<Paste>>")
#Defines undo method
    def undo(self):
        self.txt.event_generate("<<Undo>>")
#Defines redo method        
    def redo(self):
        self.txt.event_generate("<<Redo>>")
      
################################################################################ SEARCH WINDOW - opens a search window and colours the searched term (if found in the text)
#opens a search window when Search has been selected from the menu
    def searchWindowMenu(self):

        self.searchWin = Toplevel()
        self.searchWin.title("Search")
        Label(self.searchWin,text='Text to find:').pack(side=LEFT)
        self.edit = Entry(self.searchWin)
        self.edit.pack(side=LEFT, fill=BOTH, expand=1)
        self.edit.focus_set()
        button = Button(self.searchWin, text="Search", command = self.on_button)
        button.pack(side=LEFT)

#opens a search window when it's been called by the ctrl+f combination
# note that we need both fns as the searchWindowButton has a second argument 'event' which is needed
# when a fn is bound to a key combination (in this case ctrl+f)
    def searchWindowButton(self,event):
        self.searchWin = Toplevel()
        self.searchWin.title("Search")
        Label(self.searchWin,text='Text to find:').pack(side=LEFT)
        self.edit = Entry(self.searchWin)
        self.edit.pack(side=LEFT, fill=BOTH, expand=1)
        self.edit.focus_set()
        button = Button(self.searchWin, text="Search", command = self.on_button)
        button.pack(side=LEFT)
    
#searches for the word assigned and colours all the duplicates of this word in the spec (if any found)    
    def find(self):      
        self.txt.tag_remove('found', '1.0', END)
        s = self.edit.get()
        if s:
            idx = '1.0'
            while 1:
                idx = self.txt.search(s, idx, nocase=1, stopindex=END)
                if not idx: break
                lastidx = '%s+%dc' % (idx, len(s))
                self.txt.tag_add('found', idx, lastidx)
                self.txt.tag_raise(SEL)
                idx = lastidx
            self.txt.tag_config('found', background='DarkSlateGray2', foreground='black')
        self.edit.focus_set()


    def on_button(self):
        self.find()
        self.searchWin.destroy()
   

        
########################################################################################## RIGHT CLICK MENU - opens a context menu

#defines the context menu which appears when the right button of the mouse is clicked
def rClicker(e):
    
    global rmenu
    global checkValue
    
    
    try:
        
        def rClick_Select(e,apnd=0):
                e.widget.event_generate('<Control-a>')
                
        def rClick_Copy(e):
                e.widget.event_generate('<Control-c>')

        def rClick_Cut(e):
                e.widget.event_generate('<Control-x>')

        def rClick_Paste(e):
            e.widget.event_generate('<Control-v>')
            e.widget.focus()
            
        def rClick_Undo(e):
                e.widget.event_generate('<Control-z>')
                
        def rClick_Redo(e):
                e.widget.event_generate('<Control-y>')
            

        nclst=[
                
                (' Cut   ', lambda e=e: rClick_Cut(e)),
                (' Copy   ', lambda e=e: rClick_Copy(e)),
                (' Paste   ', lambda e=e: rClick_Paste(e)),
                (' Undo   ', lambda e=e: rClick_Undo(e)),
                (' Redo   ', lambda e=e: rClick_Redo(e)),
                (' Select All   ', lambda e=e: rClick_Select(e))
                ]

        rmenu = Menu(None, tearoff=0, takefocus=0)
        for (txt, cmd) in nclst:
            rmenu.add_command(label=txt, command=cmd)

        rmenu.post(e.x_root+10, e.y_root+10)
        checkValue=1
    except TclError:
        print ' - rClick menu, something wrong'
        pass

    return "break"
    
#binds the menu declared in rClicker to the right button of the mouse
def rClickbinder(r):
    global rmenu

    try:
        for b in [ 'Text', 'Entry', 'Listbox', 'Label']: 
            r.bind_class(b, sequence='<Button-3>',
                             func=rClicker, add='')
                                                 
    except TclError:
        print ' - rClickbinder, something wrong'
        pass
    
#bind context menu to a specific element
    root.bind('<Button-3>',rClicker, add='')

#kills the context menu when the user clicks 
def killClicker(self):
    global checkValue
    global rmenu
    if checkValue==1:
        rmenu.destroy()
    else: pass    

##############################################################################EXIT POP-UP WINDOW - opens a pop-up window which asks the user if they want to quit  
# asks the user to confirm quitting            
def quitting():
    win=tkMessageBox.askyesno("Quit", "Are you sure you want to quit?")
    if win:
        root.destroy()
    else:
        pass

# fixes the position of the exit pop-up window in the centre of the main window        
def center(win):                                                 
        win.update_idletasks()
        w = win.winfo_screenwidth()
        h = win.winfo_screenheight()
        size = tuple(int(_) for _ in win.geometry().split('+')[0].split('x'))
        x = w/2 - size[0]/2
        y = h/2 - size[1]/2
        win.geometry("%dx%d+%d+%d" % (size + (x, y)))   
#############################################################


root = Tk()
ex = Example(root)
fileText=StringVar()
root.geometry("900x650+300+300")
root.protocol("WM_DELETE_WINDOW", quitting)
root.bind('<Button-3>',rClicker, add='')
root.bind('<Button-1>',killClicker, add='')
root.mainloop()



#if __name__ == '__main__':
    #main()
    
    
