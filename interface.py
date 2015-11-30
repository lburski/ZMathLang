'''
Created on 17 Jun 2015

@author: lb89
'''
from Tkinter import *
import ImageTk
import tkFileDialog 
from ScrolledText import *
import zdracheck
import zdra
import totalise
import os.path
#import zcga


def combine_funcs(*funcs):
    def combined_func(*args, **kwargs):
        for f in funcs:
            f(*args, **kwargs)
        return combined_func


class Example(Frame):

    def __init__(self, master):
        Frame.__init__(self, master)   

        self.master = master        
        self.initUI()
        

    def initUI(self):
        #self.topMessage = StringVar()

        self.master.title("ZDRa Interface")
        self.pack(fill=BOTH, expand=1, side=LEFT)
               
        m1 = PanedWindow(self.master, width = 750)
        m1.pack(fill=BOTH, expand=1)
        
        scrollbar = Scrollbar(self)
        scrollbar.pack( side = RIGHT, fill=Y )

        menubar = Menu(self.master)
        self.master.config(menu=menubar)

        fileMenu = Menu(menubar)
        zdraMenu = Menu(menubar)
        gpsaMenu = Menu(menubar)
        fileMenu.add_command(label="Open", command=self.onOpen)
        zdraMenu.add_command(label = "ZDRa Check", command=self.zdracheck)
        #zdraMenu.add_command(label = "Totalise Spec", command=self.totalisespec)
        #zdraMenu.add_command(label = "Add Refinements")
        gpsaMenu.add_command(label = "Proof Skeleton", command=self.createskeleton)
        gpsaMenu.add_command(label = "ProofPower-Z Skeleton", command=self.createppgpsa)
        gpsaMenu.add_command(label = "Isabelle Skeleton", command=self.createIsaPS)
        gpsaMenu.add_command(label = "FillInIsaSkeleton", command=self.fillInIsa)
        menubar.add_cascade(label="File", menu=fileMenu)
        menubar.add_cascade(label= "ZDRa", menu=zdraMenu)
        menubar.add_cascade(label="GPSa", menu=gpsaMenu)

        self.txt = Text(self, yscrollcommand = scrollbar.set)
        self.txt.pack(fill=BOTH, expand=1)
        
        self.m2 = PanedWindow(m1, orient=VERTICAL)
        m1.add(self.m2)
        
        toplabel = Label(self.m2, text= "Messages")
        toplabel.pack()
        
        self.top = ScrolledText(self.m2, wrap=WORD, state=DISABLED)
        self.m2.add(self.top)
        self.top.pack()
        
        bottomlabel = Label(self.m2, text = "User input")
        bottomlabel.pack()
        
        self.bottom = ScrolledText(self.m2, wrap=WORD)
        self.m2.add(self.bottom)
        self.bottom.pack()
        
        scrollbar.config(command = self.txt.yview)
        
        self.txt.insert(END, "Please choose a specification by clicking on file then open")
        
        b = Button(self.m2, text = "Submit Message", command = self.submitbutton)
        b.pack()

        #self.topMessage.set("Please pick a specification from the top left")
    
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
        self.thedepgraph = zdracheck.creatdepgraphplot(self.fl)
        self.thegoto = zdracheck.createplot(self.fl)
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
        photoimage = ImageTk.PhotoImage(file=self.goto_location)
        canvas.create_image(300, 300, image=photoimage)
        gotoWindow.pack()
        #zdracheck.showplot(self.thegoto)
    
    def showDependency(self):
        self_dep_location = totalise.find_dp_name(self.fl)
        gotoWindow = Toplevel()
        gotoWindow.title("Dep Graph")
        canvas = Canvas(gotoWindow, width=600, height=600)
        canvas.pack()
        photoimage = ImageTk.PhotoImage(file=self_dep_location)
        canvas.create_image(300, 300, image=photoimage)
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
                zdra.x.fillInNames(self.Isalocation)
                self.top.config(state=NORMAL)
                self.top.delete(1.0, END)
                self.top.insert(END, "Isabelle Skeleton successfully filled in ")
                self.top.config(state=DISABLED)
            else:
                self.top.config(state=NORMAL)
                self.top.delete(1.0, END)
                self.top.insert(END, "Please write where your ZCGa labelled documents is:")
                self.top.config(state=DISABLED)
        else:
            self.top.config(state=NORMAL)
            self.top.delete(1.0, END)
            self.top.insert(END, "Please convert specification into Isabelle Skeleton first")
            self.top.config(state=DISABLED)
        
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
        print self.bottom.get("1.0", "end-1c")
           

    def onOpen(self):
        ftypes = [('Tex files', '*.tex'), ('All files', '*')]
        dlg = tkFileDialog.Open(self, filetypes = ftypes)
        self.fl = dlg.show()

        if self.fl != '':
            self.txt.delete(1.0, END)
            self.text = self.readFile(self.fl)
            self.txt.insert(END, self.text)
            self.top.config(state=NORMAL)
            self.top.delete(1.0, END)
            
                

    def readFile(self, filename):
        f = open(filename, "r")
        text = f.read()
        return text

    

def main():

    root = Tk()
    ex = Example(root)
    root.geometry("900x650+300+300")
    root.mainloop() 
    
    


if __name__ == '__main__':
    main()  
    