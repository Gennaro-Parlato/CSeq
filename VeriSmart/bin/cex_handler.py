import os.path
import sys
import subprocess
import shlex
import re
import multiprocessing
from bin import utils
import json


VERSION = "2017.12.16"

"""

Objectives:
    Handle cex generator:
        + Load cseq.env
        + Load counterexample for cbmc

Prerequisites:

TODO:
    -

Changelog:
    2017.12.16  Initial version

"""


class CEX:
    sep = "- - - - - - - - - - - - - - - - - - - - - - - - - -"

    def __init__(self, seqfile, answer):
        self.seqfile = seqfile
        self.answer = answer

    def produceCEX(self):
        # 1. load object file
        objectFilename = self.seqfile[:-1] + "json"

        if not os.path.isfile(objectFilename):
            return

        cseqObj = {}

        with open(objectFilename) as infile:
            cseqObj = json.load(infile)

        self.maps = cseqObj["maps"]
        self.backend = cseqObj["backend"]
        self.threadnamesmap = cseqObj["threadnamesmap"]
        self.threadindexes = cseqObj["threadindexes"]
        self.threadindextoname = cseqObj["threadindextoname"]
        self.varnamesmap = cseqObj["varnamesmap"]
        self.coordstofunctions = utils.json_deserialize(cseqObj["coordstofunctions"])
        self.outputtofiles = cseqObj["outputtofiles"]

        self.output = self._translateCPROVERcex(self.answer)

        # save counter example
        with open(self.seqfile[:-1] + "cseq.log", "w") as outfile:
            outfile.write(self.output)

    """ Full counterexample translation for CBMC
       (and many tools based on the CPROVER framework)
    """
    def _translateCPROVERcex(self, cex):
        if self.backend != "cbmc":
            return "error trace translation for backend %s is yet supported." % self.backend

        translatedcex = ""
        lines = cex.split("\n")
        k = cex[:cex.find("Counterexample:")].count("\n")+1+1
        separator = "----------------------------------------------------"

        while k<len(lines):
            # case 1: another transition to fetch
            if lines[k].startswith("State ") and lines[k+1] == separator:
                A,B,C = lines[k],lines[k+1],lines[k+2]

                # the part below the separator might be
                # more than one line long..
                j=1
                while ( k+2+j<len(lines) and
                    not lines[k+2+j].startswith("State ") and
                    not lines[k+2+j].startswith("Violated property") ):
                    C+=lines[k+2+j]
                    j+=1

                X,Y,Z = self._mapCPROVERstate(A,B,C)

                if X != "":
                    translatedcex += "%s\n" % X
                    if Y != "": translatedcex += "%s\n" % Y
                    if Z != "": translatedcex += "%s\n" % Z
                    translatedcex += "\n"
            # case 2: final transation with property violation
            elif lines[k].startswith("Violated property"):
                Y,Z,W = self._mapCPROVERendstate(lines[k+1],lines[k+2],lines[k+3])

                translatedcex += "Violated property:\n%s\n%s\n%s\n" % (Y,Z,W)
                translatedcex += "\nVERIFICATION FAILED"

            k+=1

        if len(translatedcex) > 0:
            translatedcex = "Counterexample:\n\n" + translatedcex + "\n\n"

        return translatedcex


    """ Returns the coords of the original input file
        in the format (line,file)
        corresponding to the given output line number, or
        (?,?) if unable to map back.
    """
    def sbizz(self,lineno):
        # print lineno, "##########################"
        lineno = str(lineno)
        nextkey = "0"
        inputfile = ""

        lastmodule = len(self.maps)

        if lineno in self.maps[len(self.maps)-1]:
            firstkey = nextkey = lastkey = lineno

            for modno in reversed(range(0,lastmodule)):
                if str(nextkey) in self.maps[modno] and str(nextkey) != "0":
                    lastkey = str(nextkey)
                    nextkey = str(self.maps[modno][str(nextkey)])
                else:
                    nextkey = "0"

                if str(nextkey)!="0" and modno == 0 and str(lastkey) in self.outputtofiles:
                    inputfile = self.outputtofiles[str(lastkey)]

        if str(nextkey) == "0": nextkey = "?"
        if inputfile == "": inputfile = "?"

        # print nextkey, inputfile
        return (nextkey, inputfile)

    __lastthreadID = ""


    def _mapCPROVERstate(self,A,B,C,showbinaryencoding=False):
        # print "Mapping:", A, B, C
        Aout = Bout = Cout = ""
        keys = {}

        # Fetch values.
        try:
            # 1st line
            tokens = A.split()

            for key,value in zip(tokens[0::2],tokens[1::2]):
                keys[key] = value

            stateout = keys["State"]

            # 3rd line
            line3 = C.strip()
            lvalue = line3[:line3.find("=")]
            rvalue = line3[len(lvalue)+1:]

            # double-check parsing correctness
            if "function" in keys: Aout = "State %s file %s line %s function %s thread %s" % (keys["State"],keys["file"],keys["line"],keys["function"],keys["thread"])
            else: Aout = "State %s file %s line %s thread %s" % (keys["State"],keys["file"],keys["line"],keys["thread"])
            Cout = "  %s=%s" % (lvalue,rvalue)

            if A != Aout or C != Cout:
                self.warn("unable to parse counterexample state %s" % keys["State"])
                return ("","","")
        except Exception as e:
            self.warn("unable to parse counterexample state")
            return ("","","")

        # TRUC: now detect context switch by __cs_pc_cs
        # Special case: context switching.
        if lvalue.startswith("__cs_pc_cs") and "function" in keys and keys["function"] != "":
            threadout = lvalue[11:-1]    # extract * from __cs_pc_cs[(*)]
            threadout = "".join(i for i in threadout if i.isdigit())
            threadindexout = ""
            self.__lastthreadID = threadout
            if threadout in self.threadindextoname:
                threadindexout = self.threadindextoname[threadout]
            Aout = "State %s" % (stateout)
            Cout = "  thread %s (%s) scheduled" % (threadout,threadindexout)
            return Aout,self.sep,Cout

        # Special case: thread creation
        if lvalue == "__cs_threadID":
            threadout = ""
            threadindexout = ""
            fileout = ""
            if "line" in keys: lineout,fileout = self.sbizz(int(keys["line"]))
            Aout = "State %s file %s line %s thread %s" % (stateout,fileout,lineout,self.__lastthreadID)
            Cout = "  pthread_create(thread %s)" % (rvalue[:rvalue.find(" (")])
            return Aout,self.sep,Cout

        # Special case: cond signal
        if lvalue == "__cs_cond_to_signal":
            threadout = ""
            threadindexout = ""
            fileout = ""
            if "line" in keys: lineout,fileout = self.sbizz(int(keys["line"]))
            Aout = "State %s file %s line %s thread %s" % (stateout,fileout,lineout,self.__lastthreadID)
            Cout = "  pthread_cond_signal(%s)" % (rvalue[:rvalue.find(" (")])
            return Aout,self.sep,Cout

        # Special case: cond wait
        if lvalue == "__cs_cond_to_wait_for":
            threadout = ""
            threadindexout = ""
            fileout = ""
            if "line" in keys: lineout,fileout = self.sbizz(int(keys["line"]))
            Aout = "State %s file %s line %s thread %s" % (stateout,fileout,lineout,self.__lastthreadID)
            Cout = "  pthread_cond_wait(%s,?)" % (rvalue[:rvalue.find(" (")])
            return Aout,self.sep,Cout

        # Special case: mutexes lock and unlock
        if lvalue == "__cs_mutex_to_lock" and "function" in keys and not keys["function"]=="__cs_cond_wait_2":
            threadout = ""
            threadindexout = ""
            fileout = ""
            if "line" in keys: lineout,fileout = self.sbizz(int(keys["line"]))
            Aout = "State %s file %s line %s thread %s" % (stateout,fileout,lineout,self.__lastthreadID)
            Cout = "  pthread_mutex_lock(%s)" % (rvalue[:rvalue.find(" (")])
            return Aout,self.sep,Cout

        if lvalue == "__cs_mutex_to_unlock" and "function" in keys and not keys["function"]=="__cs_cond_wait_1" :
            threadout = ""
            threadindexout = ""
            fileout = ""
            if "line" in keys: lineout,fileout = self.sbizz(int(keys["line"]))

            Aout = "State %s file %s line %s thread %s" % (stateout,fileout,lineout,self.__lastthreadID)
            Cout = "  pthread_mutex_unlock(%s)" % (rvalue[:rvalue.find(" (")])
            return Aout,self.sep,Cout

        # Special case: mutexes destroy
        if lvalue == "__cs_mutex_to_destroy":
            threadout = ""
            threadindexout = ""
            fileout = ""
            if "line" in keys: lineout,fileout = self.sbizz(int(keys["line"]))
            Aout = "State %s file %s line %s thread %s" % (stateout,fileout,lineout,self.__lastthreadID)
            Cout = "  pthread_mutex_destroy(%s)" % (rvalue[:rvalue.find(" (")])
            return Aout,self.sep,Cout

        # Special case: explicit __CSEQ_message().
        if lvalue== "__cs_message":
            threadout = ""
            threadindexout = ""

            if "line" in keys: lineout,fileout = self.sbizz(int(keys["line"]))

            if "function" in keys:
                #if keys["function"] in self.threadindexes: threadout = self.threadindexes[keys["function"]]
                if keys["function"] in self.threadnamesmap: functionout = self.threadnamesmap[keys["function"]]

            if "function" in keys:
                if keys["function"] in self.threadindexes: threadout = self.threadindexes[keys["function"]]
                #if keys["function"] in self.threadnamesmap: functionout = self.threadnamesmap[keys["function"]]

            message = rvalue[:rvalue.find(" (")][1:-1]
            Aout = "State %s thread %s" % (stateout,self.__lastthreadID)
            Cout = "  "+message
            return Aout,self.sep,Cout

        # State mapping for the lazy schema,
        # general case.
        fileout = functionout = ""
        lineout = 0
        # Truc -- dirty fix
        threadout = -1

        if "line" in keys: lineout,fileout = self.sbizz(int(keys["line"]))

        if "function" in keys:
            if keys["function"] in self.threadindexes: threadout = self.threadindexes[keys["function"]]
            if keys["function"] in self.threadnamesmap: functionout = self.threadnamesmap[keys["function"]]

        # Truc
        if threadout == -1:    # Cannot find the thread id from line map
            threadout = self.__lastthreadID

        if self.coordstofunctions is not None and (str(lineout),str(fileout)) in self.coordstofunctions: functionout = self.coordstofunctions[(str(lineout),str(fileout))]

        if lvalue in self.varnamesmap: lvalue = self.varnamesmap[lvalue]

        rightvar = rvalue[:rvalue.rfind(" (")]

        if rightvar[0] != "&" and rightvar in self.varnamesmap: rvalue = rvalue.replace(rightvar,self.varnamesmap[rightvar],1)
        elif rightvar[0] == "&" and rightvar[1:] in self.varnamesmap: rvalue = "&"+rvalue.replace(rightvar,self.varnamesmap[rightvar[1:]],1)

        if not showbinaryencoding: rvalue = rvalue[:rvalue.rfind(" (")]

        if functionout != "": Aout = "State %s file %s line %s function %s thread %s" % (stateout,fileout,lineout,functionout,threadout)
        else: Aout = "State %s file %s line %s thread %s" % (stateout,fileout,lineout,threadout)

        Cout = "  %s=%s" % (lvalue,rvalue)

        # Filter out extra computations due to simulation code injected when translating.
        if lvalue.startswith("__cs_") and lvalue!= "__cs_message":
            return "","",""

        # Filter out __CPROVER internal states.
        if lineout == "?" and fileout == "?": return "","",""

        return (Aout,B,Cout)


    def _mapCPROVERendstate(self,A,B,C):
        mapback = {}

        """
        "Violated property:"
        "  file _cs_lazy_unsafe.c line 318 function thread3_0"
        "  assertion 0 != 0"
        "  0 != 0"

        """
        # Fetch values.
        try:
            # 1st line
            tokens = A.split()
            keys = {}

            for key,value in zip(tokens[0::2], tokens[1::2]):
                keys[key] = value

            line = filename = function = ""
        except Exception as e:
            self.warn("unable to parse counterexample final state")
            return ("","","")

        #if "file" in keys: filename = keys["file"]

        #if "line" in keys and int(keys["line"]) in mapback: line = mapback[int(keys["line"])]
        lineout = fileout = ""
        if "line" in keys: lineout,fileout = self.sbizz(int(keys["line"]))

        if "function" in keys and int(keys["line"]) in mapback:
            function = keys["function"]

            if function in self.threadindexes: thread = self.threadindexes[function]
            if function in self.threadnamesmap: function = self.threadnamesmap[function]

            A = "  file %s line %s function %s" % (fileout,lineout,function)
        else:
            A = "  file %s line %s" % (fileout,lineout)

        return (A,B,C)




