import multiprocessing
import os.path

import time, math

from multiprocessing import Process, Queue
from threading import Thread
from queue import Empty

from bin import utils
import core.module
import json
import sys
import traceback
import collections


from mpi4py import MPI
from enum import Enum

class ItrWithHasNext:
    def __init__(self, itr):
        self.itr = itr
        self.__has_next = None
        self.buffer = []
        
    def __iter__(self):
        return self
    
    def __next__(self):
        if len(self.buffer) > 0:
            item = self.buffer[0]
            self.buffer = self.buffer[1:]
            self.__has_next = True if len(self.buffer) > 0 else None
            return item
        else:
            return next(self.itr)
    
    def has_next(self):
        if self.__has_next is None:
            if len(self.buffer) > 0:
                self.__has_next = True
            else:
                try:
                    self.buffer.append(next(self.itr))
                    self.__has_next = True
                except StopIteration:
                    self.__has_next = False
        return self.__has_next


class StatusCode(Enum):
    UNSAFE = 1
    SAFE = 2
    UNKNOWN = 3
    STOP = 4
    KILL = 5
    SOLVE = 6
    READY = 7
    FINISHED = 8
    
class AnalysisTask:
    def __init__(self, lproc, confignumber, config):
        self.q = Queue()
        self.proc = lproc(self.q)
        self.thr = Thread(target=lambda: self.doTask())
        self.confignumber = confignumber
        self.config = config
        
    def doTask(self):
        self.proc.join()
        try:
            ans = self.q.get_nowait()
            MPI.COMM_WORLD.send(ans[0], dest=0, tag=ans[1])
        except Empty:
            pass
        
    def start(self):
        self.proc.start()
        self.thr.start()
        
    def kill(self):
        self.proc.kill()
        self.printStopped(self.confignumber.replace("s", ""))
        self.thr.join()
        
    def printStopped(self, index):
        print("{0:20}{1:20}".format("[#" + str(index) + "]", utils.colors.BLUE + "STOPPED" + utils.colors.NO, ))
        sys.stdout.flush()
        
    def join(self):
        self.thr.join()

rank = MPI.COMM_WORLD.Get_rank()
numberProcess = MPI.COMM_WORLD.Get_size()
server = 0

isMaster = rank == 0
isSlave = rank > 0



def start_process():
    ''' Put some debug information here if wanted
    '''
    pass


class loopAnalysisPolipa(core.module.Translator):
    __lines = {}              # cs for each thread

    __threadName = []         # NEW: name of threads, as they are found in code

    __threadbound = 0        # number of threads

    __threadIndex = {}      # index of the thread = value of threadcount when the pthread_create to that thread was discovered
       #SAT formula level instances 
    __satSwarm = False      # must become an input option, True iff we generate instances at the sat formula level
    __ctrlVarPrefix = "_cs_SwCtrl"
    __ctrlVarDefs = []
        
    __bitwidths = {}

    def init(self):
        self.addInputParam('bitwidth','custom bidwidths for integers','w',None,True)
        self.addOutputParam('bitwidth')
            
    def is_underapprox(self, t):
        return 'abstr_under' in t and t['abstr_under']
        
    def is_overapprox(self, t):
        return 'abstr_under' not in t and 'bit_width' in t
        
    def is_plain(self, t):
        return 'abstr_under' not in t and 'bit_width' not in t
        
    def getConfigNumber(self, dct):
        return [k for k in dct.keys() if len(k)>1 and k[0]=='s' and k.split("_")[0][1:].isnumeric()][0]
        
    def variations(self, w):
        timeout = self.timeout_instance
        w_nbr = self.getConfigNumber(w)
        vrs = []
        #for b in (4,8,16):
        #    vrs.append({w_nbr+"_under_"+str(b):w[w_nbr], 'abstr_under': True, 'bit_width':b, 'timeout':timeout})
        #    vrs.append({w_nbr+"_over_"+str(b):w[w_nbr], 'bit_width':b, 'timeout':timeout})
        vrs.append({w_nbr+"_plain":w[w_nbr], 'timeout':timeout})
        return vrs
        
    def propagate_kill(self): #TODO verificare se gli slave possono effettivamente parlare tra di loro, altrimenti il master uccide tutti con messaggi diretti
        rank_to_kill = [(rank+1)*2-1, (rank+1)*2]
        if rank_to_kill[0] < numberProcess:
            MPI.COMM_WORLD.send(StatusCode.KILL.value, dest=rank_to_kill[0], tag=StatusCode.KILL.value)
            if rank_to_kill[1] < numberProcess:
                MPI.COMM_WORLD.send(StatusCode.KILL.value, dest=rank_to_kill[1], tag=StatusCode.KILL.value)
                
    def stop_filter(self, t, w, bmax, underapprox, overapprox, plain):
        if t[self.getConfigNumber(t)] != w:
            return False
        if underapprox and self.is_underapprox(t) and t['bit_width'] < bmax:
            return True
        elif overapprox and self.is_overapprox(t) and t['bit_width'] < bmax:
            return True
        elif plain and self.is_plain(t):
            return True
        else:
            return False
            
    def stop(self, w, bmax, underapprox=False, overapprox=False, plain=False):
        newq = []
        for t in self.Q:
            if self.stop_filter(t, w, bmax, underapprox, overapprox, plain):
                self.printSkipped(self.getConfigNumber(t))
            else:
                newq.append(t)
        self.Q = collections.deque(newq)
        newJ = {}
        for slaveid in self.J:
            t = self.J[slaveid]
            if self.stop_filter(t, w, bmax, underapprox, overapprox, plain):
                MPI.COMM_WORLD.send(StatusCode.STOP.value, dest=slaveid, tag=StatusCode.STOP.value)
            else:
                newJ[slaveid] = t
        self.J = newJ

    def loadfromstring(self, seqcode, env, fill_only_fields=None):
        self.__lines = self.getInputParamValue('lines')
        self.__compulsoryVPs = self.getInputParamValue('compulsoryVPs')
        self.__threadName = self.getInputParamValue('threadNames')
        self.__threadIndex = self.getInputParamValue('threadIndex')
        self.__threadBound = len(self.__threadName)
        self.__satSwarm = env.sat_swarm
        self.__rounds = env.rounds
        self.timeout_instance = env.timeout_instance
        #print(self.__lines)
        #print(self.__threadName)
        #print(self.__threadBound)

        # 17/03/2021 C.J Rossouw
        # Avoid crash due to functions being called before declaration,  this uses map from before without reseting parser values
        self.__threadIndex = self.Parser.threadOccurenceIndex
        #print(self.__threadIndex)
        #sys.exit(0)
        cs = "Number of context-switch of each thread:"
        for t in self.__lines:
            cs += "\n%s : %s" %(t, str(self.__lines[t]-self.__compulsoryVPs[t]))
            
        if (self.__satSwarm): 
            self.__bitwidths = self.getInputParamValue('bitwidth')
            for t in self.__lines:
                fname = 'nondet' + str(self.__threadIndex[t])
                self.__bitwidths['',fname] = math.ceil(math.log(self.__lines[t],2))
                self.__ctrlVarDefs.append('unsigned int %s();'%fname)
                
        if isMaster:
            
            if env.show_cs:
                print(cs)
            # Generating configuration file
            if env.config_file == "":
                if not env.automatic:
                    print("Please set -A option if you want to automatically generate instances")
                env.config_file = env.inputfile[:-2] + \
                    "_auto_config%s.json" % env.suffix

            configFile = env.config_file

            if env.automatic:
                if env.isSwarm:
                    print("Generating configurations...")
            else:
                print("Loading configurations...")

            configIterator = self.generateConfigIterator(
                env, cs, configFile, env.inputfile, env.percentage)

            # Generating instances
            if env.automatic:
                if env.isSwarm:
                    if env.instances_limit == 0:
                        print("Generating instances with no limit")
                    else:
                        print("Generating instances with limit %s" %
                              env.instances_limit)
            instanceIterator = self.generateInstanceIterator(env, configIterator, seqcode)
            status = MPI.Status()
            try:
                self.Qthr = 2000 # it must be > number of slaves
                self.W = ItrWithHasNext(instanceIterator)
                self.Q = collections.deque()
                self.J = dict()
                self.S = collections.deque()
                
                while self.W.has_next() or len(self.Q) > 0 or len(self.J) > 0:
                    status = MPI.Status()
                    #print("Master listening")
                    info = MPI.COMM_WORLD.recv(source=MPI.ANY_SOURCE, tag=MPI.ANY_TAG, status=status)
                    #print("Master got", status.tag, status.Get_source(), info)
                    m = status.tag
                    slaveId = status.Get_source()
                    self.S.append(slaveId)
                    if m != StatusCode.READY.value and slaveId in self.J:
                        t = self.J[slaveId]
                        t_confNbr = self.getConfigNumber(t)
                        if m == StatusCode.SAFE.value:
                            if self.is_underapprox(t):
                                self.stop(t[t_confNbr], t['bit_width'], underapprox=True)
                            else:
                                self.stop(t[t_confNbr], float("+inf"), underapprox=True, overapprox=True, plain=True)
                        elif m == StatusCode.UNSAFE.value:
                            if self.is_overapprox(t):
                                self.stop(t[t_confNbr], t['bit_width'], overapprox=True)
                            else:
                                self.foundtime = time.time() - env.starttime
                                self.propagate_kill()
                                totaltime = time.time() - env.starttime
                                self.printIsUnsafe(totaltime, self.foundtime, env.inputfile, env.isSwarm)
                                print("Rank: ", rank, " - Master terminates its execution")
                                MPI.COMM_WORLD.Abort()
                                MPI.Finalize()
                                sys.exit(0)
                        elif m == StatusCode.UNKNOWN.value:
                            noformula = info # TODO use this info somehow (raise timeout?)
                        if slaveId in self.J:
                            del self.J[slaveId]
                    while self.W.has_next() and len(self.Q) <= self.Qthr:
                        code_wnbr_config = next(self.W)
                        w = {code_wnbr_config[1]:code_wnbr_config[2]}
                        vrs = self.variations(w)
                        self.Q.extend(vrs)
                    while len(self.Q) > 0 and len(self.S) > 0:
                        s = self.S.popleft()
                        t = self.Q.popleft()
                        self.J[s] = t
                        #print("sending", s)
                        MPI.COMM_WORLD.send(json.dumps(t), dest=s, tag=StatusCode.SOLVE.value)
                self.propagate_kill()
                totaltime = time.time() - env.starttime
                self.printIsSafe(totaltime, env.inputfile, env.isSwarm)
                print("Rank: ", rank, " - Master terminates its execution")
                MPI.COMM_WORLD.Abort()
                MPI.Finalize()
                sys.exit(0)
            except KeyboardInterrupt as e:
                print("Interrupted by user")
                sys.exit(1)
        elif isSlave:
            task = None
            status = MPI.Status()
            dirname, filename = os.path.split(os.path.abspath(env.inputfile))
            swarmdirname = dirname + "/" + filename[:-2] + '.swarm%s/' % env.suffix
            MPI.COMM_WORLD.send(StatusCode.READY.value, dest=server, tag=StatusCode.READY.value)
            while True:
                #print("sl listening")
                jsonConfig = MPI.COMM_WORLD.recv(source=server, status=status)
                #print("sl got")
                tag = status.tag
                if tag == StatusCode.SOLVE.value:
                    jsonConfigDict = json.loads(jsonConfig)
                    configNumber = self.getConfigNumber(jsonConfigDict)
                    timeout = jsonConfigDict['timeout']
                    
                    # prepare the instance
                    configintervals = jsonConfigDict[configNumber]
                    maxlabels = {}
                    output = []
                    i = 0
                    startIndex = 0
                    conf = ""
                    if 'bit_width' not in jsonConfigDict:
                        conf = "plain"
                    else:
                        bw = str(jsonConfigDict['bit_width'])
                        ou = 'under' if 'abstr_under' in jsonConfigDict and jsonConfigDict['abstr_under'] else 'over'
                        conf = ou + "_" + bw

                    while i < len(self.__threadName):
                        tName = self.__threadName[i]
                        startIndex, l = self.substitute(
                            seqcode, configintervals[tName], tName, startIndex, maxlabels)
                        listToStr = ''.join(s for s in l)
                        output.append(listToStr)
                        i += 1
                    maindriver = self.substituteMainDriver(maxlabels, seqcode[startIndex:], configintervals)
                    output.append(maindriver)

                    output[0] = self.substituteThreadLines(output[0], maxlabels)

                    if (self.__satSwarm):
                        stemp = ''.join(s for s in self.__ctrlVarDefs)
                        output.insert(0, stemp)
                    instanceGenerated = ''.join(t for t in output)
                    instanceGenerated = instanceGenerated.replace('plain.h"',conf+'.h"')
                    
                    task = AnalysisTask(lambda q:Process(target=self.backendAndReport, args=(env, instanceGenerated, configNumber, configintervals, swarmdirname, filename[:-2], timeout, q, conf)), configNumber, conf)
                    task.start()
                    
                elif tag == StatusCode.STOP.value:
                    task.kill()
                    MPI.COMM_WORLD.send(StatusCode.READY.value, dest=server, tag=StatusCode.READY.value)
                elif tag == StatusCode.KILL.value:
                    if task is not None:
                        task.kill()
                    self.propagate_kill()
                    print("Rank: ", rank, " - Slave terminates its execution")
                    sys.exit(0)
                else:
                    print("Rank: ", rank, " - received an invalid tag",tag,"arg",jsonConfig)
                    
            sys.exit(0)
        sys.exit(0)

        if env.isSwarm and env.instances_only:
            sequentializationtime = time.time() - env.starttime
            print("Time for producing $file = %0.2fs" % sequentializationtime)
        
        backendStart = time.time()
        if env.isSwarm:
            pool_size = env.cores
            if pool_size == 0:
                print("0 processes created.")
                sys.exit(0)
            if not env.instances_only:
                print("Analyzing instance(s) with " + str(env.initial_timeout) + "s timeout for " + str(
                pool_size) + " processes")
                print("======================================================")
        else:
            pool_size = 1

        if pool_size > env.instances_limit and env.instances_limit != 0:
            pool_size = env.instances_limit

        pool = multiprocessing.Pool(
            processes=pool_size, initializer=start_process)
        manager = multiprocessing.Manager()
        results = manager.Queue()
        foundbug = False
        error = False
        foundtime = 0
        sentinel = object()

        def logResults(out):
            results.put(out)

        try:
            for i in range(0, pool_size):
                instance, confignumber, configintervals = next(
                    instanceIterator, (sentinel, 0, 0))
                if instance is sentinel:
                    break
                pool.apply_async(self.backendChain, (env, instance, confignumber, configintervals, swarmdirname,
                                                     filename[:-2],), callback=logResults)
            for instance, confignumber, configintervals in instanceIterator:
                out = results.get()
                if out == "ERROR":
                    error = True
                if out is False and not foundbug:
                    foundtime = time.time() - env.starttime
                    foundbug = True
                    if env.exit_on_error:
                        break
                pool.apply_async(self.backendChain, (env, instance, confignumber, configintervals, swarmdirname,
                                                     filename[:-2],), callback=logResults)

        except KeyboardInterrupt as e:
            print("Interupted by user")
            pool.terminate()
            pool.close()
            pool.join()
            sys.exit(1)

        pool.close()
        pool.join()

        backendTime = time.time() - backendStart
        
        if env.instances_only:
            if env.isSwarm:
                print("Time for generating instances = %0.2fs" % backendTime )
                print("Instances generated in " + swarmdirname)
            # in the non swarm case, it is the only process running that signals that the sequentialization has succeded
            sys.exit(0)

        if not foundbug:
            while not results.empty():
                out = results.get()
                if out is False:
                    foundbug = True
                    foundtime = time.time() - env.starttime
                    break
                if out == "ERROR":
                    error = True
                    break    
            
        totaltime = time.time() - env.starttime
        
        if error:
            self.printError(totaltime, env.inputfile, env.isSwarm)
            return
        if foundbug:
            self.printIsUnsafe(totaltime, foundtime,
                               env.inputfile, env.isSwarm)
        else:
            self.printIsSafe(totaltime, env.inputfile, env.isSwarm)
        return
        
    def backendAndReport(self, env, instance, confignumber, configintervals, swarmdirname, filename, timeout, aa, config):
        #print("A")
        self.setOutputParam('time', timeout)
        #print("backend in")
        out = self.backendChain(env, instance, confignumber, configintervals, swarmdirname, filename, config)
        #print("backend out")
        if out == True:
            #print("send safe",StatusCode.SAFE.value, server, StatusCode.SAFE.value)
            #MPI.COMM_WORLD.send(StatusCode.SAFE.value, dest=server, tag=StatusCode.SAFE.value)
            aa.put((StatusCode.SAFE.value, StatusCode.SAFE.value))
            #print("sent safe")
        elif out == False:
            #print("send unsafe")
            #MPI.COMM_WORLD.send(StatusCode.UNSAFE.value, dest=server, tag=StatusCode.UNSAFE.value)
            aa.put((StatusCode.UNSAFE.value, StatusCode.UNSAFE.value))
        elif out.startswith("ERROR"):
            error = True
            noformula = "NOFORMULA" in out
            #print("send err ",noformula)
            #MPI.COMM_WORLD.send(noformula, dest=server, tag=StatusCode.UNKNOWN.value)
            aa.put((noformula, StatusCode.UNKNOWN.value))
        #print("B")
        return out

    def substitute(self, seqCode, list, tName, startIndex, maxlabels):
        self.__threadIndex["main_thread"] = self.__threadIndex["main"]
        if tName == 'main':
            tName = 'main_thread'
        output = []
        i = int(seqCode[startIndex:].index(tName)) + startIndex
        output.append(seqCode[startIndex:i])
        done = False
        j = i
        ICount = 0
        count = 0
        iList = 0
        cRange = range(list[iList][0], list[iList][1] + 1)
        while (i < len(seqCode) and not done):
            if seqCode[i:i+3] == '@£@':
                if seqCode[i + 3] in ('I','J'):
                    # Stop stripping at m
                    isCompulsoryVP = seqCode[i + 3] == 'J'
                    m = i   #S: +3 ?
                    output.append(seqCode[j:i])
                    stringToStrip = ''

                    l1 = count
                    #l2 = count + 1
                    if (self.__satSwarm): 
                        l1 = self.__ctrlVarPrefix + '_' +  str(self.__threadIndex[tName]) + '_' + str(l1)
                        original_tName = 'main' if tName == 'main_thread' else tName 
                        self.__bitwidths['',l1] = math.ceil(math.log(self.__lines[original_tName],2))
                    #    l2 = self.__ctrlVarPrefix + tName + str(l2)
                            
                    while(seqCode[m-5 : m] != "@£@I2"):
                        stringToStrip += seqCode[m]
                        m += 1

                    # First statement of thread
                    if count == 0:
                        while(seqCode[m-5 : m] != "@£@I3"):   #take DR_S from "@£@I2 DR_S @£@I3 S @£@I4"
                                                    stringToStrip += seqCode[m]
                                                    m += 1    

                        for sub in (
                            ("@£@I1",'__CSEQ_rawline("IF(%s,%s,t%s_%s)");' % (self.__threadIndex[tName], l1, tName, count+1)),
                            ("@£@J1",'__CSEQ_rawline("IF(%s,%s,t%s_%s)");' % (self.__threadIndex[tName], l1, tName, count+1)),
                            ("@£@L1", str(count)),
                            ("@£@L2", str(count)),
                            ("@£@I2", ''), 
                            ("@£@I3", '')):
                                stringToStrip = stringToStrip.replace(*sub)
                        output.append(stringToStrip)

                        if(self.__satSwarm):
                            fname = 'nondet' + str(self.__threadIndex[tName])
                            self.__ctrlVarDefs.append('unsigned int %s = %s();' % (l1,fname))
                            #self.__ctrlVarDefs.append('__CSEQ_rawline("__CPROVER_bitvector[1] %s = nondet1();");' % l2)

                        while(seqCode[m-5 : m] != "@£@I4"): #delete "S @£@I4" from "@£@I2 DR_S @£@I3 S @£@I4"
                                                    m += 1    
                        count += 1
                        i = m

                    
                    elif ICount in cRange or isCompulsoryVP:

                        while(seqCode[m-5 : m] != "@£@I3"):   #include "DR_S @£@I3" from " DR_S @£@I3 S @£@I4"
                                                    stringToStrip += seqCode[m]
                                                    m += 1    

                        while(seqCode[m-5 : m] != "@£@I4"): #delete "S @£@I4" from "@£@I2 DR_S @£@I3 S @£@I4"
                                                    m += 1    

                        for sub in (
                            ("@£@I1", '__CSEQ_rawline("t%s_%s:"); __CSEQ_rawline("IF(%s,%s,t%s_%s)");' % (tName, count, self.__threadIndex[tName], l1, tName, count + 1 )),
                            ("@£@J1", '__CSEQ_rawline("t%s_%s:"); __CSEQ_rawline("IF(%s,%s,t%s_%s)");' % (tName, count, self.__threadIndex[tName], l1, tName, count + 1 )),
                            ("@£@L1", str(count)),
                            ("@£@L2", str(count)),
                            ("@£@I2", ''), 
                            ("@£@I3", '')):
                                stringToStrip = stringToStrip.replace(*sub)
                        output.append(stringToStrip)

                        if(self.__satSwarm):
                            fname = 'nondet' + str(self.__threadIndex[tName])
                            self.__ctrlVarDefs.append('unsigned int %s = %s();' % (l1,fname))

                        count += 1
                        if isCompulsoryVP: # that was a compulsory vp. You shouldn't be counting it, treat it like it was invisible
                            ICount -= 1
                        elif ICount == list[iList][1] and iList < len(list) - 1:
                            iList += 1
                            cRange = range(list[iList][0], list[iList][1] + 1)
                            
                        
                        i = m
                    
                    else:
                        while(seqCode[m-5 : m] != "@£@I3"):   #delete "DR_S @£@I3"  from "DR_S @£@I3 S @£@I4"
                                                    m += 1    
                        stringToStrip = ''  #delete portion "@£@I1...@£@I2"

                        while(seqCode[m-5 : m] != "@£@I4"): #include "S @£@I4" from "DR_S @£@I3 S @£@I4"
                                                    stringToStrip += seqCode[m]
                                                    m += 1    

                        stringToStrip = stringToStrip.replace('@£@I4','')
                        output.append(stringToStrip)


                        i = m
#                        if seqCode[j:i] != '':
#                            output.append(seqCode[j:i])
#                        i = m
                    
                    j = i
                    ICount += 1

                # Guard label
                elif seqCode[i + 3] == 'G':
                    s = seqCode[j:i] + '__CSEQ_assume( __cs_pc_cs[%s] >= %s );' % (
                        self.__threadIndex[tName], count)
                    output.append(s)
                    i += 4
                    j = i

                # Last statement of thread
                else:
                    s = seqCode[j:i] + '__CSEQ_rawline("t%s_%s: ");' % (tName, count)
                    output.append(s)
                    i += 4
                    done = True
                    maxlabels[tName] = count
            else:
                i += 1
        del self.__threadIndex["main_thread"]
        return i, output

    def substituteMainDriver(self, maxlabels, mainDriver, configintervals):
        output = ''
        #w_vars = set()
        cs_vars = {t_name:["__cs_"+str(i)+"_"+str(r) for r in range(self.__rounds + (1 if t_name == "main" else 0))] for (i,t_name) in enumerate(self.__threadName)}
        wnd_assumes = []
        for tname in configintervals:
            shouldStart = 1
            for i in range(len(configintervals[tname])):
                if configintervals[tname][i][0] != shouldStart:
                    for ivl in configintervals[tname][i:]:
                        wnd_assumes.append('__CPROVER_assume('+' || '.join('('+vrs+' >= '+str(ivl[0])+' && '+vrs+' <= '+str(ivl[1])+')' for vrs in cs_vars[tname])+');')
                        #w_vars.add('w_'+tname+'_'+str(ivl[0])+'_'+str(ivl[1]))
                    break
                else:
                    shouldStart = configintervals[tname][i][1]+1
        
        i = 0
        #Implementare per quando ci sono piu di 99 thread
        threadToCheckWindows = None
        threadToCheckNbr = None
        hasEverFoundOpenBrace = False
        ctxSwitchIdx = 0 # counter for context switch blocks. It should be in [0, #rounds * #threads]
        while i < len(mainDriver):
            if mainDriver[i:i+3] == '@£@':
                numthread = mainDriver[i+5]
                extralen = 0
                if len(mainDriver) >= i+7 and mainDriver[i+6] in "0123456789":
                    numthread += mainDriver[i+6]
                    extralen = 1
                #print("numthread: " + numthread)
                tname = self.__threadName[int(numthread)]
                threadToCheckWindows = tname
                threadToCheckNbr = numthread
                if tname == 'main':
                    tname = 'main_thread'
                maxthreadlabel = maxlabels[tname]
                output += str(maxthreadlabel)
                i+=6+extralen
            elif mainDriver[i] == '{' and not hasEverFoundOpenBrace:
                hasEverFoundOpenBrace = True
                decl = ""
                #if len(w_vars) > 0:
                #    decl = '__CSEQ_rawline("unsigned __CPROVER_bitvector[1] '+', '.join(w+" = 0" for w in w_vars)+';");'
                decl_cs = 'unsigned int '+(', '.join(', '.join(csv) for csv in cs_vars.values()))+';'
                output += mainDriver[i] + "\n" + decl +"\n" + decl_cs +"\n" + "\n".join(wnd_assumes)+"\n"
                i+=1
            elif mainDriver[i] == '\n' and threadToCheckWindows is not None:
                conds = []
                cs_pc_cs = "__cs_pc_cs["+str(threadToCheckNbr)+"]"
                roundIdx = ctxSwitchIdx//len(cs_vars) #len(cs_vars) == number of threads
                assume = '__CPROVER_assume(__cs_'+str(threadToCheckNbr)+'_'+str(roundIdx)+' == '+cs_pc_cs+');'
                ctxSwitchIdx+=1
                
                #for ivl in configintervals[threadToCheckWindows]:
                #    #w_var = 'w_'+threadToCheckWindows+'_'+str(ivl[0])+'_'+str(ivl[1])
                #    #if w_var in w_vars:
                #    #    conds.append('__CSEQ_rawline("'+w_var+' |= ('+cs_pc_cs+' >= '+str(ivl[0])+' && '+cs_pc_cs+' <= '+str(ivl[1])+');");')
                output += mainDriver[i] + mainDriver[i].join([assume]+conds) + mainDriver[i]
                threadToCheckWindows = None
                threadToCheckNbr = None
                i+=1
            elif mainDriver[i:i+9] == 'return 0;':
                assume = ""
                #if len(w_vars) > 0:
                #    assume = '__CSEQ_rawline("__CPROVER_assume('+' && '.join(w_vars)+');");\n'
                output += assume + mainDriver[i:i+9]
                i += 9
            else:
                output += mainDriver[i]
                i+=1
        return output

    def substituteThreadLines(self, seqcode, maxlabels):
        threadsize = ""
        numthread = 0
        for i in maxlabels:
            threadsize += " %s" % maxlabels[i]
            if numthread < self.__threadBound - 1:
                threadsize += ","
                numthread+=1
        output = seqcode.replace("$THREADSIZE", threadsize)
        return output

    def generateConfigIterator(self, env, lines, configfile, inputfile, percentage):
        if percentage and env.isSwarm:
            configGen = utils.ConfigGeneratorPercentage(lines, env.window_percent, env.picked_window,
                                                        env.instances_limit, consecutive=(
                                                            not env.scatter),
                                                        double=env.shifted_window, skiplist=env.skip_thread)
            singleConfigFilename = configfile + ".tmp"
            lenConf, result, generatedData = configGen.generatingConfigPercentage(singleConfigFilename,
                                                  softLimit=env.soft_limit,
                                                  hardLimit=env.hard_limit,
                                                  verbose=env.debug,
                                                  randomness=(not env.no_random),
                                                 start=env.start_sample)

            return configGen.generatorConfigIterator(singleConfigFilename, lenConf, generatedData)

        else:
            configGen = utils.ConfigGenerator(lines, percentage, env.cluster_config, env.window_length,
                                              env.window_percent,
                                              env.picked_window,
                                              env.instances_limit, env.config_only, consecutive=(
                                                  not env.scatter),
                                              double=env.shifted_window, skiplist=env.skip_thread)
            singleConfigFilename = configfile + ".tmp"
            if env.isSwarm:
                if env.automatic:
                    # Create a generator
                    # Overwrite configuration file
                    return configGen.generatingConfig(configfile, singleConfigFilename, inputfile,
                                                      softLimit=env.soft_limit,
                                                      hardLimit=env.hard_limit, randomness=(
                                                          not env.no_random),
                                                      start=env.start_sample)
                else:
                    with open(configfile, "r") as fd:
                        generatedData = json.load(fd)
                    return configGen.generatorConfigIterator(singleConfigFilename, len(generatedData), generatedData)
            else:
                conf = {
                    's0': {}
                }
                for t in self.__lines:
                    conf["s0"][t] = [[1, self.__lines[t]]]
                return configGen.generatorConfigIterator(singleConfigFilename, len(conf), conf)

    def generateInstanceIterator(self, env, configIterator, seqCode):
        if env.config_only:
            sys.exit(0)
        for config in configIterator:
            with open(config[0], "r") as config:        
                maxlabels = {}
                jsonConfig = json.load(config)
                configNumber, configintervals = dict(jsonConfig).popitem()
                output = []
                i = 0
                startIndex = 0

                while i < len(self.__threadName):    
                    tName = self.__threadName[i]
                    startIndex, l = self.substitute(
                                                seqCode, configintervals[tName], tName, startIndex, maxlabels)
                    listToStr = ''.join(s for s in l)
                    output.append(listToStr)
                    i += 1
                maindriver = self.substituteMainDriver(maxlabels, seqCode[startIndex:], configintervals)
                output.append(maindriver)

                output[0] = self.substituteThreadLines(output[0], maxlabels)
            if (self.__satSwarm):
                stemp = ''.join(s for s in self.__ctrlVarDefs)
                output.insert(0,stemp)
                #print(stemp)
                #sys.exit(0)
            instanceGenerated = ''.join(t for t in output)
            #with open("test.c", 'w') as fd:
                #fd.write(instanceGenerated)
            #sys.exit()
            yield instanceGenerated, configNumber, configintervals

    def backendChain(self, env, instance, confignumber, configintervals, swarmdirname, filename, config):
        output = instance
        analysistime = time.time()
        # print (env.transforms)
        for i, m in enumerate(env.backendmodules):
            # print(m.getname() + "QUI")
            try:
                timeBefore = time.time()
                if env.debug:
                    print("/* " + m.getname())
                m.initParams(env)
                m.setInstanceInfo(swarmdirname, filename, confignumber, configintervals)
                #	print(output)
                #	sys.exit(0)
                if (self.__satSwarm):
                    self.setOutputParam('bitwidth', self.__bitwidths)
                m.loadfromstring(output, env)
                output = m.getoutput()
                # print(output)
                # sys.exit(0)

                # linemapping only works on Translator (C-to-C) modules
                if "inputtooutput" in dir(m):
                    env.maps.append(m.outputtoinput)
                    env.lastlinenoinlastmodule = m.output.count("\n")
                # core.utils.saveFile("log/__mapO2I___%s.c" % (m.getname()), str(m.outputtoinput))

                if not env.isSwarm and env.debug:
                    fileno = "0" + str(env.transforms + 1).zfill(2)
                    # core.utils.saveFile("log/_%s_input___%s.c" % (fileno, m.getname()), m.input)
                    # core.utils.saveFile("log/_%s_output__%s.c" % (fileno, m.getname()), m.output)
                    print("[%s] ok %0.2fs */" % (fileno, int(time.time()) - int(timeBefore)))
                    sys.stdout.flush()

                env.transforms += 1

            except KeyboardInterrupt as e:
                print("Chain interrupted by user")
                sys.exit(1)
            except Exception as e:
                traceback.print_exc()
                raise e
        if env.instances_only:
            if not env.isSwarm:
                print("Sequentialization successfully completed.")
            return True
        verifierResult = output
        memsize = self.getInputParamValue('memsize')

        processedResult = self.processResult(verifierResult, env.backend)
        # print("processedResult: " + processedResult)
        analysistime = time.time() - analysistime
        if processedResult == "TRUE":
            if env.isSwarm:
                self.printNoFoundBug(confignumber.replace(
                    "s", ""), memsize, analysistime)
            return True
        elif processedResult == "FALSE":
            if env.isSwarm:
                self.printFoundBug(confignumber.replace(
                    "s", ""), memsize, analysistime)
            # controesempio è in errorTrace se cex settata, salvare in file per swarm e stampare a video per noSwarm
            return False

        else:
            noformula = "NOFORMULA" in processedResult
            if env.isSwarm:
                self.printUnknown(confignumber.replace(
                    "s", ""),noformula=noformula)
            return "ERROR" + (" NOFORMULA" if noformula else "")
        sys.stdout.flush()

    def printUnknown(self, index, noformula=False):
        print("{0:20}{1:20}".format("[#" + str(index) + "]", utils.colors.YELLOW + "UNKNOWN" + (" NOFORMULA" if noformula else "") + utils.colors.NO, ))
        sys.stdout.flush()

    def printNoFoundBug(self, index, memsize, analysistime):
        print("{0:20}{1:20}{2:10}{3:10}".format("[#" + str(index) + "]", utils.colors.GREEN + "SAFE" + utils.colors.NO,
                                                "%0.2fs " % analysistime, self.calcMem(memsize)))
        sys.stdout.flush()

    def printFoundBug(self, index, memsize, analysistime):
        print("{0:20}{1:20}{2:10}{3:10}".format("[#" + str(index) + "]", utils.colors.RED + "UNSAFE" + utils.colors.NO,
                                                "%0.2fs " % analysistime, self.calcMem(memsize)))
        sys.stdout.flush()
        
    def printSkipped(self, index):
        print("{0:20}{1:20}".format("[#" + str(index) + "]", utils.colors.BLUE + "SKIPPED" + utils.colors.NO, ))
        sys.stdout.flush()

    def printIsSafe(self, totalTime, inputfile, isSwarm):
        if isSwarm:
            print("======================================================")
            print("Cannot find bugs in this configuration")
        print(inputfile + utils.colors.GREEN + " TRUE " +
              utils.colors.NO + ", %0.2fs" % totalTime)
        sys.stdout.flush()

    def printIsUnsafe(self, totalTime, foundtime, inputfile, isSwarm):
        if isSwarm:
            print("======================================================")
            print("Bugs found in this configuration")
            print("Found time : " + "%0.2fs" % foundtime)
        print(inputfile + utils.colors.RED + " FALSE " +
              utils.colors.NO + ", %0.2fs" % totalTime)
        sys.stdout.flush()

    def printError(self, totalTime, inputfile, isSwarm):
        if isSwarm:
            print("======================================================")
        print(inputfile + utils.colors.YELLOW + " UNKNOWN " +
            utils.colors.NO + ", %0.2fs" % totalTime)
        sys.stdout.flush()

    def processResult(self, result, format):
        # Expressions to check for from the log to see whether verification went fine.
        verificationOK = {}
        # BMC backends
        verificationOK["esbmc"] = "VERIFICATION SUCCESSFUL"
        verificationOK["cbmc"] = "VERIFICATION SUCCESSFUL"
        verificationOK["blitz"] = "VERIFICATION SUCCESSFUL"
        verificationOK["llbmc"] = "No error detected."
        # AI
        verificationOK["framac"] = "__FRAMAC_spec"
        verificationOK["2ls"] = "VERIFICATION SUCCESSFUL"
        verificationOK["pagai"] = "RESULT: TRUE"  # TODO
        verificationOK["interproc"] = "TOBEPROCESSED"
        verificationOK["satabs"] = "VERIFICATION SUCCESSFUL"
        verificationOK["cpachecker"] = "Verification result: SAFE. No error path found by chosen configuration."
        # Testing
        verificationOK["klee"] = "NOSUCHTHINGFORKLEE"
        verificationOK["smack"] = "Finished with 1 verified, 0 errors"
        # Concurrent
        verificationOK["concurinterproc"] = "TOBEPROCESSED"
        verificationOK["impara"] = "VERIFICATION SUCCESSFUL"
        verificationOK["seahorn"] = "BRUNCH_STAT Result TRUE"

        # Expressions to check for from the log to check whether verification failed.
        verificationFAIL = {}
        # BMC
        verificationFAIL["cbmc"] = "VERIFICATION FAILED"
        verificationFAIL["esbmc"] = "VERIFICATION FAILED"
        verificationFAIL["blitz"] = "VERIFICATION FAILED"
        verificationFAIL["llbmc"] = "Error detected."
        # AI
        verificationFAIL["framac"] = "__FRAMAC_spec"
        verificationFAIL["2ls"] = "VERIFICATION FAILED"
        verificationFAIL["pagai"] = "RESULT: UNKNOWN"
        verificationFAIL["interproc"] = "TOBEPROCESSED"
        verificationFAIL["satabs"] = "VERIFICATION FAILED"
        verificationFAIL["cpachecker"] = "Verification result: UNSAFE."
        # testing
        verificationFAIL["smack"] = "Finished with 0 verified,"
        verificationFAIL["klee"] = "ASSERTION FAIL: "
        # Concurrent
        verificationFAIL["concurinterproc"] = "TOBEPROCESSED"
        verificationFAIL["impara"] = "VERIFICATION FAILED"
        verificationFAIL["seahorn"] = "BRUNCH_STAT Result FALSE"

        # report analysis details

        outcome = ""

        if result != "":
            backendAnswer = result if format != "klee" else "err"
            if format in ("cbmc", "esbmc",):
                for line in backendAnswer.splitlines():
                    if " variables, " in line:
                        splitline = line.split()
                        variables = splitline[0]
                        clauses = splitline[2]
                    if verificationOK[format] in line:
                        outcome = "TRUE"
                        break
                    elif verificationFAIL[format] in line:
                        outcome = "FALSE"
                        break
        else:
            outcome = "UNKNOWN"
        return outcome

    def calcMem(self, hmemsize):
        if (sys.platform.startswith('linux')):
            hmemsize = hmemsize / 1024.0
        elif (sys.platform.startswith('darwin')):
            hmemsize = hmemsize / (1024.0 * 1024.0)
        else:
            hmemsize = hmemsize / (1024.0)
        return "%0.2fMB" % (hmemsize)
