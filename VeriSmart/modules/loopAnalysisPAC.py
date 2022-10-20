import multiprocessing
import os.path
import signal

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
        self.printStopped(self.confignumber.replace("s", ""), config=self.config)
        self.thr.join()
        
    def printStopped(self, index, config=""):
        print("{0:20}{1:20}".format("[#" + str(index) + (" "+config if len(config) > 0 else "") + "]", utils.colors.BLUE + "STOPPED" + utils.colors.NO, ))
        sys.stdout.flush()
        
    def join(self):
        self.thr.join()

rank = MPI.COMM_WORLD.Get_rank()
numberProcess = MPI.COMM_WORLD.Get_size()
server = 0

isMaster = rank == 0
isSlave = rank > 0



hashtable = {}
reportHashtable = {}



#service_name = 'compute'
#port_name = MPI.Open_port()
#info = MPI.Info.Create()
#info.Set("ompi_global_scope", "true")
#MPI.Publish_name(service_name, port_name, info)
#inter_comm = comm.Accept(port_name, info)



def start_process():
    ''' Put some debug information here if wanted
    '''
    pass


class loopAnalysisPAC(core.module.Translator):
    __lines = {}  # cs for each thread

    __threadName = []  # NEW: name of threads, as they are found in code

    __threadbound = 0  # number of threads

    __threadIndex = {}  # index of the thread = value of threadcount when the pthread_create to that thread was discovered
    # SAT formula level instances
    __satSwarm = False  # must become an input option, True iff we generate instances at the sat formula level
    __ctrlVarPrefix = "_cs_SwCtrl"
    __ctrlVarDefs = []

    __bitwidths = {}
    
    windowProgr = 0

    def __init__(self):
        super().__init__()
        self.activeProcess = 0
        self.foundtime = 0
        self.isUnsafe = False
        self.isUnknown = False

    def init(self):
        self.addInputParam('bitwidth', 'custom bidwidths for integers', 'w', None, True)
        self.addOutputParam('bitwidth')
        
    def getNewConfigNumber(self):
        ans = 's'+str(self.windowProgr)
        self.windowProgr+=1
        return ans
        
    def getConfigNumber(self, dct):
        return [k for k in dct.keys() if len(k)>1 and k[0]=='s' and k[1:].isnumeric()][0]
        
    def firstWindow(self):
        conf = {
            "s-1": {}
        }
        for t in self.__lines:
            conf["s-1"][t] = [[1, self.__lines[t] - self.__compulsoryVPs[t]]]
        return conf
        
    def thread_VP_count(self, t):
        return sum(k[1]-k[0]+1 for k in t)
        
    def delete_vp(self, t, frm, to): #Remove ([from, to]  0-indexed)-th VPs. E.g. delete_vp([[1 3] [7 9]], 4, 6) = [[1 3] [7 7]]
        out = []
        blkStart = 0
        for blk in t:
            # each block is [blk[0]  blk[1]] !
            blkEnd = blkStart + blk[1]-blk[0]
            # that corresponds to indicies [blkStart  blkEnd]
            
            # Cases (they are exaustive under invariant frm <= to and blkStart <= blkEnd):
            # frm <= to < blkStart <= blkEnd: keep everything until end
            # frm <= blkStart <= blkEnd <= to: skip block and continue
            # blkStart <= blkEnd < frm <= to: keep and continue
            # frm <= blkStart <= to < blkEnd: keep last (blkEnd-to-1) and keep everything until end
            # blkStart < frm <= blkEnd <= to: keep first (frm-blkStart-1) and continue
            # blkStart < frm <= to < blkEnd: keep first (frm-blkStart-1) and last (blkEnd-to-1) and keep everything until end
            
            
            
            if frm <= to and to < blkStart and blkStart <= blkEnd:
                out.append(blk)
            elif frm <= blkStart and blkStart <= blkEnd and blkEnd <= to:
                pass
            elif blkStart <= blkEnd and blkEnd < frm and frm <= to:
                out.append(blk)
            elif frm <= blkStart and blkStart <= to and to < blkEnd:
                nbk = [blk[1] - (blkEnd-to-1), blk[1]]
                if nbk[0] <= nbk[1]:
                    out.append(nbk)
            elif blkStart < frm and frm <= blkEnd and blkEnd <= to:
                nbk = [blk[0], blk[0]+frm-blkStart-1]
                if nbk[0] <= nbk[1]:
                    out.append(nbk)
            elif blkStart < frm and frm <= to and to < blkEnd:
                nbk1 = [blk[0], blk[0]+frm-blkStart-1]
                if nbk1[0] <= nbk1[1]:
                    out.append(nbk1)
                nbk2 = [blk[1]-(blkEnd-to-1), blk[1]]
                if nbk2[0] <= nbk2[1]:
                    out.append(nbk2)
            else:
                assert(False)
            blkStart = blkEnd+1
        return out
        
    def splitWindow(self, conf, env):
        parts = env.rounds+1
        max_tlen = 0
        max_tname = None
        confNumber = self.getConfigNumber(conf)
        for tname in conf[confNumber]:
            tlen = self.thread_VP_count(conf[confNumber][tname])
            if tlen > max_tlen:
                max_tlen = tlen
                max_tname = tname
        if parts > max_tlen:
            parts = max_tlen
        out_wind = []
        for i in range(parts):
            ow = {"s-1":{t:v for (t,v) in conf[confNumber].items() if t != max_tname}}
            ow["s-1"][max_tname] = self.delete_vp(conf[confNumber][max_tname], i*max_tlen//parts, (i+1)*max_tlen//parts-1)
            out_wind.append(ow)
        return out_wind
        
    def is_underapprox(self, t):
        return 'abstr_under' in t and t['abstr_under']
        
    def is_overapprox(self, t):
        return 'abstr_under' not in t and 'bit_width' in t
        
    def is_plain(self, t):
        return 'abstr_under' not in t and 'bit_width' not in t
        
    def variations(self, conf):
        timeout = self.timeout_instance
        vrs = []
        for b in (4,8,16):
            vrs.append({self.getNewConfigNumber():conf["s-1"], 'abstr_under': True, 'bit_width':b, 'timeout':timeout})
            vrs.append({self.getNewConfigNumber():conf["s-1"], 'bit_width':b, 'timeout':timeout})
        vrs.append({self.getNewConfigNumber():conf["s-1"], 'timeout':timeout})
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
                conf = "?"
                if 'bit_width' not in t:
                    conf = "plain"
                else:
                    bw = str(t['bit_width'])
                    ou = 'under' if 'abstr_under' in t and t['abstr_under'] else 'over'
                    conf = ou + "_" + bw
                self.printSkipped(self.getConfigNumber(t), config=conf)
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
        
    def wont_conclude(self, w):
        for t in self.Q:
            if t[self.getConfigNumber(t)] == w:
                return False
        for t in self.J.values():
            if t[self.getConfigNumber(t)] == w:
                return False
        return True

    def loadfromstring(self, seqcode, env, fill_only_fields=None):
        self.__lines = self.getInputParamValue('lines')
        self.__compulsoryVPs = self.getInputParamValue('compulsoryVPs')
        self.__threadName = self.getInputParamValue('threadNames')
        self.__threadIndex = self.getInputParamValue('threadIndex')
        self.__threadBound = len(self.__threadName)
        self.__satSwarm = env.sat_swarm
        self.timeout_instance = env.timeout_instance
        # print(self.__lines)
        # print(self.__threadName)
        # print(self.__threadBound)

        # 17/03/2021 C.J Rossouw
        # Avoid crash due to functions being called before declaration,  this uses map from before without reseting parser values
        self.__threadIndex = self.Parser.threadOccurenceIndex
        # print(self.__threadIndex)
        # sys.exit(0)

        if (self.__satSwarm):
            self.__bitwidths = self.getInputParamValue('bitwidth')
            for t in self.__lines: # TODO: careful with compulsory vps
                fname = 'nondet' + str(self.__threadIndex[t])
                self.__bitwidths['', fname] = math.ceil(math.log(self.__lines[t], 2))
                self.__ctrlVarDefs.append('unsigned int %s();' % fname)

        if isMaster:
            status = MPI.Status()
            try:
                self.Qthr = 2000 # it must be > number of slaves
                self.W = collections.deque([self.firstWindow()])
                self.Q = collections.deque()
                self.J = dict()
                self.S = collections.deque()
                
                while len(self.W) > 0 or len(self.Q) > 0 or len(self.J) > 0:
                    status = MPI.Status()
                    #print("listening",status)
                    info = MPI.COMM_WORLD.recv(source=MPI.ANY_SOURCE, tag=MPI.ANY_TAG, status=status)
                    #print("got", status.tag, status.Get_source(), info)
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
                        #TODO test if (m != StatusCode.SAFE.value or self.is_underapprox(t)) and self.wont_conclude(t[t_confNbr]):
                        #    self.W.extend(self.splitWindow(t,env))
                    while len(self.W) > 0 and len(self.Q) <= self.Qthr:
                        w = self.W.popleft()
                        vrs = self.variations(w)
                        self.Q.extend(vrs)
                        # TODO test: if mode == FIND_WSIZE
                        self.W.append(self.splitWindow(vts[0], env)[0])
                    while len(self.Q) > 0 and len(self.S) > 0:
                        s = self.S.popleft()
                        t = self.Q.pop() #.popleft()
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
                    configNumber = [k for k in jsonConfigDict.keys() if len(k)>1 and k[0]=='s' and k[1:].isnumeric()][0]
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
                    maindriver = self.substituteMainDriver(maxlabels, seqcode[startIndex:])
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
        
        ''''
            
        ########################################################################################################
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

        configIterator = self.masterGeneratesConfigIterator(
            env, cs, configFile, env.inputfile, env.percentage)

        if env.config_only:
            MPI.Finalize()
            sys.exit(0)

        # Generating instances
        if env.automatic:
            if env.isSwarm:
                if env.instances_limit == 0:
                    print("Generating instances with no limit")
                else:
                    print("Generating instances with limit %s" %
                          env.instances_limit)

    dirname, filename = os.path.split(os.path.abspath(env.inputfile))
    swarmdirname = dirname + "/" + filename[:-2] + '.swarm%s/' % env.suffix

    if isMaster:

        try:
            for config in configIterator:
                with open(config[0], "r") as config:
                    jsonConfig = json.load(config)

                    # distributed verismart:        mpirun -np 4 --oversubscribe --quiet python3 ./verismart.py -i peterson.c --master-slave --stop-on-fail
                    # distributed cbmc verismart:      mpirun -np 1 --ompi-server file:address_ompi_server python3 ./verismart.py -i peterson.c
                    # print(str(jsonConfig).replace("\'", "\""))
                    # encoded_string = str(jsonConfig).replace("\'", "\"").encode()
                    # byte_array = bytearray(encoded_string)
                    # inter_comm.Send([byte_array, MPI.CHAR], dest=0)

                    self.masterSendTile(env, jsonConfig)

                    # MPI.Unpublish_name(service_name, port_name)
                    # MPI.Close_port(port_name)
                    # inter_comm.Disconnect()

            self.masterKillSlaves()

            totaltime = time.time() - env.starttime

            if self.isUnsafe:
                self.printIsUnsafe(totaltime, self.foundtime, env.inputfile, env.isSwarm)
            elif self.isUnknown:
                self.printError(totaltime, env.inputfile, env.isSwarm)
            else:
                self.printIsSafe(totaltime, env.inputfile, env.isSwarm)

            for jsonConfigTmp, result in reportHashtable.items():
                print(jsonConfigTmp, result)

            print("Rank: ", rank, " - Master terminates its execution")
            comm.Abort()
            MPI.Finalize()
            sys.exit(0)

        except KeyboardInterrupt as e:
            print("Interrupted by user")
            sys.exit(1)

    elif isSlave:

        queue = multiprocessing.Queue()

        if env.exit_on_error:
            slaveAnalysisProcess = Process(target=self.slaveAnalysis, args=(seqcode, env, fill_only_fields, queue))
            slaveAnalysisProcess.start()

            while True:
                jsonConfig = comm.recv(source=server, status=status)
                tag = status.tag
                if tag == StatusCode.KILL.value:
                    while not queue.empty():
                        queue.get()
                    queue.close()
                    queue.join_thread()
                    slaveAnalysisProcess.kill()
                    print("Rank: ", rank, " - Slave terminates its execution")
                    sys.exit(0)
                else:
                    queue.put(jsonConfig)

        self.slaveAnalysis(seqcode, env, fill_only_fields)
        return'''
            
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
            if seqCode[i:i + 3] == '@£@':
                if seqCode[i + 3] in ('I', 'J'):
                    # Stop stripping at m
                    isCompulsoryVP = seqCode[i + 3] == 'J'
                    m = i  # S: +3 ?
                    output.append(seqCode[j:i])
                    stringToStrip = ''

                    l1 = count
                    # l2 = count + 1
                    if (self.__satSwarm):
                        l1 = self.__ctrlVarPrefix + '_' + str(self.__threadIndex[tName]) + '_' + str(l1)
                        original_tName = 'main' if tName == 'main_thread' else tName
                        self.__bitwidths['', l1] = math.ceil(math.log(self.__lines[original_tName], 2))
                    #	l2 = self.__ctrlVarPrefix + tName + str(l2)

                    while (seqCode[m - 5: m] != "@£@I2"):
                        stringToStrip += seqCode[m]
                        m += 1

                    # First statement of thread
                    if count == 0:
                        while (seqCode[m - 5: m] != "@£@I3"):  # take DR_S from "@£@I2 DR_S @£@I3 S @£@I4"
                            stringToStrip += seqCode[m]
                            m += 1

                        for sub in (
                                ("@£@I1", '__CSEQ_rawline("IF(%s,%s,t%s_%s)");' % (
                                        self.__threadIndex[tName], l1, tName, count + 1)),
                                ("@£@J1", '__CSEQ_rawline("IF(%s,%s,t%s_%s)");' % (
                                        self.__threadIndex[tName], l1, tName, count + 1)),
                                ("@£@L1", str(count)),
                                ("@£@L2", str(count)),
                                ("@£@I2", ''),
                                ("@£@I3", '')):
                            stringToStrip = stringToStrip.replace(*sub)
                        output.append(stringToStrip)

                        if (self.__satSwarm):
                            fname = 'nondet' + str(self.__threadIndex[tName])
                            self.__ctrlVarDefs.append('unsigned int %s = %s();' % (l1, fname))
                        # self.__ctrlVarDefs.append('__CSEQ_rawline("__CPROVER_bitvector[1] %s = nondet1();");' % l2)

                        while (seqCode[m - 5: m] != "@£@I4"):  # delete "S @£@I4" from "@£@I2 DR_S @£@I3 S @£@I4"
                            m += 1
                        count += 1
                        i = m


                    elif ICount in cRange or isCompulsoryVP:

                        while (seqCode[m - 5: m] != "@£@I3"):  # include "DR_S @£@I3" from " DR_S @£@I3 S @£@I4"
                            stringToStrip += seqCode[m]
                            m += 1

                        while (seqCode[m - 5: m] != "@£@I4"):  # delete "S @£@I4" from "@£@I2 DR_S @£@I3 S @£@I4"
                            m += 1

                        for sub in (
                                ("@£@I1", '__CSEQ_rawline("t%s_%s:"); __CSEQ_rawline("IF(%s,%s,t%s_%s)");' % (
                                        tName, count, self.__threadIndex[tName], l1, tName, count + 1)),
                                ("@£@J1", '__CSEQ_rawline("t%s_%s:"); __CSEQ_rawline("IF(%s,%s,t%s_%s)");' % (
                                        tName, count, self.__threadIndex[tName], l1, tName, count + 1)),
                                ("@£@L1", str(count)),
                                ("@£@L2", str(count)),
                                ("@£@I2", ''),
                                ("@£@I3", '')):
                            stringToStrip = stringToStrip.replace(*sub)
                        output.append(stringToStrip)

                        if (self.__satSwarm):
                            fname = 'nondet' + str(self.__threadIndex[tName])
                            self.__ctrlVarDefs.append('unsigned int %s = %s();' % (l1, fname))

                        count += 1
                        if isCompulsoryVP:  # that was a compulsory vp. You shouldn't be counting it, treat it like it was invisible
                            ICount -= 1
                        elif ICount == list[iList][1] and iList < len(list) - 1:
                            iList += 1
                            cRange = range(list[iList][0], list[iList][1] + 1)

                        i = m

                    else:
                        while (seqCode[m - 5: m] != "@£@I3"):  # delete "DR_S @£@I3"  from "DR_S @£@I3 S @£@I4"
                            m += 1
                        stringToStrip = ''  # delete portion "@£@I1...@£@I2"

                        while (seqCode[m - 5: m] != "@£@I4"):  # include "S @£@I4" from "DR_S @£@I3 S @£@I4"
                            stringToStrip += seqCode[m]
                            m += 1

                        stringToStrip = stringToStrip.replace('@£@I4', '')
                        output.append(stringToStrip)

                        i = m
                    #						if seqCode[j:i] != '':
                    #							output.append(seqCode[j:i])
                    #						i = m

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

    def substituteMainDriver(self, maxlabels, mainDriver):
        output = ''
        i = 0
        # Implementare per quando ci sono piu di 99 thread
        while i < len(mainDriver):
            if mainDriver[i:i + 3] == '@£@':
                numthread = mainDriver[i + 5]
                extralen = 0
                if len(mainDriver) >= i+7 and mainDriver[i+6] in "0123456789":
                    numthread += mainDriver[i+6]
                    extralen = 1
                # print("numthread: " + numthread)
                tname = self.__threadName[int(numthread)]
                if tname == 'main':
                    tname = 'main_thread'
                maxthreadlabel = maxlabels[tname]
                output += str(maxthreadlabel)
                i += 6+extralen
            else:
                output += mainDriver[i]
                i += 1
        return output

    def substituteThreadLines(self, seqcode, maxlabels):
        threadsize = ""
        numthread = 0
        for i in maxlabels:
            threadsize += " %s" % maxlabels[i]
            if numthread < self.__threadBound - 1:
                threadsize += ","
                numthread += 1
        output = seqcode.replace("$THREADSIZE", threadsize)
        return output

    def masterGeneratesConfigIterator(self, env, lines, configfile, inputfile, percentage):
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

    def slaveGeneratesInstanceIterator(self, env, seqCode, queue=None):

        comm.send(rank, dest=server, tag=StatusCode.REQUEST.value)

        while True:

            jsonConfig = ""
            if env.exit_on_error == False:

                #jsonConfig = comm.recv(source=server, status=status)

                tag = status.tag

                if tag == StatusCode.KILL.value:
                    print("Rank: ", rank, " - Slave terminates its execution")
                    sys.exit(0)

            else:
                jsonConfig = queue.get()

            configNumber, configintervals = dict(jsonConfig).popitem()
            maxlabels = {}
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
            maindriver = self.substituteMainDriver(maxlabels, seqCode[startIndex:])
            output.append(maindriver)

            output[0] = self.substituteThreadLines(output[0], maxlabels)

            if (self.__satSwarm):
                stemp = ''.join(s for s in self.__ctrlVarDefs)
                output.insert(0, stemp)
            # print(stemp)
            # sys.exit(0)
            instanceGenerated = ''.join(t for t in output)
            # with open("test.c", 'w') as fd:
            # fd.write(instanceGenerated)
            # sys.exit()
            yield instanceGenerated, configNumber, configintervals

    def masterSendTile(self, env, jsonConfig):

        #comm.recv(source=MPI.ANY_SOURCE, status=status)
        tag = status.tag
        rankClient = status.Get_source()
        
        if tag == StatusCode.UNSAFE.value:
            jsonConfigAnalyzed = hashtable[str(rankClient)]
            reportHashtable[str(jsonConfigAnalyzed)] = StatusCode.UNSAFE.value

            if self.isUnsafe is False:
                self.foundtime = time.time() - env.starttime
                self.isUnsafe = True

                if env.exit_on_error == True:

                    totaltime = time.time() - env.starttime
                    self.printIsUnsafe(totaltime, self.foundtime, env.inputfile, env.isSwarm)

                    for slave in range(1, numberProcess):
                        comm.send(StatusCode.KILL.value, dest=slave, tag=StatusCode.KILL.value)

                    for jsonConfigTmp, result in reportHashtable.items():
                        print(jsonConfigTmp, result)

                    print("Rank: ", rank, " - Master terminates its execution")
                    comm.Abort()
                    MPI.Finalize()
                    sys.exit(0)

        elif tag == StatusCode.SAFE.value:
            jsonConfigAnalyzed = hashtable[str(rankClient)]
            reportHashtable[str(jsonConfigAnalyzed)] = StatusCode.SAFE.value

        elif tag == StatusCode.UNKNOWN.value:
            jsonConfigAnalyzed = hashtable[str(rankClient)]
            reportHashtable[str(jsonConfigAnalyzed)] = StatusCode.UNKNOWN.value
            self.isUnknown = True

        hashtable[str(rankClient)] = jsonConfig

        comm.send(jsonConfig, dest=rankClient)

    def masterKillSlaves(self):

        for slave in range(1, numberProcess):

            #comm.recv(source=MPI.ANY_SOURCE, status=status)
            tag = status.tag
            rankClient = status.Get_source()

            if tag == StatusCode.REQUEST.value:
                comm.send(StatusCode.KILL.value, dest=rankClient, tag=StatusCode.KILL.value)

            if tag == StatusCode.UNSAFE.value:
                jsonConfigAnalyzed = hashtable[str(rankClient)]
                reportHashtable[str(jsonConfigAnalyzed)] = StatusCode.UNSAFE.value
                self.isUnsafe = True

            elif tag == StatusCode.SAFE.value:
                jsonConfigAnalyzed = hashtable[str(rankClient)]
                reportHashtable[str(jsonConfigAnalyzed)] = StatusCode.SAFE.value

            elif tag == StatusCode.UNKNOWN.value:
                jsonConfigAnalyzed = hashtable[str(rankClient)]
                reportHashtable[str(jsonConfigAnalyzed)] = StatusCode.UNKNOWN.value
                self.isUnknown = True

            if str(rankClient) in hashtable:
                comm.send(StatusCode.KILL.value, dest=rankClient, tag=StatusCode.KILL.value)

    def slaveAnalysis(self, seqcode, env, fill_only_fields=None, queue=None):

        print(env.inputfile)

        dirname, filename = os.path.split(os.path.abspath(env.inputfile))
        swarmdirname = dirname + "/" + filename[:-2] + '.swarm%s/' % env.suffix

        instanceIterator = self.slaveGeneratesInstanceIterator(env, seqcode, queue)

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
        sentinel = object()

        def logResults(out):
            results.put(out)
            if out is True:
                comm.send(StatusCode.SAFE.value, dest=server, tag=StatusCode.SAFE.value)
            if out is False:
                comm.send(StatusCode.UNSAFE.value, dest=server, tag=StatusCode.UNSAFE.value)
            if out == "ERROR":
                error = True
                comm.send(StatusCode.UNKNOWN.value, dest=server, tag=StatusCode.UNKNOWN.value)

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
                    print("UNKNOWN ", rank)
                if out is False and not foundbug:
                    self.foundtime = time.time() - env.starttime
                    foundbug = True
                    if env.exit_on_error:
                        break
                pool.apply_async(self.backendChain, (env, instance, confignumber, configintervals, swarmdirname,
                                                     filename[:-2],), callback=logResults)

        except KeyboardInterrupt as e:
            print("Interrupted by user")
            pool.terminate()
            pool.close()
            pool.join()
            sys.exit(1)

        pool.close()
        pool.join()

        backendTime = time.time() - backendStart

        if env.instances_only:
            if env.isSwarm:
                print("Time for generating instances = %0.2fs" % backendTime)
                print("Instances generated in " + swarmdirname)
            # in the non swarm case, it is the only process running that signals that the sequentialization has succeded
            sys.exit(0)

        if not foundbug:
            while not results.empty():
                out = results.get()
                if out is False:
                    foundbug = True
                    self.foundtime = time.time() - env.starttime
                    break
                if out == "ERROR":
                    error = True
                    break

        totaltime = time.time() - env.starttime

        if error:
            self.printError(totaltime, env.inputfile, env.isSwarm)
            return
        if foundbug:
            self.printIsUnsafe(totaltime, self.foundtime,
                               env.inputfile, env.isSwarm)
        else:
            self.printIsSafe(totaltime, env.inputfile, env.isSwarm)

        queue.task_done()
        return

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
                    "s", ""), memsize, analysistime, config=config)
            return True
        elif processedResult == "FALSE":
            if env.isSwarm:
                self.printFoundBug(confignumber.replace(
                    "s", ""), memsize, analysistime, config=config)
            # controesempio è in errorTrace se cex settata, salvare in file per swarm e stampare a video per noSwarm
            return False

        else:
            noformula = "NOFORMULA" in processedResult
            if env.isSwarm:
                self.printUnknown(confignumber.replace(
                    "s", ""),noformula=noformula, config=config)
            return "ERROR" + (" NOFORMULA" if noformula else "")
        sys.stdout.flush()

    def printUnknown(self, index, noformula=False, config=""):
        print("{0:20}{1:20}".format("[#" + str(index) + (" "+config if len(config) > 0 else "") + "]", utils.colors.YELLOW + "UNKNOWN" + (" NOFORMULA" if noformula else "") + utils.colors.NO, ))
        sys.stdout.flush()

    def printNoFoundBug(self, index, memsize, analysistime, config=""):
        print("{0:20}{1:20}{2:10}{3:10}".format("[#" + str(index) + (" "+config if len(config) > 0 else "") + "]", utils.colors.GREEN + "SAFE" + utils.colors.NO,
                                                "%0.2fs " % analysistime, self.calcMem(memsize)))
        sys.stdout.flush()

    def printFoundBug(self, index, memsize, analysistime, config=""):
        print("{0:20}{1:20}{2:10}{3:10}".format("[#" + str(index) + (" "+config if len(config) > 0 else "") + "]", utils.colors.RED + "UNSAFE" + utils.colors.NO,
                                                "%0.2fs " % analysistime, self.calcMem(memsize)))
        sys.stdout.flush()
        
    def printSkipped(self, index, config=""):
        print("{0:20}{1:20}".format("[#" + str(index) + (" "+config if len(config) > 0 else "") + "]", utils.colors.BLUE + "SKIPPED" + utils.colors.NO, ))
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
                didGenerateFormula = False
                for line in backendAnswer.splitlines():
                    if " variables, " in line:
                        splitline = line.split()
                        variables = splitline[0]
                        clauses = splitline[2]
                        didGenerateFormula = True
                    if "Runtime Symex" in line:
                        didGenerateFormula = True
                    if verificationOK[format] in line:
                        outcome = "TRUE"
                        break
                    elif verificationFAIL[format] in line:
                        outcome = "FALSE"
                        break
                if len(outcome) == 0 and not didGenerateFormula:
                    outcome = "NOFORMULA"
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
