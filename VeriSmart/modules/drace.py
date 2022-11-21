from modules import abstr_dr_common
from core import abs_dr_rules
import math

class drace(abstr_dr_common.abstr_dr_common):

    __codeContainsAtomic = False #set to True if code contains blocks that are executed atomically
    __codeContainsAtomicCheck = True #this is set to False as soon as __codeContainsAtomic is determined
    #__VP1required = False  # True iff current visible point is the last one of this context
    #__VP2required = False  # True iff current visible point is the first one of this context
    
    def init(self, abs_on=False):
        super().init(abs_on=abs_on, dr_on=True)
        self.abs_dr_vpstate = abs_dr_rules.VPState()
        #self.abs_dr_vpstate.VP1required = False
        #self.abs_dr_vpstate.VP2required = False
        
    def initFlags(self,count):
        #self.__stats  =  Stats.TOP
        if count == -2:
            self.abs_dr_vpstate.VP1required = True
            self.abs_dr_vpstate.VP2required = True
            #self.__VP1required = True
            #self.__VP2required = True
        else:
            self.abs_dr_vpstate.VP1required = False
            self.abs_dr_vpstate.VP2required = False
            #self.__VP1required = False
            #self.__VP2required = False
        return
    
    #self.__VP1required = True  self.__VP2required = True 
    def additionalCode(self,threadIndex):
        s = ''

        if self.abs_dr_vpstate.VP1required:
            s += '__cs_dataraceActiveVP1 = ( @£@L1 == (__cs_pc_cs[%s]-1) ) ; \n' % threadIndex
        if self.abs_dr_vpstate.VP2required:
            s += '__cs_dataraceActiveVP2 = ( @£@L2 == __cs_pc[%s] ) ; \n' % threadIndex   #DR
        return s

    def alternateCode(self, n):
        for adr in self.conf_adr: 
            adr.disableDr()
        s = self.visit(n)
        for adr in self.conf_adr: 
            adr.enableDr()
        return s
      
    def codeContainsAtomic(self):
        return True
        if self.__codeContainsAtomicCheck:
            for i in self.Parser.funcCallCnt: #self.Parser.funcName:
                if i.startswith("__CSEQ_atomic"):
                    self.__codeContainsAtomic = True
                    break
            self.__codeContainsAtomicCheck = False
        return self.__codeContainsAtomic  
        
    def createMainRoundRobin(self, ROUNDS):
        '''  New main driver:
        '''
        main = ''
        main += "int main(void) {\n"
        main += self.global_var_initializations+";\n"
        main += "FIELD_DECLS();\n"

        #DR init TODO handle atomic
        #if self.codeContainsAtomic(): 
        #    main += '__CPROVER_field_decl_global("dr_write_noatomic", (_Bool) 0); \n __CPROVER_field_decl_local("dr_write_noatomic", (_Bool) 0); \n ' #set whenever writes meaningful for DR occur outside atomic blocks
        #main += '__CPROVER_field_decl_global("dr_write", (_Bool) 0); \n __CPROVER_field_decl_local("dr_write", (_Bool) 0); \n' #set whenever a meaningful write occurs

        ''' Part I:
            Pre-guessed jump lengths have a size in bits depending on the size of the thread.
        '''
        for r in range(0, ROUNDS):
            for t in range(0,self.getThreadbound()+1):
                threadsize = self.getLines()[self.getThreadName()[t]]
                k = int(math.floor(math.log(threadsize,2)))+1
                self._bitwidth['main','__cs_tmp_t%s_r%s' % (t,r)] = k

        maxts = ROUNDS*(self.getThreadbound()+1)-2  #DR
        main +="          unsigned int __cs_dr_ts %s;\n" % self.getExtra_nondet()   #DR
        self._bitwidth['main','__cs_dr_ts'] = int(math.floor(math.log(maxts,2)))+1  #DR
        main +="          __CSEQ_assume(__cs_dr_ts <= %s);\n" % maxts  #DR


        ''' First round (round 0)
        '''
        round = 0
        # Main thread
        main +="__CSEQ_rawline(\"/* round  %s */\");\n" % round
        main +="__CSEQ_rawline(\"    /* main */\");\n"
        #caledem
        main +="__cs_active_thread[%s] = 1;\n" % self.Parser.threadOccurenceIndex['main']
        main +="          unsigned int __cs_tmp_t%s_r0 %s;\n" % (self.Parser.threadOccurenceIndex['main'], self.getExtra_nondet())
        main +="          __cs_pc_cs[%s] = __cs_tmp_t%s_r0;\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'])
        main +="          __CSEQ_assume(__cs_pc_cs[%s] > 0);\n" % self.Parser.threadOccurenceIndex['main']
        main +="          __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (self.Parser.threadOccurenceIndex['main'], "@£@ML" + str(self.Parser.threadOccurenceIndex['main']))
        main +="          if(__cs_dr_ts == 0) __cs_dataraceDetectionStarted=1;\n"
        main +="          main_thread();\n"
        main +="          if(__cs_dataraceDetectionStarted) __cs_dataraceSecondThread=1;\n"  #DR
        main +="          __cs_pc[%s] = __cs_pc_cs[%s];\n"   % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'])
        main +="\n"
        # Other threads
        ts = 1 #DR
        i = 0
        for t in self.getThreadName():
            if t == 'main': continue
            if i <= self.getThreadbound():
                main +="__CSEQ_rawline(\"    /* %s */\");\n" % t
                #main +="__CSEQ_rawline(\"__cs_ts=%s;\");\n" % i   #POR
                #main +="__CSEQ_rawline(\"__cs_tsplusone=%s;\");\n" % ( self.getThreadbound()+1+i)   #POR
                main +="         unsigned int __cs_tmp_t%s_r0 %s;\n" % (i, self.getExtra_nondet())
                main +="         if (__cs_dataraceContinue & __cs_active_thread[%s]) {\n" % (i)           #DR
                main +="             __cs_pc_cs[%s] = __cs_tmp_t%s_r0;\n" % (i, i)
                main +="             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (i, "@£@ML" + str(self.Parser.threadOccurenceIndex[t]))
                #main +="             __cs_noportest=0;\n"   #POR
                if ts <= maxts :   #DR
                      main +="             if(__cs_dr_ts == %s) __cs_dataraceDetectionStarted=1;\n" % ts #DR
                main +="             %s(__cz_threadargs[%s]);\n" % (t, i)
                main +="             if(__cs_dataraceSecondThread & (__cs_tmp_t%s_r0 > 0)) __cs_dataraceContinue=0;\n" % i #DR
                if ts <= maxts :   #DR
                      main +="             if(__cs_dataraceDetectionStarted) __cs_dataraceSecondThread=1;\n"  #DR
                #main +="             __CSEQ_assume(__cs_is_por_exec);\n" #DR
                main +="             __cs_pc[%s] = __cs_pc_cs[%s];\n" % (i, i)
                main +="         }\n\n"
                i += 1
                ts += 1 #DR

        ''' Other rounds
        '''
        for round in range(1, ROUNDS):
            main +="__CSEQ_rawline(\"/* round  %s */\");\n" % round
            #main +="__CSEQ_rawline(\"__cs_isFirstRound= 0;\");\n"  #POR
            # For main thread
            main +="__CSEQ_rawline(\"    /* main */\");\n"
            #main +="__CSEQ_rawline(\"__cs_ts=%s;\");\n" % (round * (self.getThreadbound()+1))   #POR
            #main +="__CSEQ_rawline(\"__cs_tsplusone=%s;\");\n" % ( (round+1) * ( self.getThreadbound()+1) )  #POR
            main +="          unsigned int __cs_tmp_t%s_r%s %s;\n" % (self.Parser.threadOccurenceIndex['main'],round, self.getExtra_nondet())
            main +="          if (__cs_dr_ts > %s &  __cs_dataraceContinue & __cs_active_thread[%s]) {\n" %  (ts - (self.getThreadbound()+1), self.Parser.threadOccurenceIndex['main'])          #DR
            if self.getGuessCsOnly():
                main +="             __cs_pc_cs[%s] = __cs_tmp_t%s_r%s;\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], round)
            else:
                main +="             __cs_pc_cs[%s] = __cs_pc[%s] + __cs_tmp_t%s_r%s;\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], round)
            main +="             __CSEQ_assume(__cs_pc_cs[%s] >= __cs_pc[%s]);\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'])
            main +="             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (self.Parser.threadOccurenceIndex['main'], "@£@ML" + str(self.Parser.threadOccurenceIndex['main']))
            if ts <= maxts :   #DR
                main +="             if(__cs_dr_ts == %s) __cs_dataraceDetectionStarted=1;\n" % ts  #DR
            main +="             main_thread();\n"
            main +="             if(__cs_dataraceSecondThread & (__cs_tmp_t%s_r%s > 0 )) __cs_dataraceContinue=0;\n" % (self.Parser.threadOccurenceIndex['main'], round) #DR
            if ts <= maxts :   #DR
                main +="             if(__cs_dataraceDetectionStarted) __cs_dataraceSecondThread=1;\n"  #DR
            #main +="             __CSEQ_assume(__cs_is_por_exec);\n" #POR
            main +="             __cs_pc[%s] = __cs_pc_cs[%s];\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'])
            main +="          }\n\n"
            main +="\n"
            # For other threads
            ts += 1 #DR
            i = 0
            for t in self.getThreadName():
                if t == 'main': continue
                if i <= self.getThreadbound():
                    main +="__CSEQ_rawline(\"    /* %s */\");\n" % t
                    #main +="__CSEQ_rawline(\"__cs_ts=%s;\");\n" % (round * (self.getThreadbound()+1) + i )   #POR
                    #if (round == ROUNDS -1):
                        #main +="__CSEQ_rawline(\"__cs_tsplusone=%s;\");\n" % ( (round+1) * ( self.getThreadbound()+1))  #POR
                    #else:
                        #main +="__CSEQ_rawline(\"__cs_tsplusone=%s;\");\n" % ( (round+1) * ( self.getThreadbound()+1) + i)  #POR
                    main +="         unsigned int __cs_tmp_t%s_r%s %s;\n" % (i, round, self.getExtra_nondet())
                    main +="         if (__cs_dr_ts > %s & __cs_dataraceContinue & __cs_active_thread[%s]) {\n" % ( ts - (self.getThreadbound()+1) ,i)           #DR
                    if self.getGuessCsOnly():
                        main +="             __cs_pc_cs[%s] = __cs_tmp_t%s_r%s;\n" % (i, i, round)
                    else:
                        main +="             __cs_pc_cs[%s] = __cs_pc[%s] + __cs_tmp_t%s_r%s;\n" % (i, i, i, round)
                    main +="             __CSEQ_assume(__cs_pc_cs[%s] >= __cs_pc[%s]);\n" % (i, i)
                    main +="             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (i, '@£@ML' + str(self.Parser.threadOccurenceIndex[t]))
                    #main +="             __cs_noportest=0;\n"  #POR
                    if ts <= maxts :   #DR
                         main +="             if(__cs_dr_ts == %s) __cs_dataraceDetectionStarted=1;\n" %  ts #DR
                    main +="             %s(__cz_threadargs[%s]);\n" % (t, i)
                    main +="             if(__cs_dataraceSecondThread & (__cs_tmp_t%s_r%s > 0)) __cs_dataraceContinue=0;\n" % (i,round) #DR
                    if ts <= maxts :   #DR
                         main +="             if(__cs_dataraceDetectionStarted) __cs_dataraceSecondThread=1;\n"  #DR
                    #main +="             __CSEQ_assume(__cs_is_por_exec);\n" #POR
                    main +="             __cs_pc[%s] = __cs_pc_cs[%s];\n" % (i, i)
                    main +="         }\n\n"
                    i += 1
                    ts += 1 #DR


        #''' Last call to main
        #'''

        ## For the last call to main thread
        #k = int(math.floor(math.log(self.getLines()['main'],2)))+1
        #main += "          unsigned int __cs_tmp_t0_r%s %s;\n" % (ROUNDS, self.getExtra_nondet())
        #self._bitwidth['main','__cs_tmp_t0_r%s' % (ROUNDS)] = k
        #main +="           if (__cs_dr_ts > %s & __cs_dataraceContinue & __cs_active_thread[0]) {\n" % ((round-1) * (self.getThreadbound()+1)+i) #DR
        #if self.getGuessCsOnly():
        #    main +="             __cs_pc_cs[0] = __cs_tmp_t0_r%s;\n" % (ROUNDS)
        #else:
        #    main +="             __cs_pc_cs[0] = __cs_pc[0] + __cs_tmp_t0_r%s;\n" % (ROUNDS)
        #main +="             __CSEQ_assume(__cs_pc_cs[0] >= __cs_pc[0]);\n"
        #main +="             __CSEQ_assume(__cs_pc_cs[0] <= %s);\n" % (self.getLines()['main'])
        ##main +="             __cs_noportest=0;\n"  #POR
        #main +="             __cs_main_thread();\n"
        #main +="           }\n"
        main +="     __CPROVER_assert(!"+self.conf_adr[0].dr+",\"Data race failure\");\n"
        main += "    return 0;\n"
        main += "}\n\n"

        return main
