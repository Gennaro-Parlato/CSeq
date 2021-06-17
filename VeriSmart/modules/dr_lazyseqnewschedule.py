""" Lazy-CSeq Sequentialization module extension with data race detection
"""

"""

	2021.03.30  Initial version

"""
import math, re, os.path
import sys
from time import gmtime, strftime
import pycparser.c_parser, pycparser.c_ast, pycparser.c_generator
import core.common, core.module, core.parser, core.utils
from enum import Enum,auto
from modules import lazyseqnewschedule

class Stats(Enum):
      TOP = auto()
      ACC = auto()
      noACC = auto()
      PRE = auto()

class dr_lazyseqnewschedule(lazyseqnewschedule.lazyseqnewschedule):

	# DR data for discarding clearly benign dataraces (i.e., when we have write-write of the same value
	__enableDR = False   #True iff input option --dr is chosen
	__wwDatarace = False 
	__noShadow = False
	#__enableDRlocals = False  # data race code also on local vars

	__stats =  Stats.TOP  # TOP iff at the top level of an expression
                              # ACC iff ACCESS mode
                              #  noACC iff  noACCESS mode
                              # PRE iff visiting postExp in array reference (PREFIX mode)

	__optional1 = False # True iff OPTIONAL1 is true for the current expression
	__optional2 = False # True iff OPTIONAL2 is true for the current expression

	__WSE = '' #contains the WSE comma expression of the last visited subexpression

	__visitingLHS = False  # set to True when vising the left hand side of an assignment to determine whether the this is an access meaningful for data race detection
	__access = False  # set to True to denote that the LHS of an assignment is meaningful for data race detection
	__funcID = False  # set to True iff we are visiting the id of a function  in a function call

	__visitingStruct = False # True iff we are visiting a structure name

	__VP1required = False  # True iff current visible point is the last one of this context

	__VP2required = False  # True iff current visible point is the first one of this context
	__enableDRcode = True  # Disabled when visiting atomic o or special function definitions		

	__isArray = False                # used to flag that we are below an ArrayRef node
	__arrayName = ''            # contains the array name when on visiting array ref (going-up)
	__const = {}                # variables that are declared const
	__const[''] = []            # init const vars for global scope

	def init(self):
		self.addInputParam('rounds', 'round-robin schedules', 'r', '1', False)
		self.addInputParam('threads', 'max no. of thread creations (0 = auto)', 't', '0', False)
		self.addInputParam('deadlock', 'check for deadlock', '', default=False, optional=True)
		self.addInputParam('decomposepc', 'use seperate variable for each pc', '', default=False, optional=True)
		self.addInputParam('robin', 'use round robin schedule', '', default=False, optional=True)
		self.addInputParam('guess-cs-only', 'context switch is guessed only', '', default=False, optional=True)
		self.addInputParam('norobin', 'use new schedule', '', default=False, optional=True)
		self.addInputParam('preanalysis', 'use preanalysis input from abstract interpretation backend', 'u', default=None, optional=True)

		self.addInputParam('donotcheckvisiblepointer', 'do not check pointer for visible statement', '', default=False, optional=True)

		self.addOutputParam('bitwidth')
		self.addOutputParam('header')

		#Calenda De Mattia
		self.addOutputParam('lines')
		self.addOutputParam('threadNames')
		self.addOutputParam('threadIndex')


	def additionalDefs(self):
		#header += 'unsigned int __cs_ts = 0; \n'   #POR 
		#header += 'unsigned int __cs_tsplusone = %s; \n' % (self.getThreadbound()+1)   #POR 
		#header += '_Bool __cs_is_por_exec = 1; \n'   #POR 
		#header += '_Bool __cs_isFirstRound = 1; \n'   #POR 
		header = '_Bool __cs_dataraceDetectionStarted = 0; \n'   #DR
		header += '_Bool __cs_dataraceSecondThread = 0; \n'   #DR
		header += '_Bool __cs_dataraceNotDetected = 1; \n'   #DR
		header += '_Bool __cs_dataraceContinue = 1; \n'   #DR
		header += '_Bool __cs_dataraceActiveVP1 = 0; \n'   #DR
		header += '_Bool __cs_dataraceActiveVP2 = 0; \n'   #DR
		# DR API implementation
		if self.__enableDR and self.__noShadow:
			header += 'const void * shadowmem[SMSIZE]={0,0,0,0,0};\n\
					int shadowmem_idx=0;\n\
					void __CPROVER_field_decl_global(char* s,  _Bool b){\n\
					}\n\
					void __CPROVER_set_field(void* x, char* s, int b){\n\
					shadowmem[shadowmem_idx]=x;\n\
					shadowmem_idx++;\n\
					}\n\
					_Bool __CPROVER_get_field(void* x, char* s){\n\
					return (shadowmem[0]==x || shadowmem[1]==x || shadowmem[2]==x \
					|| shadowmem[3]==x || shadowmem[4]==x);\n\
					}\n'
		return header


	def loadfromstring(self, string, env):

		self.__enableDR = env.enableDR
		self.__wwDatarace = env.wwDatarace
		self.__noShadow = env.no_shadow
		#self.__enableDRlocals = env.local
		super(dr_lazyseqnewschedule, self).loadfromstring(string, env)

# routines for visit_Compound

	def initFlags(self):
            self.__stats  =  Stats.TOP
            self.__VP1required = False
            self.__VP2required = False
            return

	def additionalCode(self,threadIndex):
		s = ''

		if self.__VP1required:
			s += '__cs_dataraceActiveVP1 = ( @#@L1 == (__cs_pc_cs[%s]-1) ) ; \n' % threadIndex
		if self.__VP2required:
			s += '__cs_dataraceActiveVP2 = ( @#@L2 == __cs_pc[%s] ) ; \n' % threadIndex   #DR
		return s

#end routines for visit_Compound


	def visit_ExprList(self, n):
            if self.getGlobalMemoryTest() or not self.__enableDRcode: 
                #ret = super(dr_lazyseqnewschedule, self).visit_ExprList(n)
                #print("GMtest: " + ret)
                return super(dr_lazyseqnewschedule, self).visit_ExprList(n)

            visited_subexprs = []
            wseList = []
            opt = True
            #n.show()
            for expr in n.exprs:
                self.__stats = Stats.TOP
            #    s = self.visit(expr)
            #    print("element: " + s)
                #print(self.__WSE)
                visited_subexprs.append('('+ self.visit(expr) + ')')
                wseList.append('('+ str(self.__WSE)+')')
                opt = opt and self.__optional2

            self.__optional1 = opt
            self.__optional2 = self.__optional1
            self.__WSE = ', '.join(wseList)
            self.setExpList(visited_subexprs)
            ret = ', '.join(visited_subexprs)
            #print("List: " + str(visited_subexprs))
            #print("DR: " + ret)
            #n.show()
            return ', '.join(visited_subexprs)

#    visit_FuncCall routines
	def frefVisit(self,n):
		old_funcID = self.__funcID
		self.__funcID = True
		ret = self._parenthesize_unless_simple(n.name)
		self.__funcID =  old_funcID
		return ret

	def addRetFuncCall(self,fname,args,tindex=None):
#		if args == '' : 
#			self.__WSE = args

		if tindex == None:
			self.__WSE = '%s ( %s )' % (fname,args)
		else: 
			#print(fname)
			#print(self.__WSE)
			self.__WSE = '%s ( %s, %s )' % (fname,args, tindex)
			#print(self.__WSE)
		self.__optional2 = True  #function calls appear only in the WSE formulas (all the rewriting is on the parameters)
		self.__optional1 = self.__optional2

#		if (fname == 'assume_abort_if_not' and not (self.getGlobalMemoryTest() or not self.__enableDRcode)):
#			n.show()
#			print("WSE: " + self.__WSE)

#	def visit_FuncCall(self, n):
#            fref = self._parenthesize_unless_simple(n.name)
#            return fref + '(' + self.visit(n.args) + ')'


	def visit_ArrayRef(self, n):
                if self.getGlobalMemoryTest() or not self.__enableDRcode: 
                    return super(dr_lazyseqnewschedule, self).visit_ArrayRef(n)
                self.__arrayName = ''
                ret = ''
                old_drStats = self.__stats  #DR  

                self.__stats = Stats.PRE #DR

                old_isArray = self.__isArray  
                self.__isArray = True  

                arrref = self._parenthesize_unless_simple(n.name)
                wse = self.__WSE 
                self.__isArray = old_isArray #POR

                if not self.__optional2:
                   ret =  arrref 
                    
                opt1 = self.__optional2

                self.__stats = Stats.ACC #DR

                subscript = self.visit(n.subscript)
                #subscript = self.fixArrayIndex(subscript)
                wse_index = self.fixArrayIndex(self.__WSE)

                wse = wse + '[' + wse_index + ']'

                if not self.__optional2:
                   if ret != '': 
                      ret += ','
                   ret += subscript

                #print(self.__arrayName)  
                #  the value of ret at this point is fine for noACC and PRE modes
                if old_drStats != Stats.PRE:
                   if old_drStats == Stats.ACC or  old_drStats == Stats.TOP:
                      #print(self.__arrayName)
                      if self._isGlobal(self.getCurrentThread(), self.__arrayName) or self._isPointer(self.getCurrentThread(), self.__arrayName):   #POR
                         if ret != '':
                             ret += ','
                
                         ret += '( __cs_dataraceActiveVP2 && __cs_dataraceSecondThread  && (__cs_dataraceNotDetected = __cs_dataraceNotDetected && ! __CPROVER_get_field(&%s,"dr_write")))' % wse
                         self.__VP2required = True

                   if self.__visitingLHS:
                         self.__access = True
                         self.__visitingLHS = False
                         self.__arrayName = ''
                    
                if old_drStats == Stats.TOP:
                   if ret != '':
                      ret += ','
                   ret += wse
                #print(self.__access)
                   
                self.__optional1 = opt1 and self.__optional2 
                self.__optional2 = self.__optional1  
                self.__WSE = wse

                self.__stats = old_drStats  #DR  
                return ret

	def visit_ID(self, n):
		#print(n.name)
		#print(self.getGlobalMemoryTest())
		if self.getGlobalMemoryTest() or not self.__enableDRcode: 
			return super(dr_lazyseqnewschedule, self).visit_ID(n)
		if self.__funcID:
			self.__WSE = super(dr_lazyseqnewschedule, self).visit_ID(n)
			self.__optional1 = True
			self.__optional2 = True
			return self.__WSE

		ret = ''   # noACC is default
		wse = n.name
		self.__optional2 = True
		
#		if (n.name == '__cs_param_read_nvram_buf'):
#			print("Const check: " + str(self._isConst(self.getCurrentThread(), n.name)))
			
		
		#if (self._isGlobal(self.getCurrentThread(), n.name) or self._isPointer(self.getCurrentThread(), n.name)) and not self.__isArray and not self._isConst(self.getCurrentThread(),n.name):
		if ( not self.isThread(n.name) and not self.__isArray and not self._isConst(self.getCurrentThread(),n.name)):
			if self.__stats != Stats.noACC: 
				ret += '( __cs_dataraceActiveVP2 && __cs_dataraceSecondThread  && (__cs_dataraceNotDetected = __cs_dataraceNotDetected && ! __CPROVER_get_field(&%s,"dr_write")))' %  wse
				self.__VP2required = True
				self.__optional2 = False

			if self.__visitingLHS:
                           self.__access = True
                           self.__visitingLHS = False
		self.__optional1 = True   # no subexpressions 
		super(dr_lazyseqnewschedule, self).visit_ID(n)
		self.__WSE = wse
                
		if self.__stats == Stats.TOP:
			ret =  wse if ret == '' else '%s, %s' % (ret, wse)

		if self.__isArray:
			self.__arrayName = n.name
				
		#print("visit_ID ret: " + ret)
		#print("Optional1: " + str(self.__optional1))
		#print("Optional2: " + str(self.__optional2))
		#print("Stats: " + str(self.__stats))
		#n.show()
		return ret

	def visit_Assignment(self, n):
                if self.getGlobalMemoryTest() or not self.__enableDRcode: 
                     return super(dr_lazyseqnewschedule, self).visit_Assignment(n)

                #print(type(n.lvalue))
                assert (self.__stats != Stats.noACC),"Assignment explored in noACC mode!" # noACC is not possible here since an assignment expression is not an lvalue

                ret = ''        
                old_drStats = self.__stats  

                self.__stats = Stats.noACC 

                old_visitingLHS = self.__visitingLHS
                self.__visitingLHS = True
                old_access = self.__access
                self.__access = False

                lvalue = self.visit(n.lvalue)
                #print("Visited left-handside")
                
                self.__visitingLHS = old_visitingLHS

                if not self.__optional1:   # OPTIONAL1
                   ret =  lvalue 

                opt1 = self.__optional2

                lwse = self.__WSE  # lwse now contains the lvalue where the data is assigned
                if self.__access:
                    if ret != '':
                       ret += ','
                    p1 = '( __cs_dataraceActiveVP1 && __cs_dataraceDetectionStarted && !__cs_dataraceSecondThread && __CPROVER_set_field(&%s,"dr_write",1) ), ' % lwse
                    self.__VP1required = True
 
                    p2 = '( __cs_dataraceActiveVP2 && __cs_dataraceSecondThread  && (__cs_dataraceNotDetected = __cs_dataraceNotDetected && ! __CPROVER_get_field(&%s,"dr_write")))' % lwse
                    self.__VP2required = True

                    ret += p1 + p2

                self.__access = old_access


                self.__stats = Stats.ACC 

                rvalue = self.visit(n.rvalue)
                #print("RVALUE: " + rvalue)
                #n.rvalue.show()

                if not self.__optional2:
                   if ret != '':
                      ret += ', '
                   ret +=  rvalue 
                   #print("RET: " + ret)
                   #n.rvalue.show()

                rwse = self.__WSE
                #print("WSE: " + rwse)

                self.__optional1 = opt1 and self.__optional2
                self.__optional2 = False  #Assignment has side effects

		#print self.__sharedVarsW
                if ret != '':
                    ret += ','
                ret += '%s %s %s' % (lwse, n.op, rwse)
                self.__WSE = lwse
                #print("RET: " + ret)

                self.__stats = old_drStats  
                return ret

	def visit_UnaryOp(self, n):
		if self.getGlobalMemoryTest() or not self.__enableDRcode: 
			return super(dr_lazyseqnewschedule, self).visit_UnaryOp(n)

		#print(self.__stats)
		ret = ''        
		old_stats = self.__stats  
		old_visitingLHS = self.__visitingLHS  #only used for inc/dec
		old_access = self.__access  #only used for inc/dec

		self.__stats = Stats.ACC 
		if n.op == "&":
			self.__stats = Stats.noACC
		if n.op == "++" or n.op == "--" or n.op == "p++" or n.op == "p--":
			self.__stats = Stats.noACC
			self.__visitingLHS = True
			self.__access = False
		operand = self._parenthesize_unless_simple(n.expr)

#		ret = '%s%s' % (n.op, operand)
		wse = self.__WSE
		self.__WSE = '%s%s' % (n.op, wse)  #This is the rigth WSE expression except for postfix increment and decrement operators, and sizeof operator

		if n.op == "++" or n.op == "--" or n.op == "p++" or n.op == "p--": 
			if  n.op == "p++": 
				self.__WSE = '(%s + 1)' % wse
			elif n.op == "p--": 
				self.__WSE = '(%s - 1)' % wse
			else:
				self.__WSE = wse
			if self.__access:
				if ret != '':
					ret += ','
				p1 = '( __cs_dataraceActiveVP1 && __cs_dataraceDetectionStarted && !__cs_dataraceSecondThread && __CPROVER_set_field(&%s,"dr_write",1) ), ' % wse
				self.__VP1required = True 

				p2 = '( __cs_dataraceActiveVP2 && __cs_dataraceSecondThread  && (__cs_dataraceNotDetected = __cs_dataraceNotDetected && ! __CPROVER_get_field(&%s,"dr_write")))' % wse
				self.__VP2required = True 

				ret += p1 + p2
			if ret != '':
				ret += ','
			if n.op == "++" or n.op == "--":
				ret += '%s%s' % (n.op,wse)
			else:
				ret += '%s%s' % (wse,n.op[1:])
		else:
			if n.op == '&':         
				if not self.__optional1:
					ret = operand
			
			elif n.op == "*":
				if not self.__optional2:
					ret = operand
				if self.__stats == Stats.ACC or self.__stats == Stats.PRE:
					if ret != '':
						ret += ','
					ret += '( __cs_dataraceActiveVP2 && __cs_dataraceSecondThread  && (__cs_dataraceNotDetected = __cs_dataraceNotDetected && ! __CPROVER_get_field(&%s,"dr_write")))' % wse
					self.__VP2required = True

				if self.__visitingStruct:  #these parentheses are required to force priority in the c expression (* x).y
					self.__WSE = '(%s)' % self.__WSE  

#				if old_stats == Stats.TOP: 
#					if ret != '':
#						ret += ','
#					ret += self.__WSE


			else:
				if not self.__optional2:
					ret = operand
				if n.op == 'sizeof': 
					self.__WSE = "%s ( %s )" % (n.op,wse)
				#self.__optional1 = self.__optional2
				#print(self.__WSE)
				#n.show()
				#print(ret)
				#return ret

			if old_stats == Stats.TOP: 
				if ret != '':
					ret += ','
				ret += self.__WSE

		self.__visitingLHS =old_visitingLHS  #only used for inc/dec
		self.__access = old_access #only used for inc/dec

		self.__optional1 = self.__optional2
		if n.op == "++" or n.op == "--" or n.op == "p++" or n.op == "p--":
			self.__optional2 = False   #inc/dec have side effects

		self.__stats = old_stats

		return ret



	def visit_TernaryOp(self, n):
		
		if self.getGlobalMemoryTest() or not self.__enableDRcode: 
			return super(dr_lazyseqnewschedule, self).visit_TernaryOp(n)

		old_stats = self.__stats

		self.__stats = Stats.ACC
		iftrue = self._visit_expr(n.iftrue)
		wseT = self.__WSE
		opt2T = self.__optional2

		self.__stats = Stats.ACC
		iffalse = self._visit_expr(n.iffalse)
		wseF = self.__WSE
		opt2F = self.__optional2

		self.__stats = Stats.TOP
		if opt2T and opt2F:
			self.__stats = Stats.ACC
		cond = self._visit_expr(n.cond)
		wseC = self.__WSE
		opt2C = self.__optional2

		self.__WSE = '(%s)? (%s) : (%s)' % (wseC, wseT, wseF)

		if opt2T:
			if opt2F:
				if opt2C:
					ret = ''
				else:
					ret = cond
			else:
				ret = '(!%s && %s)' % (cond,iffalse)
		else:
			if opt2F:
				ret = '(%s && %s)' % (cond,iftrue)
			else:	
				ret = '(%s ? %s : %s)' % (cond,iftrue,iffalse)

		if old_stats == Stats.TOP:
			if ret != '':
				ret += ','
			ret += self.__WSE

		self.__optional2 = opt2C and opt2T and opt2F 
		self.__optional1 = self.__optional2
		self.__stats = old_stats
		#print(ret)
		return ret


	def visit_Constant(self, n):
		if self.getGlobalMemoryTest() or not self.__enableDRcode: 
			return super(dr_lazyseqnewschedule, self).visit_Constant(n)

		self.__optional1 = True
		self.__optional2 = True
		self.__WSE = n.value
		return n.value

	def visit_BinaryOp(self, n):
		if self.getGlobalMemoryTest() or not self.__enableDRcode: 
			return super(dr_lazyseqnewschedule, self).visit_BinaryOp(n)

		#print(n.op)
		old_stats = self.__stats

		self.__stats = Stats.ACC
		lval_str = self._parenthesize_if(n.left, lambda d: not self._is_simple_node(d))
		wse = self.__WSE
		optL = self.__optional2

		self.__stats = Stats.ACC
		rval_str = self._parenthesize_if(n.right, lambda d: not self._is_simple_node(d))
		self.__WSE = '(%s %s %s)' % (wse, n.op, self.__WSE)
		optR = self.__optional2

		ret = ''
		if not optL:
			ret = lval_str

		if not optR: 
			if ret != '': 
				ret += ','
			if n.op == '&&' or n.op == '||':
				ret += '%s %s %s' % (wse, n.op, rval_str)  #TOP for the left-hand side
			else:
				ret += rval_str	

		if old_stats == Stats.TOP:
			if ret != '':
				ret += ','
			ret += self.__WSE

		self.__optional2 = optL and optR 
		self.__optional1 = self.__optional2
		self.__stats = old_stats

#		print("RET: " + ret)
		return ret

	def visit_StructRef(self, n):
		if self.getGlobalMemoryTest() or not self.__enableDRcode: 
			return super(dr_lazyseqnewschedule, self).visit_StructRef(n)

		old_stats = self.__stats
		old_visitingStruct = self.__visitingStruct

		self.__visitingStruct = True
		self.__stats = Stats.noACC
		sref = self._parenthesize_unless_simple(n.name)
		opt1 = self.__optional2
		self.__visitingStruct = old_visitingStruct

		wse = self.__WSE 

#		print("RET: " + ret)
		#print("WSE: " + self.__WSE)

		self.visit(n.field)
		self.__WSE = wse + n.type + self.__WSE
		opt2 = self.__optional2
		
		ret =''
		if not self.__optional2:
			ret = sref 
		
		if old_stats == Stats.ACC:
			p2 = '( __cs_dataraceActiveVP2 && __cs_dataraceSecondThread  && (__cs_dataraceNotDetected = __cs_dataraceNotDetected && ! __CPROVER_get_field(&%s,"dr_write")))' % self.__WSE
			self.__VP2required = True 

			if ret != '':
				ret += ','
			ret += p2
			
		if old_stats == Stats.TOP:
			if ret != '':
                                ret += ','
			ret += self.__WSE

		self.__optional2 = opt1 and opt2

		self.__optional1 = self.__optional2
		self.__stats = old_stats

		return ret

#	def visit_ParamList(self, n):
		#print(n)
#		return ', '.join(self.visit(param) for param in n.params)


	def visit_Cast(self, n):
           if self.getGlobalMemoryTest() or not self.__enableDRcode: 
                return super(dr_lazyseqnewschedule, self).visit_Cast(n)

           old_stats = self.__stats
           s = '(' + self._generate_type(n.to_type) + ')'
           if self.__stats == Stats.PRE or self.__stats == Stats.TOP: 
              self.__stats = Stats.ACC     # ACC and noACC stay unchanged
           ret = self._parenthesize_unless_simple(n.expr)
           self.__WSE = s + ' ' + self.__WSE
           if old_stats == Stats.TOP:
              if self.__optional2:
                 ret = self.__WSE
              else: 
                 ret += ', ' + self.__WSE
           self.__optional1 = self.__optional2
           self.__stats = old_stats
           return ret

	def visit_FuncDef(self, n):
		if (n.decl.name.startswith('__CSEQ_atomic_') or n.decl.name == '__CSEQ_assert'):
			self.__enableDRcode = False

		self.__const[n.decl.name] = []

		ret = super(dr_lazyseqnewschedule,self).visit_FuncDef(n)

		if (n.decl.name.startswith('__CSEQ_atomic_') or n.decl.name == '__CSEQ_assert'):
			self.__enableDRcode = True

		return ret

	def visit_Decl(self,n):
		if (n.quals and 'const' in n.quals):
			self.__const[self.getCurrentThread()].append(n.name)
		ret = super(dr_lazyseqnewschedule,self).visit_Decl(n)

		if n.init and n.storage and 'static' in n.storage and '__cs_dataraceActiveVP' in ret:  #this is needed to avoid 
			spl = ret.split('=')
			splr = (' = ' .join(spl[1:])).split(',')
			ret = spl[0]+'= %s ; '% splr.pop() + ','.join(splr) + ';'
		return ret

	def visit_Typename(self, n):
		name = super(dr_lazyseqnewschedule,self).visit_Typename(n)
		self.__WSE = name
		return name

#	def visit_Compound(self,n):
#		for stm in n.block_items:
#                    stm.show()
#		return super(dr_lazyseqnewschedule,self).visit_Compound(n
	########################################################################################
	########################################################################################
	########################################################################################
	########################################################################################
	########################################################################################
	########################################################################################


	def createMainRoundRobin(self, ROUNDS):
		'''  New main driver:
		'''
		main = ''
		main += "int main(void) {\n"

		#DR init
		main += '__CPROVER_field_decl_global("dr_write", (_Bool) 0); \n' #% (ROUNDS)

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
		main +="          __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (self.Parser.threadOccurenceIndex['main'], "@#@ML" + str(self.Parser.threadOccurenceIndex['main']))
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
				main +="             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (i, "@#@ML" + str(self.Parser.threadOccurenceIndex[t]))
				#main +="             __cs_noportest=0;\n"   #POR
				if ts <= maxts :   #DR
					  main +="             if(__cs_dr_ts == %s) __cs_dataraceDetectionStarted=1;\n" % ts #DR
				main +="             %s(__cs_threadargs[%s]);\n" % (t, i)
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
			main +="             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (self.Parser.threadOccurenceIndex['main'], "@#@ML" + str(self.Parser.threadOccurenceIndex['main']))
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
					main +="             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (i, '@#@ML' + str(self.Parser.threadOccurenceIndex[t]))
					#main +="             __cs_noportest=0;\n"  #POR
					if ts <= maxts :   #DR
						 main +="             if(__cs_dr_ts == %s) __cs_dataraceDetectionStarted=1;\n" %  ts #DR
					main +="             %s(__cs_threadargs[%s]);\n" % (t, i)
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
		main +="     __CPROVER_assert(__cs_dataraceNotDetected,\"Data race failure\");\n"
		main += "    return 0;\n"
		main += "}\n\n"

		return main

######################

	def _isConst(self,f,v):
		return ( v in self.__const[f] or v in self.__const[''])
