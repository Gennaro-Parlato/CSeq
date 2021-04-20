""" Lazy-CSeq Sequentialization module
	maintained by Truc Nguyen Lam, University of Southampton.
"""
VERSION = 'lazyseqnewschedule-0.1-2016.08.08'

"""

Transformation:
	implements the lazy sequentialization schema
	(see Inverso, Tomasco, Fischer, La Torre, Parlato, CAV'14)

Prerequisites:
	- all functions should have been inlined, except the main(), all thread functions, all __CSEQ_atomic_ functions, and function __CSEQ_assert
	- all loops should habe been unrolled
	- no two threads refers to the same thread function (use module duplicator.py)

TODO:
	- get rid of _init_scalar() (see ext. notes)
	- check the STOP() inserting mechanism
	- this schema assumes no mutex_lock() in main() - is this fine?
	- handle typedef in guessing numbit

Changelog:
	2017.08.17  preserve __cs_exit function (not overriding with STOP_*VOID)
	2017.02.28  add option to only guess __cs_pc_cs (instead of using addition)
	2016.11.30  temporary disable of static for argc and argv variables
	2016.11.29  remove nondet initialization if backend is CBMC
	2016.11.22  fix problem with function pointer reference (smacker benchmarks)
	2016.09.21  add specific main function to KLEE backend (with only round robin approach)
	2016.09.21  fix small bug that causes the injection of GUARD in atomic function
	2016.08.12  Add option to use only one pc_cs
	2016.08.12  Add preanalysis from framac to guess the number of bits for each variable
	2016.08.10  Add round robin (old schedule) option
	2016.08.09  Add decomposepc option
	2016.08.08  Initial version

"""
import math, re, os.path
import sys
from time import gmtime, strftime
import pycparser.c_parser, pycparser.c_ast, pycparser.c_generator
import core.common, core.module, core.parser, core.utils


class lazyseqnewschedule(core.module.Translator):
	__lines = {}                     # lines for each thread
	#__threadName = ['main']         # OLD: name of threads, as they are found in pthread_create(s) - the threads all have different names
	__threadName = []                # NEW: name of threads, as they are found in code

	__threadIndex = {}               # index of the thread = value of threadcount when the pthread_create to that thread was discovered
	__threadCount = 0                # pthread create()s found so far

	__labelLine = {}                 # statement number where labels are defined [function, label]
	__gotoLine = {}                  # statement number where goto to labels appear [function, label]
	__maxInCompound = 0              # max label within a compound
	__labelLength = 55               # for labels to have all the same length, adding padding when needed
	__startChar = 't'                # special char to distinguish between labeled and non-labelled lines

	__stmtCount = -1                 # thread statement counter (to build thread labels)

	__currentThread = ''             # name of the current thread (also used to build thread labels)

	__threadbound = 0                # bound on the number of threads

	__firstThreadCreate = False      # set once the first thread creation is met
	__globalMemoryAccessed = False   # used to limit context-switch points (when global memory is not accessed, no need to insert them)

	__first = False
	__atomic = False                 # no context-switch points between atomic_start() and atomic_end()

	_bitwidth = {}                   # custom bitwidth for specific int variables, e.g. ['main','var'] = 4

	_deadlockcheck = False

	__decomposepc = False             # decompose pc

	__one_pc_cs = False             # use only one pc_cs variable

	__roundrobin = True

	__preanalysis = {}
	__visiting_struct = False
	__struct_stack = []               # stack of struct name

	__visit_funcReference = False

	__extra_nondet = '= __CSEQ_nondet_uint()'

	__donotcheckpointer = False

	__guess_cs_only = False

	# POR data structs for Read/Write analysis
	__visitingLPart = False          # set to true if visiting the left part of an assignment, i.e., lvalue is the written var
	__sharedVarsR = []               # set of shared vars read in the current statement being visited
	__sharedVarsW = []               # set of shared vars written in the current statement being visited
	__isArray = False                # used to flag that we are below an ArrayRef node
	__laddress = ''                  # used to store the address of lvalue while visiting the left-side of an assignment
	__inReference = False            # True iff within & scope

	# DR added to handle conditional expressions
	__visitingCE = False
	__conditionCE = ''
	__CEadditionalCondition = ''
	__CEadditionalSetFields = ''
	__CEreadVars=[]    #maintains the list of vars for which a conditional get_field clause is added in the current conditional exp
	__CEwriteVars=[]   #maintains the list of vars for which a conditional set_field clause is added in the current conditional exp 

	# DR data for discarding clearly benign dataraces (i.e., when we have write-write of the same value
	__dr_additionalCondition = '1'
	__wwDatarace = False 
	__enableDR = False
	__noShadow = False

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


	def loadfromstring(self, string, env):
		if self.getInputParamValue('deadlock') is not None:
			self._deadlockcheck = True

		threads = int(self.getInputParamValue('threads'))
		rounds = int(self.getInputParamValue('rounds'))
		backend = self.getInputParamValue('backend')
		self.__wwDatarace = env.wwDatarace
		self.__enableDR = env.enableDR
		self.__noShadow = env.no_shadow
		if self.getInputParamValue("preanalysis") is not None:
			self.__preanalysis = self.getInputParamValue("preanalysis")
			if env.debug:
				seqfile = core.utils.rreplace(env.inputfile, '/', '/_cs_', 1) if '/' in env.inputfile else '_cs_' + env.inputfile
				if env.outputfile is not None and env.outputfile != '':
					seqfile = env.outputfile
				logfile = seqfile + '.framac.log.extract'
				with open(logfile, "w") as logfile:
					logfile.write(str(self.__preanalysis))

		if self.getInputParamValue('decomposepc') is not None:
			self.__decomposepc = True

		if self.getInputParamValue('onepccs') is not None:
			self.__one_pc_cs = True

		if self.__decomposepc and self.__one_pc_cs:
			self.error("Cannot select to option decomposepc and onepccs at the same time\n")

		if self.getInputParamValue('norobin') is not None:
			self.__roundrobin = False

		if self.getInputParamValue('robin') is not None:
			self.__roundrobin = True

		if self.getInputParamValue('donotcheckvisiblepointer') is not None:
			self.__donotcheckpointer = True

		if self.getInputParamValue('guess-cs-only') is not None:
			self.__guess_cs_only = True

		self.__threadbound = threads

		super(self.__class__, self).loadfromstring(string, env)
		if backend == 'cbmc' or backend is None:
			self.__extra_nondet = ''

		if backend == 'klee':    # specific main for klee
			# Only use round robin style for klee
			if self.__decomposepc:
				self.output += self.__createMainKLEERoundRobinDecomposePC(rounds)
			elif self.__one_pc_cs:
				self.output += self.__createMainKLEERoundRobinOnePCCS(rounds)
			else:
				self.output += self.__createMainKLEERoundRobin(rounds)
		else:
			# Add the new main().
			if self.__roundrobin:
				if self.__decomposepc:
					self.output += self.__createMainRoundRobinDecomposePC(rounds)
				elif self.__one_pc_cs:
					self.output += self.__createMainRoundRobinOnePCCS(rounds)
				else:
					if self.__enableDR:
						self.output += self.__createMainRoundRobinDR(rounds)
					else:
						self.output += self.__createMainRoundRobin(rounds)
			else:
				if self.__decomposepc:
					self.output += self.__createMainDecomposePC(rounds)
				elif self.__one_pc_cs:
					self.output += self.__createMainOnePCCS(rounds)
				else:
					self.output += self.__createMain(rounds)

		# Insert the thread sizes (i.e. number of visible statements).
		lines = ''

		i = maxsize = 0

		for t in self.__threadName:
			if i <= self.__threadbound:
				if i>0: lines += ', '
				lines += str(self.__lines[t])
				maxsize = max(int(maxsize), int(self.__lines[t]))
				#print "CONFRONTO %s %s " % (int(maxsize), int(self.__lines[t]))
			i += 1
		if env.debug: print ("thread lines: {%s}" % lines),
		ones = ''
		if i <= self.__threadbound:
			if i>0: ones += ', '
			ones += '-1'
		i += 1

		# Generate the header.
		#
		# the first part is not parsable (contains macros)
		# so it is passed to next module as a header...

		if self.__decomposepc:
			header = core.utils.printFile('modules/lazyseqAdecomposepc.c')
		elif self.__one_pc_cs:
			header = core.utils.printFile('modules/lazyseqAonepccs.c')
		else:
			header = core.utils.printFile('modules/lazyseqA.c')
		header = header.replace('<insert-maxthreads-here>',str(threads))
		header = header.replace('<insert-maxrounds-here>',str(rounds))
		self.setOutputParam('header', header)


		i = 0
		pc_decls = ''
		pc_cs_decls = ''
		join_replace = ''
		thread_restart = ''
		for t in self.__threadName:
			if i <= self.__threadbound:
				threadsize = self.__lines[t]
				k = int(math.floor(math.log(threadsize,2)))+1
				pc_decls += 'unsigned int __cs_pc_%s;\n' % i
				self._bitwidth['','__cs_pc_%s' % i] = k
				pc_cs_decls += 'unsigned int __cs_pc_cs_%s;\n' % i
				self._bitwidth['','__cs_pc_cs_%s' % i] = k + 1
				join_replace += 'if (__cs_id == %s) __CSEQ_assume(__cs_pc_%s == __cs_thread_lines[%s]);\n' % (i, i, i)
				thread_restart += 'if (__cs_thread_index == %s) __cs_pc_cs_%s = 0;\n' % (i, i)
			i += 1
		join_replace += 'if (__cs_id >= %s) __CSEQ_assume(0);\n' % (i)
		thread_restart += 'if (__cs_thread_index >= %s) __CSEQ_assume(0);\n' % (i)

		# ..this is parsable and is added on top of the output code,
		# as next module is able to parse it.
		if self.__decomposepc:
			if not self._deadlockcheck:
				header = core.utils.printFile('modules/lazyseqBnewscheduledecomposepc.c').replace('<insert-threadsizes-here>',lines)
			else:
				header = core.utils.printFile('modules/lazyseqBdeadlocknewscheduledecomposepc.c').replace('<insert-threadsizes-here>',lines)
			header = header.replace('<insert-pc-decls-here>', pc_decls + pc_cs_decls )
			header = header.replace('<insert-join_replace-here>', join_replace)
			header = header.replace('<insert-thread_restart-here>', thread_restart)
			header = header.replace('<insert-numthreads-here>', str(threads+1))
		elif self.__one_pc_cs:
			if not self._deadlockcheck:
				header = core.utils.printFile('modules/lazyseqBnewscheduleonepccs.c').replace('<insert-threadsizes-here>',lines)
			else:
				header = core.utils.printFile('modules/lazyseqBdeadlocknewscheduleonepccs.c').replace('<insert-threadsizes-here>',lines)
			header = header.replace('<insert-numthreads-here>', str(threads+1))
		else:
			if not self._deadlockcheck:
				if self.__enableDR:
						if env.local==1:
							if env.isSwarm:
								header = core.utils.printFile('modules/dr_1lazyseqBnewschedule.c').replace('<insert-threadsizes-here>',"$THREADSIZE")
							else:
								header = core.utils.printFile('modules/dr_1lazyseqBnewschedule.c').replace('<insert-threadsizes-here>',lines)
						elif env.local==2:
							if env.isSwarm:
								header = core.utils.printFile('modules/dr_2lazyseqBnewschedule.c').replace('<insert-threadsizes-here>',"$THREADSIZE")
							else:
								header = core.utils.printFile('modules/dr_2lazyseqBnewschedule.c').replace('<insert-threadsizes-here>',lines)
						else:
							if env.isSwarm:
								header = core.utils.printFile('modules/dr_0lazyseqBnewschedule.c').replace('<insert-threadsizes-here>',"$THREADSIZE")
							else:
								header = core.utils.printFile('modules/dr_0lazyseqBnewschedule.c').replace('<insert-threadsizes-here>',lines)
				else:
					if env.isSwarm:
						header = core.utils.printFile('modules/lazyseqBnewschedule.c').replace('<insert-threadsizes-here>',"$THREADSIZE")
					else:
						header = core.utils.printFile('modules/lazyseqBnewschedule.c').replace('<insert-threadsizes-here>', lines)
			else:
				header = core.utils.printFile('modules/lazyseqBdeadlocknewschedule.c').replace('<insert-threadsizes-here>',lines)
			header = header.replace('<insert-numthreads-here>', str(threads+1))

		
		#header += 'unsigned int __cs_ts = 0; \n'   #POR 
		#header += 'unsigned int __cs_tsplusone = %s; \n' % (self.__threadbound+1)   #POR 
		#header += '_Bool __cs_is_por_exec = 1; \n'   #POR 
		#header += '_Bool __cs_isFirstRound = 1; \n'   #POR 
		header += '_Bool __cs_dataraceDetectionStarted = 0; \n'   #DR
		header += '_Bool __cs_dataraceSecondThread = 0; \n'   #DR
		header += '_Bool __cs_dataraceNotDetected = 1; \n'   #DR
		header += '_Bool __cs_dataraceContinue = 1; \n'   #DR
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

		self.insertheader(header)

		# Calculate exact bitwidth size for a few integer control variables of the seq. schema,
		# good in case the backend handles bitvectors.
		self._bitwidth['','__cs_active_thread'] = 1
		k = int(math.floor(math.log(maxsize,2)))+1
		if self.__decomposepc is False:
			self._bitwidth['','__cs_pc'] = k
			self._bitwidth['','__cs_pc_cs'] = k+1

		self._bitwidth['','__cs_thread_lines'] = k

		k = int(math.floor(math.log(self.__threadbound,2)))+1
		self._bitwidth['','__cs_last_thread'] = k
		self._bitwidth[core.common.changeID['pthread_mutex_lock'],'__cs_thread_index'] = k
		self._bitwidth[core.common.changeID['pthread_mutex_unlock'],'__cs_thread_index'] = k

		# self.setOutputParam('__cs_bitwidth', self._bitwidth)

		# Fix gotos by inserting ASS_GOTO(..) blocks before each goto,
		# excluding gotos which destination is the line below.
		for (a,b) in self.__labelLine:
			if (a,b) in self.__gotoLine and (self.__labelLine[a,b] == self.__gotoLine[a,b]+1):
				self.output = self.output.replace('<%s,%s>' % (a,b), '')
			else:
				self.output = self.output.replace('<%s,%s>' % (a,b), 'ASS_GOTO(%s)' % self.__labelLine[a,b])

		self.setOutputParam('bitwidth', self._bitwidth)


		self.setOutputParam('lines', self.__lines)
		self.setOutputParam('threadNames', self.__threadName)
		self.setOutputParam('threadIndex', self.__threadIndex)

	def visit_Decl(self,n,no_type=False):
		# no_type is used when a Decl is part of a DeclList, where the type is
		# explicitly only for the first declaration in a list.
		#
		s = n.name if no_type else self._generate_decl(n)

		if 'scalar' in self.__preanalysis and n.name in self.__preanalysis['scalar']:
			self._bitwidth[self.__currentThread, n.name] = self.__preanalysis['scalar'][n.name]

		if 'pointer' in self.__preanalysis and n.name in self.__preanalysis['pointer']:
			self._bitwidth[self.__currentThread, n.name] = self.__preanalysis['pointer'][n.name]

		if 'array' in self.__preanalysis and n.name in self.__preanalysis['array']:
			self._bitwidth[self.__currentThread, n.name] = self.__preanalysis['array'][n.name]

		if (self.__visiting_struct and
				'struct' in self.__preanalysis and
				self.__struct_stack[-1] in self.__preanalysis['struct'] and
				n.name in self.__preanalysis['struct'][self.__struct_stack[-1]]
				):
			# TODO: remember that for a field in struct, only multiple of 8bits is acceptable
			numbit = self.__preanalysis['struct'][self.__struct_stack[-1]][n.name]
			self._bitwidth[self.__struct_stack[-1], n.name] = numbit

		if n.bitsize: s += ' : ' + self.visit(n.bitsize)
		if n.init:
			s += ' = ' + self._visit_expr(n.init)
		return s

	def _generate_struct_union_enum(self, n, name):
		""" Generates code for structs, unions and enum. name should be either
			'struct' or 'union' or 'enum'.
		"""
		s = name + ' ' + (n.name or '')  #S original code
		# There should be no anonymous struct, handling in workarounds module
		self.__visiting_struct = True
		if n.name:
			self.__struct_stack.append(n.name)
		#S original code START
		if name in ('struct', 'union'):
			members = n.decls
			body_function = self._generate_struct_union_body
		else:
			assert name == 'enum'
			members = None if n.values is None else n.values.enumerators
			body_function = self._generate_enum_body
		s = name + ' ' + (n.name or '')
		if members is not None:
			# None means no members
			# Empty sequence means an empty list of members
			s += '\n'
			s += self._make_indent()
			self.indent_level += 2
			s += '{\n'
			s += body_function(members)
			self.indent_level -= 2
			s += self._make_indent() + '}'
		#S original code END
		self.__visiting_struct = False
		if n.name:
		   self.__struct_stack.pop()
		return s

	#DR
	def dr_state1(self,thread,lab,code):
		newcode = ''
		if self.__sharedVarsW:
			newcode += 'if ( ($L == __cs_pc_cs[%s]) & __cs_dataraceDetectionStarted & !__cs_dataraceSecondThread) {\n' % (thread)
			#print self.__sharedVarsW
			for v in self.__sharedVarsW:
				newcode += '__CPROVER_set_field(%s,"dr_write",1);\n' % v
			newcode += self.__CEadditionalSetFields #added to handle conditional expressions
			if self.__wwDatarace:
				newcode += code+';\n'
			newcode += '}\n'
		return newcode

	def dr_state2(self,thread,lab):
		condition=''
		code=''
		if self.__sharedVarsW:
			condition += '||'.join('__CPROVER_get_field(%s,"dr_write")' % i for i in  self.__sharedVarsW)
		list=[]    #S: added on March 2, 2021
		for x in self.__sharedVarsR:    #S: added on March 2, 2021
		   if x not in self.__sharedVarsW:    #S: added on March 2, 2021
			   list.append(x)    #S: added on March 2, 2021
		if list:    #S: modified on March 2, 2021
		   if condition != '': condition += '|| '
		   condition += '||'.join('__CPROVER_get_field(%s,"dr_write")' % i for i in list) #S: modified on March 2, 2021
		if condition != '' and self.__CEadditionalCondition != '':
		   condition += '|| ' + self.__CEadditionalCondition
		else:
		   condition += self.__CEadditionalCondition

		if condition != '':
			if self.__wwDatarace:
				code += 'if ( ($L == __cs_pc[%s]) & __cs_dataraceSecondThread & (%s) & (%s)) __cs_dataraceNotDetected = 0;' % (thread,self.__dr_additionalCondition,condition)
			else:
				code += 'if ( ($L == __cs_pc[%s]) & __cs_dataraceSecondThread & (%s)) __cs_dataraceNotDetected = 0;' % (thread,condition)
		return code

	def dr_codeParts(self, stmt, thread, lab):
		old_additionaCondition = self.__dr_additionalCondition   #DR
		self.__dr_additionalCondition = '1'   #DR
		code = self.visit(stmt)
		dr_part1 = self.dr_state1(thread,lab,code) #DR
		dr_part2 = self.dr_state2(thread,lab) #DR
		self.__dr_additionalCondition = old_additionaCondition   #DR
		return code,dr_part1,dr_part2


	def visit_Compound(self, n):
		compoundList = ["{\n"]
		# Insert the labels at the beginning of each statement,
		# with a few exclusions to reduce context-switch points...

		if n.block_items:
			for stmt in n.block_items:
				if self.__enableDR:
					#DR: added wrt Lazy-Cseq to handle conditions on writes/reads of globals
					self.__sharedVarsR = []
					self.__sharedVarsW = []
					self.__CEadditionalCondition = ''   #for conditional expressions
					self.__CEadditionalSetFields = ''   #for conditional expressions
					#DR end

				# Case 1: last statement in a thread (must correspond to last label)
				if type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == core.common.changeID['pthread_exit']: ##if type(stmt) == pycparser.c_ast.FuncCall and self._parenthesize_unless_simple(stmt.name) == core.common.changeID['pthread_exit']:
					self.__stmtCount += 1
					self.__maxInCompound = self.__stmtCount
					code = '$F ' + self.visit(stmt) + ';\n'
					compoundList.append(code)

				# Case 2: labels
				elif (type(stmt) in (pycparser.c_ast.Label,)):
					# --1-- Simulate a visit to the stmt block to see whether it makes any use of pointers or shared memory.
					globalAccess = self.__globalAccess(stmt)
					newStmt = ''
					# --2-- Now rebuilds the stmt block again,
					#       this time using the proper formatting
					#       (now we know if the statement is accessing global memory,
					#       so to insert the stamp at the beginning when needed)
					#
					if not self.__atomic and self.__stmtCount == -1:   # first statement in a thread
						self.__stmtCount += 1
						self.__maxInCompound = self.__stmtCount
						threadIndex = self.Parser.threadOccurenceIndex[self.__currentThread]
						if self.__enableDR:
							dr_code,dr_part1,dr_part2 = self.dr_codeParts(stmt.stmt,threadIndex,str(self.__stmtCount))  #DR
							code = '$I1' + dr_part1 + '$I2' + dr_part2 + '$I3' + dr_code + ';\n'
						else:
							code = '$I1$I2$I3' + self.visit(stmt.stmt) + ';\n'
					elif (not self.__visit_funcReference and (
						(type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == '__CSEQ_atomic_begin') or
						(not self.__atomic and
							(globalAccess or
							(type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == core.common.changeID['pthread_create']) or
							(type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == core.common.changeID['pthread_join']) or
							(type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name.startswith('__CSEQ_atomic') and not stmt.name.name == '__CSEQ_atomic_end') or
							(type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name.startswith('__CSEQ_assume')) or
							(type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == '__cs_cond_wait_2')
							)
						)
						)):
						self.__stmtCount += 1
						self.__maxInCompound = self.__stmtCount
						threadIndex = self.Parser.threadOccurenceIndex[self.__currentThread]
						if self.__enableDR:
							dr_code,dr_part1,dr_part2 = self.dr_codeParts(stmt.stmt,threadIndex,str(self.__stmtCount))  #DR
							code = '$I1' + dr_part1 + '$I2' + dr_part2 + '$I3' + dr_code + ';\n'
						else:
							code = '$I1$I2$I3' + self.visit(stmt.stmt) + ';\n'
					else:
						code = self.visit(stmt.stmt) + ';\n'

					guard = ''
					if not self.__atomic:
						guard = '$G'
					code = self._make_indent() + stmt.name + ': ' + guard + code + '\n'
					compoundList.append(code)

				# Case 3: all the rest....
				elif (type(stmt) not in (pycparser.c_ast.Compound, pycparser.c_ast.Goto, pycparser.c_ast.Decl)
					and not (self.__currentThread=='main' and self.__firstThreadCreate == False) or (self.__currentThread=='main' and self.__stmtCount == -1)) :

					# --1-- Simulate a visit to the stmt block to see whether it makes any use of pointers or shared memory.
					globalAccess = self.__globalAccess(stmt)
					newStmt = ''

					self.lines = set()   # override core.module marking behaviour, otherwise  module.visit()  won't insert any marker

					# --2-- Now rebuilds the stmt block again,
					#       this time using the proper formatting
					#      (now we know if the statement is accessing global memory,
					#       so to insert the stamp at the beginning when needed)
					if not self.__atomic and self.__stmtCount == -1:   # first statement in a thread
						self.__stmtCount += 1
						self.__maxInCompound = self.__stmtCount
						threadIndex = self.Parser.threadOccurenceIndex[self.__currentThread]
						if self.__enableDR:
							dr_code,dr_part1,dr_part2 = self.dr_codeParts(stmt,threadIndex,str(self.__stmtCount))  #DR
							code = '$I1' + dr_part1 + '$I2' + dr_part2 + '$I3' + dr_code + ';\n'
						else:
							code = '$I1$I2$I3' + self.visit(stmt) + ';\n'
					elif (not self.__visit_funcReference and (
						(type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == '__CSEQ_atomic_begin') or
						(not self.__atomic and
							(globalAccess or
							(type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == core.common.changeID['pthread_create']) or
							(type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == core.common.changeID['pthread_join']) or
							(type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name.startswith('__CSEQ_atomic') and not stmt.name.name == '__CSEQ_atomic_end') or
							(type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name.startswith('__CSEQ_assume')) or
							(type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == '__cs_cond_wait_2')
							)
						)
						)):
						self.__stmtCount += 1
						self.__maxInCompound = self.__stmtCount
						threadIndex = self.Parser.threadOccurenceIndex[self.__currentThread]
						if self.__enableDR:
							dr_code,dr_part1,dr_part2 = self.dr_codeParts(stmt,threadIndex,str(self.__stmtCount))  #DR
							code = '$I1' + dr_part1 + '$I2' + dr_part2 + '$I3' + dr_code + ';\n'
						else:
							code = '$I1$I2$I3' + self.visit(stmt) + ';\n'
					else:
						code = self.visit(stmt) + ";\n"
					compoundList.append(code)
				else:
					code = self.visit(stmt) + ";\n"
					compoundList.append(code)

		compoundList[len(compoundList)-1] = compoundList[len(compoundList)-1] + '\n}'
		listToStr = ''.join(stmt for stmt in compoundList)
		return listToStr

	def visit_FuncDef(self, n):
		if (n.decl.name.startswith('__CSEQ_atomic_') or
			#n.decl.name.startswith(core.common.funcPrefixChange['__CSEQ_atomic']) or
			n.decl.name == '__CSEQ_assert' or
			n.decl.name in self.Parser.funcReferenced ):   # <--- functions called through pointers are not inlined yet
			# return self.Parser.funcBlock[n.decl.name]
			self.__currentThread = n.decl.name
			self.__visit_funcReference = True
			#ret = self.otherparser.visit(n)
			oldatomic = self.__atomic
			self.__atomic = True
			decl = self.visit(n.decl)
			body = self.visit(n.body)
			self.__atomic = oldatomic
			s = decl + '\n' + body + '\n'
			self.__currentThread = ''
			self.__visit_funcReference = False
			return s
		elif (n.decl.name != 'main' and n.decl.name not in self.Parser.threadName): return ''  #S:added to remove not yet inlined functions that are not referenced any more
		self.__first = False
		self.__currentThread = n.decl.name
		self.__firstThreadCreate = False

		#Caledem
		# Next three lines were formerly from visit_FuncCall
		# This way we get the thread names in the order the thread definitions occour
		self.__threadName.append(n.decl.name)
		#self.Parser.threadOccurenceIndex[n.decl.name] = self.__threadCount
		#self.__threadCount = self.__threadCount + 1
		# 17/03/2021 C.J. Rossouw now computer in the parser to avoid function call befor declaration

		decl = self.visit(n.decl)
		self.indent_level = 0
		body = self.visit(n.body)

		f = ''

		self.__lines[self.__currentThread] = self.__stmtCount
		###print "THREAD %s, LINES %s \n\n" % (self.__currentThread, self.__lines)

		#
		if n.param_decls:
			knrdecls = ';\n'.join(self.visit(p) for p in n.param_decls)
			self.__stmtCount = -1
			#body = body[:body.rfind('}')] + self._make_indent() + returnStmt + '\n}'
			f = decl + '\n' + knrdecls + ';\n'
		else:
			self.__stmtCount = -1
			#body = body[:body.rfind('}')] + self._make_indent() + returnStmt + '\n}'
			f = decl + '\n'

		# Remove arguments (if any) for main() and transform them into local variables in main_thread.
		# TODO re-implement seriously.
		if self.__currentThread == 'main':
			f = '%s main_thread(void)\n' % self.Parser.funcBlockOut[
				self.__currentThread]
			main_args = self.Parser.funcBlockIn['main']
			args = ''
			if main_args.find('void') != -1 or main_args == '':
				main_args = ''
			else:
				main_args = re.sub(r'\*(.*)\[\]', r'** \1', main_args)
				main_args = re.sub(r'(.*)\[\]\[\]', r'** \1', main_args)
				# split argument
				main_args = main_args.split(',')
				if len(main_args) != 2:
					self.warn('main function may have been defined incorrectly, %s' % main_args)
				# args = 'static ' + main_args[0] + '= %s; ' % self.__argc
				# args = 'static ' + main_args[0] + '; '   # Disable this for SVCOMP
				args = main_args[0] + '; '
				# argv = self.__argv.split(' ')
				# argv = '{' + ','.join(['\"%s\"' % v for v in argv]) + '}'
				# args += 'static ' + main_args[1] + '= %s;' % argv
				# args += 'static ' + main_args[1] + ';'     # Disable this for SVCOMP
				args += main_args[1] + ';'
			body = '{' + args + body[body.find('{') + 1:]

		f += body + '\n'

		self.__currentThread = ''

		return f + '\n\n'


	def visit_If(self, n):
		ifStart = self.__maxInCompound   # label where the if stmt begins

		s = 'if ('

		if n.cond:
			condition = self.visit(n.cond)
			s += condition

		s += ')\n'
		s += self._generate_stmt(n.iftrue, add_indent=True)

		ifEnd = self.__maxInCompound   # label for the last stmt in the if block:  if () { block; }
		nextLabelID = ifEnd+1

		if n.iffalse:
			elseBlock = self._generate_stmt(n.iffalse, add_indent=True)

			elseEnd = self.__maxInCompound   # label for the last stmt in the if_false block if () {...} else { block; }

			if ifStart < ifEnd:
				#threadIndex = self.Parser.threadIndex[self.__currentThread] if self.__currentThread in self.Parser.threadIndex else 0
				# GUARD(%s,%s)
				if not self.__visit_funcReference:
					# elseHeader = '$G' + str(ifEnd+1) + ' '
					elseHeader = '$G '
					# if self.__decomposepc:
						## elseHeader = '__CSEQ_assume( __cs_pc_cs_%s >= %s );' % (threadIndex, str(ifEnd+1))
						# elseHeader = '__CSEQ_rawline($G__cs_pc_cs_%s >= $$);\n' % (threadIndex)
					# elif self.__one_pc_cs:
						## elseHeader = '__CSEQ_assume( __cs_pc_cs >= %s );' % (str(ifEnd+1))
						# elseHeader = '__CSEQ_rawline($G__cs_pc_cs_ >= $$);\n'
					# else:
						## elseHeader = '__CSEQ_assume( __cs_pc_cs[%s] >= %s );' % (threadIndex, str(ifEnd+1))
						# elseHeader = '__CSEQ_rawline($G__cs_pc_cs_[%s] >= $$);\n' % (threadIndex)
						## elseHeader = (guard.replace('$$',str(self.__stmtCount+1))

			else:
				elseHeader = ''

			nextLabelID = elseEnd+1
			s += self._make_indent() + 'else\n'

			elseBlock = elseBlock.replace('{', '{ '+elseHeader, 1)
			s += elseBlock

		header = ''

		if ifStart+1 < nextLabelID:
			#threadIndex = self.Parser.threadIndex[self.__currentThread] if self.__currentThread in self.Parser.threadIndex else 0
			# GUARD(%s,%s)
			if not self.__visit_funcReference:
				# footer = '$G' + str(nextLabelID) + ' '
				footer = '$G' + ' '
				#if self.__decomposepc:
					## footer = '__CSEQ_assume( __cs_pc_cs_%s >= %s );' % (threadIndex, nextLabelID)
					#footer = '__CSEQ_rawline($G__cs_pc_cs_%s >= $$);\n' % (threadIndex)
				#elif self.__one_pc_cs:
					## footer = '__CSEQ_assume( __cs_pc_cs >= %s );' % (nextLabelID)
					#footer = '__CSEQ_rawline($G__cs_pc_cs_ >= $$);\n'
				#else:
					## footer = '__CSEQ_assume( __cs_pc_cs[%s] >= %s );' % (threadIndex, nextLabelID)
					#footer = '__CSEQ_rawline($G__cs_pc_cs_[%s] >= $$);\n' % (threadIndex)

		else:
			footer = ''

		'''
		if n.iffalse:
			header = 'ASS_ELSE(%s, %s, %s)' % (condition, ifEnd+1, elseEnd+1) + '\n' + self._make_indent()
		else:
			if ifEnd > ifStart:
				header = 'ASS_THEN(%s, %s)' % (condition, ifEnd+1) + '\n' + self._make_indent()
			else: header = ''
		'''

		return header + s + self._make_indent() + footer


	def visit_Return(self, n):
		if self.__currentThread != '__CSEQ_assert' and self.__currentThread not in self.Parser.funcReferenced and not self.__atomic:
			self.error("error: %s: return statement in thread '%s'.\n" % (self.getname(), self.__currentThread))

		s = 'return'
		if n.expr: s += ' ' + self.visit(n.expr)
		return s + ';'


	def visit_Label(self, n):
		self.__labelLine[self.__currentThread, n.name] = self.__stmtCount
		return n.name + ':\n' + self._generate_stmt(n.stmt)


	def visit_Goto(self, n):
		self.__gotoLine[self.__currentThread, n.name] = self.__stmtCount
		extra = '<%s,%s>\n' % (self.__currentThread, n.name) + self._make_indent()
		extra = ''
		return extra + 'goto ' + n.name + ';'

	def visit_ArrayRef(self, n):
		old_isArray = self.__isArray  #POR
		self.__isArray = True  #POR
		arrref = self._parenthesize_unless_simple(n.name)
		self.__isArray = old_isArray #POR
		subscript = self.visit(n.subscript)
		#threadIndex = self.Parser.threadIndex[self.__currentThread] if self.__currentThread in self.Parser.threadIndex else 0
		threadIndex = self.Parser.threadOccurenceIndex[self.__currentThread] if self.__currentThread in self.Parser.threadOccurenceIndex else 0 # 17 March 2021
		if subscript == '__cs_thread_index' and self.__currentThread != '':
			subscript = '%s' % threadIndex
		s = arrref + '[' + subscript + ']'
		if self.__isGlobal(self.__currentThread, arrref):   #POR
			if self.__visitingCE: #DR
				if not self.__inReference and '&'+s not in self.__sharedVarsR and '&'+n.name not in self.__sharedVarsW and '&'+n.name not in self.__laddress and '&'+s not in self.__CEreadVars:   #DR
					if self.__CEadditionalCondition != '': self.__CEadditionalCondition +=' ||'
					self.__CEadditionalCondition +='( %s && __CPROVER_get_field(%s,"dr_write"))' % (self.__conditionCE, ('&'+s))    #DR
					self.__CEreadVars.append('&'+s)
					if self.__visitingLPart:
						self.laddress='&'+s
			else:  #general case
				if self.__visitingLPart == False and not self.__inReference and '&'+s not in self.__sharedVarsR:   #POR
					self.__sharedVarsR.append('&'+s)    #POR
				if  self.__visitingLPart == True:
					self.__laddress = '&'+s
		return s
	#end POR
	def visit_ID(self, n):
		# If this ID corresponds either to a global variable,
		# or to a pointer...
		#
		if ((self.__isGlobal(self.__currentThread, n.name) or self.__isPointer(self.__currentThread, n.name)) and not
			n.name.startswith('__cs_thread_local_')):
			#print "variable %s in %s is global\n" % (n.name, self.__currentThread)
			self.__globalMemoryAccessed = True
		#POR start
		if (self.__isGlobal(self.__currentThread, n.name) and not self.__isArray):
			if self.__visitingCE: #DR
				if not self.__inReference and '&'+n.name not in self.__sharedVarsR and '&'+n.name not in self.__sharedVarsW and '&'+n.name not in self.__laddress and '&'+n.name not in self.__CEreadVars:  #DR
					if self.__CEadditionalCondition != '': self.__CEadditionalCondition +=' ||'
					self.__CEadditionalCondition +='( %s && __CPROVER_get_field(%s,"dr_write"))' % (self.__conditionCE, ('&'+n.name))    #DR
					self.__CEreadVars.append('&'+n.name)
					if self.__visitingLPart:
						self.__laddress = '&'+n.name
			else:  #general case
				if self.__visitingLPart == False and not self.__inReference and '&'+n.name not in self.__sharedVarsR:
					self.__sharedVarsR.append('&'+n.name)
				if self.__visitingLPart == True:
					self.__laddress = '&'+n.name
		#POR end

		# Rename the IDs of main() arguments
		#if self.__currentThread == 'main' and n.name in self.Parser.varNames['main'] and self.Parser.varKind['main',n.name] == 'p':
		#   return '__main_params_' + n.name

		return n.name

	def visit_FuncCall(self, n):
		fref = self._parenthesize_unless_simple(n.name)
		args = self.visit(n.args)

		if fref == '__CSEQ_atomic_begin':
			if not self.__visit_funcReference:
				self.__atomic = True
			return ''
		elif fref == '__CSEQ_atomic_end':
			if not self.__visit_funcReference:
				self.__atomic = False
			return ''
		elif fref.startswith('__CSEQ_atomic_'):
			self.__globalMemoryAccessed = True
		elif fref == core.common.changeID['pthread_cond_wait']:
			self.error('pthread_cond_wait in input code (use conditional wait converter module first)')


		# When a thread is created, extract its function name
		# based on the 3rd parameter in the pthread_create() call:
		#
		# pthread_create(&id, NULL, f, &arg);
		#                          ^^^
		#
		if fref == core.common.changeID['pthread_create']: # TODO re-write AST-based (see other modules)
			fName = args[:args.rfind(',')]
			fName = fName[fName.rfind(',')+2:]
			fName = fName.replace('&', '')
			##__threadName in funcDef
			# if fName not in self.__threadName:
			#     self.__threadName.append(fName)
			#     self.__threadCount = self.__threadCount + 1

			#     args = args + ', %s' % (self.__threadCount)
			#     self.__threadIndex[fName] = self.__threadCount
			# else:
				# when visiting from the 2nd time on (if it happens),
				# reuse the old thread indexS!
			args = args + ', %s' % (self.Parser.threadOccurenceIndex[fName])

			self.__firstThreadCreate = True

		if fref == core.common.changeID['pthread_exit']:
			# 17 March 2021
			#threadIndex = self.Parser.threadIndex[self.__currentThread] if self.__currentThread in self.Parser.threadIndex else 0
			threadIndex = self.Parser.threadOccurenceIndex[
				self.__currentThread] if self.__currentThread in self.Parser.threadOccurenceIndex else 0
			return fref + '(' + args + ', %s)' % threadIndex

		'''
		Avoid using pointers to handle mutexes
		by changing the function calls,
		there are two cases:

		   pthread_mutex_lock(&l)   ->  __cs_mutex_lock(l)
		   pthread_mutex_lock(ptr)  ->  __cs_mutex_lock(*ptr)

		TODO:
		   this needs proper implementation,
		   one should check that the argument is not referenced
		   elsewhere (otherwise this optimisation will not work)
		'''

		# Optimization for removing __cs_thread_index variable from global scope
		if ((fref == core.common.changeID['pthread_mutex_lock'] ) or (fref == core.common.changeID['pthread_mutex_unlock']) or
				fref.startswith('__cs_cond_wait_')):
			#threadIndex = self.Parser.threadIndex[self.__currentThread] if self.__currentThread in self.Parser.threadIndex else 0
			threadIndex= self.Parser.threadOccurenceIndex[self.__currentThread] if self.__currentThread in self.Parser.threadOccurenceIndex else 0 # 17 March 2021
			return fref + '(' + args + ', %s)' % threadIndex
		#POR start
		#listArgs = args.split(', ')
		#if fref == '__CSEQ_atomic_load'or fref == '__CSEQ_atomic_exchange' or fref.startswith('__CSEQ_atomic_fetch'):
		#    if listArgs[0] not in self.__sharedVarsR:
		#        self.__sharedVarsR.append(listArgs[0])
		#if fref == '__CSEQ_atomic_store' or fref == '__CSEQ_atomic_exchange' or fref.startswith('__CSEQ_atomic_fetch'):
		#    if listArgs[0] not in self.__sharedVarsW:
		#        self.__sharedVarsW.append(listArgs[0])
		#if fref == '__CSEQ_atomic_compare_and_exchange':   #actually only one of the following occurs, but this is simpler ....
		#     if listArgs[0] not in self.__sharedVarsW:
		#        self.__sharedVarsW.append(listArgs[0])
		#     if listArgs[1] not in self.__sharedVarsW:
		#        self.__sharedVarsW.append(listArgs[1])
		#
		#POR end

		#S: fake implementation of pthread_key_create
		#   it is replaced with  __cs_key_create and last argument (the destroyer function pointer) is removed
		#   the body of __cs_key_create differs from that of pthread_key_create in that the
		#   storing of the detroyer function is removed

		if (fref == core.common.changeID['pthread_key_create'] ):
			#print (fref + '(' + args + ')')
			args = args[:args.rfind(',')]
			#print (fref + '(' + args + ')')

		return fref + '(' + args + ')'

	########################################################################################
	########################################################################################
	########################################################################################
	########################################################################################
	########################################################################################
	########################################################################################

	def __createMainRoundRobinDecomposePC(self, ROUNDS):
		'''  New main driver:
		'''
		main = ''
		main += "int main(void) {\n"

		''' Part I:
			Pre-guessed jump lengths have a size in bits depending on the size of the thread.
		'''
		for r in range(0, ROUNDS):
			for t in range(0,self.__threadbound+1):
				threadsize = self.__lines[self.__threadName[t]]
				k = int(math.floor(math.log(threadsize,2)))+1
				self._bitwidth['main','__cs_tmp_t%s_r%s' % (t,r)] = k

		''' First round (round 0)
		'''
		round = 0
		# Main thread
		main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
		main += "__CSEQ_rawline(\"    /* main */\");\n"
		main += "          unsigned int __cs_tmp_t0_r0 %s;\n" % self.__extra_nondet
		main += "          __CSEQ_assume(__cs_tmp_t0_r0 > 0);\n"
		main += "          __cs_pc_cs_0 = __cs_tmp_t0_r0;\n"
		main += "          __CSEQ_assume(__cs_pc_cs_0 <= %s);\n" % (self.__lines['main'])
		main += "          main_thread();\n"
		main += "          __cs_pc_0 = __cs_pc_cs_0;\n"
		main += "\n"
		# Other threads
		i = 1
		for t in self.__threadName:
			if t == 'main': continue
			if i <= self.__threadbound:
				main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
				main += "         unsigned int __cs_tmp_t%s_r0 %s;\n" % (i, self.__extra_nondet)
				main += "         if (__cs_active_thread[%s]) {\n" % (i)
				main += "             __cs_pc_cs_%s = __cs_tmp_t%s_r0;\n" % (i, i)
				main += "             __CSEQ_assume(__cs_pc_cs_%s <= %s);\n" % (i, self.__lines[t])
				main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
				main += "             __cs_pc_%s = __cs_pc_cs_%s;\n" % (i, i)
				main += "         }\n\n"
				i += 1

		''' Other rounds
		'''
		for round in range(1, ROUNDS):
			main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
			# For main thread
			main += "__CSEQ_rawline(\"    /* main */\");\n"
			main += "          unsigned int __cs_tmp_t0_r%s %s;\n" % (round, self.__extra_nondet)
			main += "          if (__cs_active_thread[0]) {\n"
			if self.__guess_cs_only:
				main += "             __cs_pc_cs_0 = __cs_tmp_t0_r%s;\n" % (round)
			else:
				main += "             __cs_pc_cs_0 = __cs_pc_0 + __cs_tmp_t0_r%s;\n" % (round)
			main += "             __CSEQ_assume(__cs_pc_cs_0 >= __cs_pc_0);\n"
			main += "             __CSEQ_assume(__cs_pc_cs_0 <= %s);\n" % (self.__lines['main'])
			main += "             main_thread();\n"
			main += "             __cs_pc_0 = __cs_pc_cs_0;\n"
			main += "          }\n\n"
			main += "\n"
			# For other threads
			i = 1
			for t in self.__threadName:
				if t == 'main': continue
				if i <= self.__threadbound:
					main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
					main += "         unsigned int __cs_tmp_t%s_r%s %s;\n" % (i, round, self.__extra_nondet)
					main += "         if (__cs_active_thread[%s]) {\n" % (i)
					if self.__guess_cs_only:
						main += "             __cs_pc_cs_%s = __cs_tmp_t%s_r%s;\n" % (i, i, round)
					else:
						main += "             __cs_pc_cs_%s = __cs_pc_%s + __cs_tmp_t%s_r%s;\n" % (i, i, i, round)
					main += "             __CSEQ_assume(__cs_pc_cs_%s >= __cs_pc_%s);\n" % (i, i)
					main += "             __CSEQ_assume(__cs_pc_cs_%s <= %s);\n" % (i, self.__lines[t])
					main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
					main += "             __cs_pc_%s = __cs_pc_cs_%s;\n" % (i, i)
					main += "         }\n\n"
					i += 1


		''' Last called to main
		'''

		# For the last call to main thread
		k = int(math.floor(math.log(self.__lines['main'],2)))+1
		main += "          unsigned int __cs_tmp_t0_r%s %s;\n" % (ROUNDS, self.__extra_nondet)
		self._bitwidth['main','__cs_tmp_t0_r%s' % (ROUNDS)] = k
		main += "           if (__cs_active_thread[0] == 1) {\n"
		if self.__guess_cs_only:
			main += "             __cs_pc_cs_0 = __cs_tmp_t0_r%s;\n" % (ROUNDS)
		else:
			main += "             __cs_pc_cs_0 = __cs_pc_0 + __cs_tmp_t0_r%s;\n" % (ROUNDS)
		main += "             __CSEQ_assume(__cs_pc_cs_0 >= __cs_pc_0);\n"
		main += "             __CSEQ_assume(__cs_pc_cs_0 <= %s);\n" % (self.__lines['main'])
		main += "             main_thread();\n"
		main += "           }\n"
		main += "    return 0;\n"
		main += "}\n\n"

		return main

	def __createMainRoundRobinOnePCCS(self, ROUNDS):
		'''  New main driver:
		'''
		main = ''
		main += "int main(void) {\n"

		''' Part I:
			Pre-guessed jump lengths have a size in bits depending on the size of the thread.
		'''

		maxsize = 0
		for t in self.__lines:
			maxsize = max(maxsize, int(self.__lines[t]))
		k = int(math.floor(math.log(maxsize,2)))+1

		for r in range(0, ROUNDS):
			for t in range(0,self.__threadbound+1):
				# threadsize = self.__lines[self.__threadName[t]]
				# k = int(math.floor(math.log(threadsize,2)))+1
				self._bitwidth['main','__cs_tmp_t%s_r%s' % (t,r)] = k

		''' First round (round 0)
		'''
		round = 0
		# Main thread
		main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
		main += "__CSEQ_rawline(\"    /* main */\");\n"
		main += "          unsigned int __cs_tmp_t%s_r0;\n" % self.Parser.threadOccurenceIndex['main']
		main += "          __cs_pc_cs = __cs_tmp_t%s_r0;\n" % self.Parser.threadOccurenceIndex['main']
		main += "          __CSEQ_assume(__cs_pc_cs <= %s);\n" % (self.__lines['main'])
		main += "          main_thread();\n"
		main += "          __cs_pc[%s] = __cs_pc_cs;\n" % self.Parser.threadOccurenceIndex['main']
		main += "\n"
		# Other threads
		i = 1
		for t in self.__threadName:
			if t == 'main': continue
			if i <= self.__threadbound:
				main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
				main += "         unsigned int __cs_tmp_t%s_r0;\n" % (i)
				main += "         if (__cs_active_thread[%s]) {\n" % (i)
				main += "             __cs_pc_cs = __cs_tmp_t%s_r0;\n" % (i)
				main += "             __CSEQ_assume(__cs_pc_cs <= %s);\n" % (i, self.__lines[t])
				main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
				main += "             __cs_pc[%s] = __cs_pc_cs;\n" % (i)
				main += "         }\n\n"
				i += 1

		''' Other rounds
		'''
		for round in range(1, ROUNDS):
			main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
			# For main thread
			main += "__CSEQ_rawline(\"    /* main */\");\n"
			main += "          unsigned int __cs_tmp_t%s_r%s;\n" % (self.Parser.threadOccurenceIndex['main'], round)
			main += "          if (__cs_active_thread[%s]) {\n"
			if self.__guess_cs_only:
				main += "             __cs_pc_cs = __cs_tmp_t%s_r%s;\n" % (self.Parser.threadOccurenceIndex['main'], round)
			else:
				main += "             __cs_pc_cs = __cs_pc[%s] + __cs_tmp_t%s_r%s;\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], round)
			main += "             __CSEQ_assume(__cs_pc_cs >= __cs_pc[%s]);\n" % self.Parser.threadOccurenceIndex['main']
			main += "             __CSEQ_assume(__cs_pc_cs <= %s);\n" % (self.__lines['main'])
			main += "             main_thread();\n"
			main += "             __cs_pc[%s] = __cs_pc_cs;\n" % self.Parser.threadOccurenceIndex['main']
			main += "          }\n\n"
			main += "\n"
			# For other threads
			i = 1
			for t in self.__threadName:
				if t == 'main': continue
				if i <= self.__threadbound:
					main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
					main += "         unsigned int __cs_tmp_t%s_r%s;\n" % (i, round)
					main += "         if (__cs_active_thread[%s]) {\n" % (i)
					if self.__guess_cs_only:
						main += "             __cs_pc_cs = __cs_tmp_t%s_r%s;\n" % (i, round)
					else:
						main += "             __cs_pc_cs = __cs_pc[%s] + __cs_tmp_t%s_r%s;\n" % (i, i, round)
					main += "             __CSEQ_assume(__cs_pc_cs >= __cs_pc[%s]);\n" % (i)
					main += "             __CSEQ_assume(__cs_pc_cs <= %s);\n" % (self.__lines[t])
					main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
					main += "             __cs_pc[%s] = __cs_pc_cs;\n" % (i)
					main += "         }\n\n"
					i += 1


		''' Last called to main
		'''

		# For the last call to main thread
		# k = int(math.floor(math.log(self.__lines['main'],2)))+1
		main += "          unsigned int __cs_tmp_t%s_r%s;\n" % (ROUNDS)
		self._bitwidth['main','__cs_tmp_t%s_r%s' % (self.Parser.threadOccurenceIndex['main'], ROUNDS)] = k
		main += "           if (__cs_active_thread[0] == 1) {\n"
		if self.__guess_cs_only:
			main += "             __cs_pc_cs = __cs_tmp_t%s_r%s;\n" % (self.Parser.threadOccurenceIndex['main'], ROUNDS)
		else:
			main += "             __cs_pc_cs = __cs_pc[%s] + __cs_tmp_t%s_r%s;\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], ROUNDS)
		main += "             __CSEQ_assume(__cs_pc_cs >= __cs_pc_%s);\n" % self.Parser.threadOccurenceIndex['main'] #da rivedere
		main += "             __CSEQ_assume(__cs_pc_cs <= %s);\n" % (self.__lines['main'])
		main += "             main_thread();\n"
		main += "           }\n"
		main += "    return 0;\n"
		main += "}\n\n"

		return main

	def __createMainDecomposePC(self, ROUNDS):
		'''  New main driver:
		'''
		main = ''
		main += "int main(void) {\n"

		''' Part I:
			Pre-guessed jump lengths have a size in bits depending on the size of the thread.
		'''
		for r in range(0, ROUNDS):
			for t in range(0,self.__threadbound+1):
				threadsize = self.__lines[self.__threadName[t]]
				k = int(math.floor(math.log(threadsize,2)))+1
				self._bitwidth['main','__cs_tmp_t%s_r%s' % (t,r)] = k

		''' First round (round 0)
		'''
		round = 0
		# Main thread
		main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
		main += "__CSEQ_rawline(\"    /* main */\");\n"
		main += "          unsigned int __cs_tmp_t0_r0 %s;\n" % self.__extra_nondet
		main += "          __CSEQ_assume(__cs_tmp_t0_r0 > 0);\n"
		main += "          __cs_pc_cs_0 = __cs_tmp_t0_r0;\n"
		main += "          __CSEQ_assume(__cs_pc_cs_0 <= %s);\n" % (self.__lines['main'])
		main += "          main_thread();\n"
		main += "          __cs_last_thread = 0;\n"
		main += "          __cs_pc_0 = __cs_pc_cs_0;\n"
		main += "\n"
		# Other threads
		i = 1
		for t in self.__threadName:
			if t == 'main': continue
			if i <= self.__threadbound:
				main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
				main += "         unsigned int __cs_tmp_t%s_r0 %s;\n" % (i, self.__extra_nondet)
				# main += "         __CSEQ_assume(__cs_tmp_t%s_r0 >= 0);\n" % (i)
				main += "         unsigned int __cs_run_t%s_r0 = (__cs_tmp_t%s_r0 && (__cs_active_thread[%s] == 1));\n" % (i, i, i)
				self._bitwidth['main','__cs_run_t%s_r0' % (i)] = 1     # Register to bitwidth parameter
				main += "         if (__cs_run_t%s_r0) {\n" % (i)
				main += "             __cs_pc_cs_%s = __cs_tmp_t%s_r0;\n" % (i, i)
				main += "             __CSEQ_assume(__cs_pc_cs_%s <= %s);\n" % (i, self.__lines[t])
				main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
				main += "             __cs_last_thread = %s;\n" % (i)
				main += "             __cs_pc_%s = __cs_pc_cs_%s;\n" % (i, i)
				main += "         }\n\n"
				i += 1

		''' Other rounds
		'''
		for round in range(1, ROUNDS):
			main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
			# For main thread
			main += "__CSEQ_rawline(\"    /* main */\");\n"
			main += "          __CSEQ_assume(__cs_last_thread != 0);\n"
			main += "          unsigned int __cs_tmp_t0_r%s %s;\n" % (round, self.__extra_nondet)
			# main += "         __CSEQ_assume(__cs_tmp_t0_r%s >= 0);\n" % (round)
			main += "          unsigned int __cs_run_t0_r%s = (__cs_tmp_t0_r%s && (__cs_active_thread[0] == 1));\n" % (round, round)
			self._bitwidth['main','__cs_run_t0_r%s' % (round)] = 1     # Register to bitwidth parameter
			main += "          if (__cs_run_t0_r%s) {\n" % (round)
			if self.__guess_cs_only:
				main += "             __cs_pc_cs_0 = __cs_tmp_t0_r%s;\n" % (round)
			else:
				main += "             __cs_pc_cs_0 = __cs_pc_0 + __cs_tmp_t0_r%s;\n" % (round)
			main += "             __CSEQ_assume(__cs_pc_cs_0 >= __cs_pc_0);\n"
			main += "             __CSEQ_assume(__cs_pc_cs_0 <= %s);\n" % (self.__lines['main'])
			main += "             main_thread();\n"
			main += "             __cs_last_thread = 0;\n"
			main += "             __cs_pc_0 = __cs_pc_cs_0;\n"
			main += "          }\n\n"
			main += "\n"
			# For other threads
			i = 1
			for t in self.__threadName:
				if t == 'main': continue
				if i <= self.__threadbound:
					main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
					main += "         __CSEQ_assume(__cs_last_thread != %s);\n" % (i)
					main += "         unsigned int __cs_tmp_t%s_r%s %s;\n" % (i, round, self.__extra_nondet)
					# main += "         __CSEQ_assume(__cs_tmp_t%s_r%s >= 0);\n" % (i, round)
					main += "         unsigned int __cs_run_t%s_r%s = (__cs_tmp_t%s_r%s && (__cs_active_thread[%s] == 1));\n" % (i, round, i, round, i)
					self._bitwidth['main','__cs_run_t%s_r%s' % (i, round)] = 1     # Register to bitwidth parameter
					main += "         if (__cs_run_t%s_r%s) {\n" % (i, round)
					if self.__guess_cs_only:
						main += "             __cs_pc_cs_%s = __cs_tmp_t%s_r%s;\n" % (i, i, round)
					else:
						main += "             __cs_pc_cs_%s = __cs_pc_%s + __cs_tmp_t%s_r%s;\n" % (i, i, i, round)
					main += "             __CSEQ_assume(__cs_pc_cs_%s >= __cs_pc_%s);\n" % (i, i)
					main += "             __CSEQ_assume(__cs_pc_cs_%s <= %s);\n" % (i, self.__lines[t])
					main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
					main += "             __cs_last_thread = %s;\n" % (i)
					main += "             __cs_pc_%s = __cs_pc_cs_%s;\n" % (i, i)
					main += "         }\n\n"
					i += 1


		''' Last called to main
		'''

		# For the last call to main thread
		k = int(math.floor(math.log(self.__lines['main'],2)))+1
		main += "          unsigned int __cs_tmp_t0_r%s %s;\n" % (ROUNDS, self.__extra_nondet)
		self._bitwidth['main','__cs_tmp_t0_r%s' % (ROUNDS)] = k
		# main += "         __CSEQ_assume(__cs_tmp_t0_r%s >= 0);\n" % (ROUNDS)
		main += "           if (__cs_active_thread[0] == 1) {\n"
		if self.__guess_cs_only:
			main += "             __cs_pc_cs_0 = __cs_tmp_t0_r%s;\n" % (ROUNDS)
		else:
			main += "             __cs_pc_cs_0 = __cs_pc_0 + __cs_tmp_t0_r%s;\n" % (ROUNDS)
		main += "             __CSEQ_assume(__cs_pc_cs_0 >= __cs_pc_0);\n"
		main += "             __CSEQ_assume(__cs_pc_cs_0 <= %s);\n" % (self.__lines['main'])
		main += "             main_thread();\n"
		main += "           }\n"
		main += "    return 0;\n"
		main += "}\n\n"

		return main

	def __createMainOnePCCS(self, ROUNDS):
		'''  New main driver:
		'''
		main = ''
		main += "int main(void) {\n"

		''' Part I:
			Pre-guessed jump lengths have a size in bits depending on the size of the thread.
		'''

		maxsize = 0
		for t in self.__lines:
			maxsize = max(maxsize, int(self.__lines[t]))
		k = int(math.floor(math.log(maxsize,2)))+1

		for r in range(0, ROUNDS):
			for t in range(0,self.__threadbound+1):
				# threadsize = self.__lines[self.__threadName[t]]
				# k = int(math.floor(math.log(threadsize,2)))+1
				self._bitwidth['main','__cs_tmp_t%s_r%s' % (t,r)] = k

		''' First round (round 0)
		'''
		round = 0
		# Main thread
		main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
		main += "__CSEQ_rawline(\"    /* main */\");\n"
		main += "          unsigned int __cs_tmp_t0_r0;\n"
		main += "          __CSEQ_assume(__cs_tmp_t0_r0 > 0);\n"
		main += "          __cs_pc_cs = __cs_tmp_t0_r0;\n"
		main += "          __CSEQ_assume(__cs_pc_cs <= %s);\n" % (self.__lines['main'])
		main += "          main_thread();\n"
		main += "          __cs_last_thread = 0;\n"
		main += "          __cs_pc[0] = __cs_pc_cs;\n"
		main += "\n"
		# Other threads
		i = 1
		for t in self.__threadName:
			if t == 'main': continue
			if i <= self.__threadbound:
				main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
				main += "         unsigned int __cs_tmp_t%s_r0;\n" % (i)
				# main += "         __CSEQ_assume(__cs_tmp_t%s_r0 >= 0);\n" % (i)
				main += "         unsigned int __cs_run_t%s_r0 = (__cs_tmp_t%s_r0 && (__cs_active_thread[%s] == 1));\n" % (i, i, i)
				self._bitwidth['main','__cs_run_t%s_r0' % (i)] = 1     # Register to bitwidth parameter
				main += "         if (__cs_run_t%s_r0) {\n" % (i)
				main += "             __cs_pc_cs = __cs_tmp_t%s_r0;\n" % (i)
				main += "             __CSEQ_assume(__cs_pc_cs_%s <= %s);\n" % (i, self.__lines[t])
				main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
				main += "             __cs_last_thread = %s;\n" % (i)
				main += "             __cs_pc[%s] = __cs_pc_cs;\n" % (i)
				main += "         }\n\n"
				i += 1

		''' Other rounds
		'''
		for round in range(1, ROUNDS):
			main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
			# For main thread
			main += "__CSEQ_rawline(\"    /* main */\");\n"
			main += "          __CSEQ_assume(__cs_last_thread != 0);\n"
			main += "          unsigned int __cs_tmp_t0_r%s;\n" % (round)
			# main += "         __CSEQ_assume(__cs_tmp_t0_r%s >= 0);\n" % (round)
			main += "          unsigned int __cs_run_t0_r%s = (__cs_tmp_t0_r%s && (__cs_active_thread[0] == 1));\n" % (round, round)
			self._bitwidth['main','__cs_run_t0_r%s' % (round)] = 1     # Register to bitwidth parameter
			main += "          if (__cs_run_t0_r%s) {\n" % (round)
			if self.__guess_cs_only:
				main += "             __cs_pc_cs = __cs_tmp_t0_r%s;\n" % (round)
			else:
				main += "             __cs_pc_cs = __cs_pc[0] + __cs_tmp_t0_r%s;\n" % (round)
			main += "             __CSEQ_assume(__cs_pc_cs >= __cs_pc_0);\n"
			main += "             __CSEQ_assume(__cs_pc_cs <= %s);\n" % (self.__lines['main'])
			main += "             main_thread();\n"
			main += "             __cs_last_thread = 0;\n"
			main += "             __cs_pc[0] = __cs_pc_cs;\n"
			main += "          }\n\n"
			main += "\n"
			# For other threads
			i = 1
			for t in self.__threadName:
				if t == 'main': continue
				if i <= self.__threadbound:
					main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
					main += "         __CSEQ_assume(__cs_last_thread != %s);\n" % (i)
					main += "         unsigned int __cs_tmp_t%s_r%s;\n" % (i, round)
					# main += "         __CSEQ_assume(__cs_tmp_t%s_r%s >= 0);\n" % (i, round)
					main += "         unsigned int __cs_run_t%s_r%s = (__cs_tmp_t%s_r%s && (__cs_active_thread[%s] == 1));\n" % (i, round, i, round, i)
					self._bitwidth['main','__cs_run_t%s_r%s' % (i, round)] = 1     # Register to bitwidth parameter
					main += "         if (__cs_run_t%s_r%s) {\n" % (i, round)
					if self.__guess_cs_only:
						main += "             __cs_pc_cs = __cs_tmp_t%s_r%s;\n" % (i, round)
					else:
						main += "             __cs_pc_cs = __cs_pc_%s + __cs_tmp_t%s_r%s;\n" % ( i, i, round)
					main += "             __CSEQ_assume(__cs_pc_cs >= __cs_pc_%s);\n" % (i)
					main += "             __CSEQ_assume(__cs_pc_cs <= %s);\n" % (self.__lines[t])
					main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
					main += "             __cs_last_thread = %s;\n" % (i)
					main += "             __cs_pc[%s] = __cs_pc_cs;\n" % (i)
					main += "         }\n\n"
					i += 1


		''' Last called to main
		'''

		# For the last call to main thread
		# k = int(math.floor(math.log(self.__lines['main'],2)))+1
		main += "          unsigned int __cs_tmp_t0_r%s;\n" % (ROUNDS)
		self._bitwidth['main','__cs_tmp_t0_r%s' % (ROUNDS)] = k
		# main += "         __CSEQ_assume(__cs_tmp_t0_r%s >= 0);\n" % (ROUNDS)
		main += "           if (__cs_active_thread[0] == 1) {\n"
		if self.__guess_cs_only:
			main += "             __cs_pc_cs = __cs_tmp_t0_r%s;\n" % (ROUNDS)
		else:
			main += "             __cs_pc_cs = __cs_pc[0] + __cs_tmp_t0_r%s;\n" % (ROUNDS)
		main += "             __CSEQ_assume(__cs_pc_cs >= __cs_pc[0]);\n"
		main += "             __CSEQ_assume(__cs_pc_cs <= %s);\n" % (self.__lines['main'])
		main += "             main_thread();\n"
		main += "           }\n"
		main += "    return 0;\n"
		main += "}\n\n"

		return main

	def __createMainRoundRobin(self, ROUNDS):
		'''  New main driver:
		'''
		main = ''
		main += "int main(void) {\n"

		''' Part I:
			Pre-guessed jump lengths have a size in bits depending on the size of the thread.
		'''
		for r in range(0, ROUNDS):
			for t in range(0,self.__threadbound+1):
				threadsize = self.__lines[self.__threadName[t]]
				k = int(math.floor(math.log(threadsize,2)))+1
				self._bitwidth['main','__cs_tmp_t%s_r%s' % (t,r)] = k

		''' First round (round 0)
		'''
		round = 0
		# Main thread
		main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
		main += "__CSEQ_rawline(\"    /* main */\");\n"
		#caledem
		main += "__cs_active_thread[%s] = 1;\n" % self.Parser.threadOccurenceIndex['main']
		main += "          unsigned int __cs_tmp_t%s_r0 %s;\n" % (self.Parser.threadOccurenceIndex['main'], self.__extra_nondet)
		main += "          __cs_pc_cs[%s] = __cs_tmp_t%s_r0;\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'])
		main += "          __CSEQ_assume(__cs_pc_cs[%s] > 0);\n" % self.Parser.threadOccurenceIndex['main']
		main += "          __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (self.Parser.threadOccurenceIndex['main'], "$ML" + str(self.Parser.threadOccurenceIndex['main']))
		main += "          main_thread();\n"
		main += "          __cs_pc[%s] = __cs_pc_cs[%s];\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'])
		main += "\n"
		# Other threads
		i = 0
		for t in self.__threadName:
			if t == 'main': continue
			if i <= self.__threadbound:
				main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
				main += "         unsigned int __cs_tmp_t%s_r0 %s;\n" % (i, self.__extra_nondet)
				main += "         if (__cs_active_thread[%s]) {\n" % (i)
				main += "             __cs_pc_cs[%s] = __cs_tmp_t%s_r0;\n" % (i, i)
				main += "             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (i, "$ML" + str(self.Parser.threadOccurenceIndex[t]))
				main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
				main += "             __cs_pc[%s] = __cs_pc_cs[%s];\n" % (i, i)
				main += "         }\n\n"
				i += 1

		''' Other rounds
		'''
		for round in range(1, ROUNDS):
			main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
			# For main thread
			main += "__CSEQ_rawline(\"    /* main */\");\n"
			main += "          unsigned int __cs_tmp_t%s_r%s %s;\n" % (self.Parser.threadOccurenceIndex['main'], round, self.__extra_nondet)
			main += "          if (__cs_active_thread[%s]) {\n" % self.Parser.threadOccurenceIndex['main']
			if self.__guess_cs_only:
				main += "             __cs_pc_cs[%s] = __cs_tmp_t%s_r%s;\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], round)
			else:
				main += "             __cs_pc_cs[%s] = __cs_pc[%s] + __cs_tmp_t%s_r%s;\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], round)
			main += "             __CSEQ_assume(__cs_pc_cs[%s] >= __cs_pc[%s]);\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'])
			main += "             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (self.Parser.threadOccurenceIndex['main'], "$ML" + str(self.Parser.threadOccurenceIndex['main']))
			main += "             main_thread();\n"
			main += "             __cs_pc[%s] = __cs_pc_cs[%s];\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'])
			main += "          }\n\n"
			main += "\n"
			# For other threads
			i = 0
			for t in self.__threadName:
				if t == 'main': continue
				if i <= self.__threadbound:
					main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
					main += "         unsigned int __cs_tmp_t%s_r%s %s;\n" % (i, round, self.__extra_nondet)
					main += "         if (__cs_active_thread[%s]) {\n" % (i)
					if self.__guess_cs_only:
						main += "             __cs_pc_cs[%s] = __cs_tmp_t%s_r%s;\n" % (i, i, round)
					else:
						main += "             __cs_pc_cs[%s] = __cs_pc[%s] + __cs_tmp_t%s_r%s;\n" % (i, i, i, round)
					main += "             __CSEQ_assume(__cs_pc_cs[%s] >= __cs_pc[%s]);\n" % (i, i)
					main += "             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (i, "$ML" + str(self.Parser.threadOccurenceIndex[t]))
					main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
					main += "             __cs_pc[%s] = __cs_pc_cs[%s];\n" % (i, i)
					main += "         }\n\n"
					i += 1


		''' Last called to main
		'''

		# For the last call to main thread
		k = int(math.floor(math.log(self.__lines['main'],2)))+1
		main += "          unsigned int __cs_tmp_t%s_r%s %s;\n" % (self.Parser.threadOccurenceIndex['main'], ROUNDS, self.__extra_nondet)
		self._bitwidth['main','__cs_tmp_t%s_r%s' % (self.Parser.threadOccurenceIndex['main'], ROUNDS)] = k
		main += "           if (__cs_active_thread[%s] == 1) {\n" % self.Parser.threadOccurenceIndex['main']
		if self.__guess_cs_only:
			main += "             __cs_pc_cs[%s] = __cs_tmp_t%s_r%s;\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], ROUNDS)
		else:
			main += "             __cs_pc_cs[%s] = __cs_pc[%s] + __cs_tmp_t%s_r%s;\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], ROUNDS)
		main += "             __CSEQ_assume(__cs_pc_cs[%s] >= __cs_pc[%s]);\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'])
		main += "             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (self.Parser.threadOccurenceIndex['main'], "$ML" + str(self.Parser.threadOccurenceIndex['main']))
		main += "             main_thread();\n"
		main += "           }\n"
		main += "    return 0;\n"
		main += "}\n\n"

		return main

	def __createMainRoundRobinDR(self, ROUNDS):
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
			for t in range(0,self.__threadbound+1):
				threadsize = self.__lines[self.__threadName[t]]
				k = int(math.floor(math.log(threadsize,2)))+1
				self._bitwidth['main','__cs_tmp_t%s_r%s' % (t,r)] = k

		maxts = ROUNDS*(self.__threadbound+1)-2  #DR
		main +="          unsigned int __cs_dr_ts %s;\n" % self.__extra_nondet   #DR
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
		main +="          unsigned int __cs_tmp_t%s_r0 %s;\n" % (self.Parser.threadOccurenceIndex['main'], self.__extra_nondet)
		main +="          __cs_pc_cs[%s] = __cs_tmp_t%s_r0;\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'])
		main +="          __CSEQ_assume(__cs_pc_cs[%s] > 0);\n" % self.Parser.threadOccurenceIndex['main']
		main +="          __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (self.Parser.threadOccurenceIndex['main'], "$ML" + str(self.Parser.threadOccurenceIndex['main']))
		main +="          if(__cs_dr_ts == 0) __cs_dataraceDetectionStarted=1;\n"
		main +="          main_thread();\n"
		main +="          if(__cs_dataraceDetectionStarted) __cs_dataraceSecondThread=1;\n"  #DR
		main +="          __cs_pc[%s] = __cs_pc_cs[%s];\n"   % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'])
		main +="\n"
		# Other threads
		ts = 1 #DR
		i = 0
		for t in self.__threadName:
			if t == 'main': continue
			if i <= self.__threadbound:
				main +="__CSEQ_rawline(\"    /* %s */\");\n" % t
				#main +="__CSEQ_rawline(\"__cs_ts=%s;\");\n" % i   #POR
				#main +="__CSEQ_rawline(\"__cs_tsplusone=%s;\");\n" % ( self.__threadbound+1+i)   #POR
				main +="         unsigned int __cs_tmp_t%s_r0 %s;\n" % (i, self.__extra_nondet)
				main +="         if (__cs_dataraceContinue & __cs_active_thread[%s]) {\n" % (i)           #DR
				main +="             __cs_pc_cs[%s] = __cs_tmp_t%s_r0;\n" % (i, i)
				main +="             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (i, "$ML" + str(self.Parser.threadOccurenceIndex[t]))
				#main +="             __cs_noportest=0;\n"   #POR
				if ts <= maxts :   #DR
					  main +="             if(__cs_dr_ts == %s) __cs_dataraceDetectionStarted=1;\n" % ts #DR
				main +="             %s(__cs_threadargs[%s]);\n" % (t, i)
				main +="             if(__cs_dataraceSecondThread & (__cs_tmp_t%s_r0 > __cs_pc[%s])) __cs_dataraceContinue=0;\n" % (i,i) #DR
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
			#main +="__CSEQ_rawline(\"__cs_ts=%s;\");\n" % (round * (self.__threadbound+1))   #POR
			#main +="__CSEQ_rawline(\"__cs_tsplusone=%s;\");\n" % ( (round+1) * ( self.__threadbound+1) )  #POR
			main +="          unsigned int __cs_tmp_t%s_r%s %s;\n" % (self.Parser.threadOccurenceIndex['main'],round, self.__extra_nondet)
			main +="          if (__cs_dr_ts > %s &  __cs_dataraceContinue & __cs_active_thread[%s]) {\n" %  (ts - (self.__threadbound+1), self.Parser.threadOccurenceIndex['main'])          #DR
			if self.__guess_cs_only:
				main +="             __cs_pc_cs[%s] = __cs_tmp_t%s_r%s;\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], round)
			else:
				main +="             __cs_pc_cs[%s] = __cs_pc[%s] + __cs_tmp_t%s_r%s;\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], round)
			main +="             __CSEQ_assume(__cs_pc_cs[%s] >= __cs_pc[%s]);\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'])
			main +="             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (self.Parser.threadOccurenceIndex['main'], "$ML" + str(self.Parser.threadOccurenceIndex['main']))
			if ts <= maxts :   #DR
				main +="             if(__cs_dr_ts == %s) __cs_dataraceDetectionStarted=1;\n" % ts  #DR
			main +="             main_thread();\n"
			main +="             if(__cs_dataraceSecondThread & (__cs_tmp_t%s_r%s > __cs_pc[%s])) __cs_dataraceContinue=0;\n" % (self.Parser.threadOccurenceIndex['main'], round, self.Parser.threadOccurenceIndex['main']) #DR
			if ts <= maxts :   #DR
				main +="             if(__cs_dataraceDetectionStarted) __cs_dataraceSecondThread=1;\n"  #DR
			#main +="             __CSEQ_assume(__cs_is_por_exec);\n" #POR
			main +="             __cs_pc[%s] = __cs_pc_cs[%s];\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'])
			main +="          }\n\n"
			main +="\n"
			# For other threads
			ts += 1 #DR
			i = 0
			for t in self.__threadName:
				if t == 'main': continue
				if i <= self.__threadbound:
					main +="__CSEQ_rawline(\"    /* %s */\");\n" % t
					#main +="__CSEQ_rawline(\"__cs_ts=%s;\");\n" % (round * (self.__threadbound+1) + i )   #POR
					#if (round == ROUNDS -1):
						#main +="__CSEQ_rawline(\"__cs_tsplusone=%s;\");\n" % ( (round+1) * ( self.__threadbound+1))  #POR
					#else:
						#main +="__CSEQ_rawline(\"__cs_tsplusone=%s;\");\n" % ( (round+1) * ( self.__threadbound+1) + i)  #POR
					main +="         unsigned int __cs_tmp_t%s_r%s %s;\n" % (i, round, self.__extra_nondet)
					main +="         if (__cs_dr_ts > %s & __cs_dataraceContinue & __cs_active_thread[%s]) {\n" % ( ts - (self.__threadbound+1) ,i)           #DR
					if self.__guess_cs_only:
						main +="             __cs_pc_cs[%s] = __cs_tmp_t%s_r%s;\n" % (i, i, round)
					else:
						main +="             __cs_pc_cs[%s] = __cs_pc[%s] + __cs_tmp_t%s_r%s;\n" % (i, i, i, round)
					main +="             __CSEQ_assume(__cs_pc_cs[%s] >= __cs_pc[%s]);\n" % (i, i)
					main +="             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (i, '$ML' + str(self.Parser.threadOccurenceIndex[t]))
					#main +="             __cs_noportest=0;\n"  #POR
					if ts <= maxts :   #DR
						 main +="             if(__cs_dr_ts == %s) __cs_dataraceDetectionStarted=1;\n" %  ts #DR
					main +="             %s(__cs_threadargs[%s]);\n" % (t, i)
					main +="             if(__cs_dataraceSecondThread & (__cs_tmp_t%s_r%s > __cs_pc[%s])) __cs_dataraceContinue=0;\n" % (i,round, i) #DR
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
		#k = int(math.floor(math.log(self.__lines['main'],2)))+1
		#main += "          unsigned int __cs_tmp_t0_r%s %s;\n" % (ROUNDS, self.__extra_nondet)
		#self._bitwidth['main','__cs_tmp_t0_r%s' % (ROUNDS)] = k
		#main +="           if (__cs_dr_ts > %s & __cs_dataraceContinue & __cs_active_thread[0]) {\n" % ((round-1) * (self.__threadbound+1)+i) #DR
		#if self.__guess_cs_only:
		#    main +="             __cs_pc_cs[0] = __cs_tmp_t0_r%s;\n" % (ROUNDS)
		#else:
		#    main +="             __cs_pc_cs[0] = __cs_pc[0] + __cs_tmp_t0_r%s;\n" % (ROUNDS)
		#main +="             __CSEQ_assume(__cs_pc_cs[0] >= __cs_pc[0]);\n"
		#main +="             __CSEQ_assume(__cs_pc_cs[0] <= %s);\n" % (self.__lines['main'])
		##main +="             __cs_noportest=0;\n"  #POR
		#main +="             __cs_main_thread();\n"
		#main +="           }\n"
		main +="     __CPROVER_assert(__cs_dataraceNotDetected,\"Data race failure\");\n"
		main += "    return 0;\n"
		main += "}\n\n"

		return main

	def __createMain(self, ROUNDS):
		'''  New main driver:
		'''
		main = ''
		main += "int main(void) {\n"

		''' Part I:
			Pre-guessed jump lengths have a size in bits depending on the size of the thread.
		'''
		for r in range(0, ROUNDS):
			for t in range(0,self.__threadbound+1):
				threadsize = self.__lines[self.__threadName[t]]
				k = int(math.floor(math.log(threadsize,2)))+1
				self._bitwidth['main','__cs_tmp_t%s_r%s' % (t,r)] = k

		''' First round (round 0)
		'''
		round = 0
		# Main thread
		main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
		main += "__CSEQ_rawline(\"    /* main */\");\n"
		main += "          unsigned int __cs_tmp_t0_r0 %s;\n" % self.__extra_nondet
		main += "          __CSEQ_assume(__cs_tmp_t0_r0 > 0);\n"
		main += "          __cs_pc_cs[0] = __cs_tmp_t0_r0;\n"
		main += "          __CSEQ_assume(__cs_pc_cs[0] <= %s);\n" % "$MLM"
		main += "          main_thread();\n"
		main += "          __cs_last_thread = 0;\n"
		main += "          __cs_pc[0] = __cs_pc_cs[0];\n"
		main += "\n"
		# Other threads
		i = 1
		for t in self.__threadName:
			if t == 'main': continue
			if i <= self.__threadbound:
				main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
				main += "         unsigned int __cs_tmp_t%s_r0 %s;\n" % (i, self.__extra_nondet)
				main += "         unsigned int __cs_run_t%s_r0 = (__cs_tmp_t%s_r0 && (__cs_active_thread[%s] == 1));\n" % (i, i, i)
				self._bitwidth['main','__cs_run_t%s_r0' % (i)] = 1     # Register to bitwidth parameter
				main += "         if (__cs_run_t%s_r0) {\n" % (i)
				main += "             __cs_pc_cs[%s] = __cs_tmp_t%s_r0;\n" % (i, i)
				main += "             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (i, "$ML" + str(self.Parser.threadOccurenceIndex[t]))
				main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
				main += "             __cs_last_thread = %s;\n" % (i)
				main += "             __cs_pc[%s] = __cs_pc_cs[%s];\n" % (i, i)
				main += "         }\n\n"
				i += 1

		''' Other rounds
		'''
		for round in range(1, ROUNDS):
			main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
			# For main thread
			main += "__CSEQ_rawline(\"    /* main */\");\n"
			main += "          __CSEQ_assume(__cs_last_thread != 0);\n"
			main += "          unsigned int __cs_tmp_t0_r%s %s;\n" % (round, self.__extra_nondet)
			main += "          unsigned int __cs_run_t0_r%s = (__cs_tmp_t0_r%s && (__cs_active_thread[0] == 1));\n" % (round, round)
			self._bitwidth['main','__cs_run_t0_r%s' % (round)] = 1     # Register to bitwidth parameter
			main += "          if (__cs_run_t0_r%s) {\n" % (round)
			if self.__guess_cs_only:
				main += "             __cs_pc_cs[0] = __cs_tmp_t0_r%s;\n" % (round)
			else:
				main += "             __cs_pc_cs[0] = __cs_pc[0] + __cs_tmp_t0_r%s;\n" % (round)
			main += "             __CSEQ_assume(__cs_pc_cs[0] >= __cs_pc[0]);\n"
			main += "             __CSEQ_assume(__cs_pc_cs[0] <= %s);\n" % "$MLM"
			main += "             main_thread();\n"
			main += "             __cs_last_thread = 0;\n"
			main += "             __cs_pc[0] = __cs_pc_cs[0];\n"
			main += "          }\n\n"
			main += "\n"
			# For other threads
			i = 1
			for t in self.__threadName:
				if t == 'main': continue
				if i <= self.__threadbound:
					main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
					main += "         __CSEQ_assume(__cs_last_thread != %s);\n" % (i)
					main += "         unsigned int __cs_tmp_t%s_r%s %s;\n" % (i, round, self.__extra_nondet)
					main += "         unsigned int __cs_run_t%s_r%s = (__cs_tmp_t%s_r%s && (__cs_active_thread[%s] == 1));\n" % (i, round, i, round, i)
					self._bitwidth['main','__cs_run_t%s_r%s' % (i, round)] = 1     # Register to bitwidth parameter
					main += "         if (__cs_run_t%s_r%s) {\n" % (i, round)
					if self.__guess_cs_only:
						main += "             __cs_pc_cs[%s] = __cs_tmp_t%s_r%s;\n" % (i, i, round)
					else:
						main += "             __cs_pc_cs[%s] = __cs_pc[%s] + __cs_tmp_t%s_r%s;\n" % (i, i, i, round)
					main += "             __CSEQ_assume(__cs_pc_cs[%s] >= __cs_pc[%s]);\n" % (i, i)
					main += "             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (i,"$ML" + str(self.Parser.threadOccurenceIndex[t]))
					main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
					main += "             __cs_last_thread = %s;\n" % (i)
					main += "             __cs_pc[%s] = __cs_pc_cs[%s];\n" % (i, i)
					main += "         }\n\n"
					i += 1


		''' Last called to main
		'''

		# For the last call to main thread
		k = int(math.floor(math.log(self.__lines['main'],2)))+1
		main += "          unsigned int __cs_tmp_t0_r%s %s;\n" % (ROUNDS, self.__extra_nondet)
		self._bitwidth['main','__cs_tmp_t0_r%s' % (ROUNDS)] = k
		main += "           if (__cs_active_thread[0] == 1) {\n"
		if self.__guess_cs_only:
			main += "             __cs_pc_cs[0] = __cs_tmp_t0_r%s;\n" % (ROUNDS)
		else:
			main += "             __cs_pc_cs[0] = __cs_pc[0] + __cs_tmp_t0_r%s;\n" % (ROUNDS)
		main += "             __CSEQ_assume(__cs_pc_cs[0] >= __cs_pc[0]);\n"
		main += "             __CSEQ_assume(__cs_pc_cs[0] <= %s);\n" % "$MLM"
		main += "             main_thread();\n"
		main += "           }\n"
		main += "    return 0;\n"
		main += "}\n\n"

		return main

	#######################################################################################################
	#######################################################################################################
	#######################################################################################################
	#######################################################################################################
	#######################################################################################################
	#######################################################################################################
	#######################################################################################################

	def __createMainKLEERoundRobinDecomposePC(self, ROUNDS):
		'''  New main driver:
		'''
		main = ''
		main += "int main(void) {\n"
		''' First round (round 0)
		'''
		round = 0
		# Main thread
		main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
		main += "__CSEQ_rawline(\"    /* main */\");\n"
		main += "          __cs_pc_cs_0 = klee_range(1, %s, \"__cs_pc_cs_0\");\n" % (self.__lines['main'] + 1)
		main += "          main_thread();\n"
		main += "          __cs_pc_0 = __cs_pc_cs_0;\n"
		main += "\n"
		# Other threads
		i = 1
		for t in self.__threadName:
			if t == 'main': continue
			if i <= self.__threadbound:
				main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
				main += "         if (__cs_active_thread[%s]) {\n" % (i)
				main += "             __cs_pc_cs_%s = klee_range(0, %s, \"__cs_pc_cs_%s\");\n" % (i, self.__lines[t] + 1, i)
				main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
				main += "             __cs_pc_%s = __cs_pc_cs_%s;\n" % (i, i)
				main += "         }\n\n"
				i += 1

		''' Other rounds
		'''
		for round in range(1, ROUNDS):
			main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
			# For main thread
			main += "__CSEQ_rawline(\"    /* main */\");\n"
			main += "          if (__cs_active_thread[0]) {\n"
			main += "             __cs_pc_cs_0 = klee_range(__cs_pc_0, %s, \"__cs_pc_cs_0\");\n" % (self.__lines['main'] + 1)
			main += "             main_thread();\n"
			main += "             __cs_pc_0 = __cs_pc_cs_0;\n"
			main += "          }\n\n"
			main += "\n"
			# For other threads
			i = 1
			for t in self.__threadName:
				if t == 'main': continue
				if i <= self.__threadbound:
					main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
					main += "         if (__cs_active_thread[%s]) {\n" % (i)
					main += "             __cs_pc_cs_%s = klee_range(__cs_pc_%s, %s, \"__cs_pc_cs_%s\");\n" % (i, i, self.__lines[t] + 1, i)
					main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
					main += "             __cs_pc_%s = __cs_pc_cs_%s;\n" % (i, i)
					main += "         }\n\n"
					i += 1


		''' Last called to main
		'''

		# For the last call to main thread
		main += "           if (__cs_active_thread[0] == 1) {\n"
		main += "             __cs_pc_cs_0 = klee_range(__cs_pc_0, %s, \"__cs_pc_cs_0\");\n" % (self.__lines['main'] + 1)
		main += "             main_thread();\n"
		main += "           }\n"
		main += "    return 0;\n"
		main += "}\n\n"

		return main

	def __createMainKLEERoundRobinOnePCCS(self, ROUNDS):
		'''  New main driver:
		'''
		main = ''
		main += "int main(void) {\n"

		''' First round (round 0)
		'''
		round = 0
		# Main thread
		main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
		main += "__CSEQ_rawline(\"    /* main */\");\n"
		main += "          __cs_pc_cs = klee_range(1, %s, \"__cs_pc_cs\");\n" % (self.__lines['main'] + 1)
		main += "          main_thread();\n"
		main += "          __cs_pc[0] = __cs_pc_cs;\n"
		main += "\n"
		# Other threads
		i = 1
		for t in self.__threadName:
			if t == 'main': continue
			if i <= self.__threadbound:
				main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
				main += "         if (__cs_active_thread[%s]) {\n" % (i)
				main += "             __cs_pc_cs = klee_range(0, %s, \"__cs_pc_cs\");\n" % (self.__lines[t] + 1)
				main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
				main += "             __cs_pc[%s] = __cs_pc_cs;\n" % (i)
				main += "         }\n\n"
				i += 1

		''' Other rounds
		'''
		for round in range(1, ROUNDS):
			main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
			# For main thread
			main += "__CSEQ_rawline(\"    /* main */\");\n"
			main += "          if (__cs_active_thread[0]) {\n"
			main += "             __cs_pc_cs = klee_range(__cs_pc[0], %s, \"__cs_pc_cs\");\n" % (self.__lines['main'] + 1)
			main += "             main_thread();\n"
			main += "             __cs_pc[0] = __cs_pc_cs;\n"
			main += "          }\n\n"
			main += "\n"
			# For other threads
			i = 1
			for t in self.__threadName:
				if t == 'main': continue
				if i <= self.__threadbound:
					main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
					main += "         if (__cs_active_thread[%s]) {\n" % (i)
					main += "             __cs_pc_cs = klee_range(__cs_pc[%s], %s, \"__cs_pc_cs\");\n" % (i, self.__lines[t] + 1)
					main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
					main += "             __cs_pc[%s] = __cs_pc_cs;\n" % (i)
					main += "         }\n\n"
					i += 1


		''' Last called to main
		'''

		# For the last call to main thread
		main += "           if (__cs_active_thread[0] == 1) {\n"
		main += "             __cs_pc_cs = klee_range(__cs_pc[0], %s, \"__cs_pc_cs\");\n" % (self.__lines['main'] + 1)
		main += "             main_thread();\n"
		main += "           }\n"
		main += "    return 0;\n"
		main += "}\n\n"

		return main

	def __createMainKLEERoundRobin(self, ROUNDS):
		'''  New main driver:
		'''
		main = ''
		main += "int main(void) {\n"

		''' First round (round 0)
		'''
		round = 0
		# Main thread
		main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
		main += "__CSEQ_rawline(\"    /* main */\");\n"
		main += "          __cs_pc_cs[0] = klee_range(1, %s, \"__cs_pc_cs[0]\");\n" % (self.__lines['main'] + 1)
		main += "          main_thread();\n"
		main += "          __cs_pc[0] = __cs_pc_cs[0];\n"
		main += "\n"
		# Other threads
		i = 1
		for t in self.__threadName:
			if t == 'main': continue
			if i <= self.__threadbound:
				main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
				main += "         if (__cs_active_thread[%s]) {\n" % (i)
				main += "             __cs_pc_cs[%s] = klee_range(0, %s, \"__cs_pc_cs[%s]\");\n" % (i, self.__lines[t] + 1, i)
				main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
				main += "             __cs_pc[%s] = __cs_pc_cs[%s];\n" % (i, i)
				main += "         }\n\n"
				i += 1

		''' Other rounds
		'''
		for round in range(1, ROUNDS):
			main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
			# For main thread
			main += "__CSEQ_rawline(\"    /* main */\");\n"
			main += "          if (__cs_active_thread[0]) {\n"
			main += "             __cs_pc_cs[0] = klee_range(__cs_pc[0], %s, \"__cs_pc_cs[0]\");\n" % (self.__lines['main'] + 1)
			main += "             main_thread();\n"
			main += "             __cs_pc[0] = __cs_pc_cs[0];\n"
			main += "          }\n\n"
			main += "\n"
			# For other threads
			i = 1
			for t in self.__threadName:
				if t == 'main': continue
				if i <= self.__threadbound:
					main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
					main += "         if (__cs_active_thread[%s]) {\n" % (i)
					main += "             __cs_pc_cs[%s] = klee_range(__cs_pc[%s], %s, \"__cs_pc_cs[%s]\");\n" % (i, i, self.__lines[t] + 1, i)
					main += "             %s(__cs_threadargs[%s]);\n" % (t, i)
					main += "             __cs_pc[%s] = __cs_pc_cs[%s];\n" % (i, i)
					main += "         }\n\n"
					i += 1


		''' Last called to main
		'''

		# For the last call to main thread
		main += "           if (__cs_active_thread[0] == 1) {\n"
		main += "             __cs_pc_cs[0] = klee_range(__cs_pc[0], %s, \"__cs_pc_cs[0]\");\n" % (self.__lines['main'] + 1)
		main += "             main_thread();\n"
		main += "           }\n"
		main += "    return 0;\n"
		main += "}\n\n"

		return main

	# Checks whether variable  v  from function  f  is a pointer.
	def __isPointer(self, f, v):
		if self.__donotcheckpointer: return False
		if v in self.Parser.varNames[f] and self.Parser.varType[f,v].endswith('*'): return True
		elif v in self.Parser.varNames[''] and self.Parser.varType['',v].endswith('*'): return True
		else: return False

	# Checks whether variable  v  from function  f  is global.
	def __isGlobal(self, f, v):
		if (v in self.Parser.varNames[''] and v not in self.Parser.varNames[f]): return True
		else: return False

	# Check whether the given AST node accesses global memory or uses a pointer.
	#
	# TODO: this overapproximation is very rough,
	#      (variable dependency, pointer analysis etc,
	#       could be useful for refinement)
	#
	def __globalAccess(self, stmt):
		if self.__atomic: return False  # if between atomic_begin() and atomic_end() calls no context switchs needed..

		oldStmtCount = self.__stmtCount             # backup counters
		oldMaxInCompound = self.__maxInCompound
		oldGlobalMemoryAccessed = self.__globalMemoryAccessed

		globalAccess = False
		self.__globalMemoryAccessed = False

		if type(stmt) not in (pycparser.c_ast.If, ):
			tmp = self._generate_stmt(stmt)
		else:
			tmp = self._generate_stmt(stmt.cond)

		globalAccess = self.__globalMemoryAccessed

		self.__stmtCount = oldStmtCount             # restore counters
		self.__maxInCompound = oldMaxInCompound
		self.__globalMemoryAccessed = oldGlobalMemoryAccessed

		return globalAccess
	
	#DR overriding built on the POR version
	def visit_Assignment(self, n):
		old_visitingLPart = self.__visitingLPart 
		self.__visitingLPart = True
		lvalue = self.visit(n.lvalue)
		#if lvalue == 'turn': n.show()
		if self.__visitingCE:  #added to handle conditional expressions
			if self.__laddress != '' and self.__laddress not in self.__CEwriteVars:
				self.__CEadditionalSetFields += 'if(%s) __CPROVER_set_field(%s,"dr_write",1);\n' % (self.__conditionCE, self.__laddress)  
				self.__CEwriteVars.append(self.__laddress)
		elif self.__laddress != '' and self.__laddress not in self.__sharedVarsW:
			self.__sharedVarsW.append(self.__laddress)

		self.__visitingLPart = False  #S: added on March 2, 2021
		rvalue = self.visit(n.rvalue)

		if self.__dr_additionalCondition == "1":   #DR
			self.__dr_additionalCondition = lvalue + ' != ' + rvalue   #DR
		else:    #DR
			self.__dr_additionalCondition += ' | ' + lvalue + ' != ' + rvalue   #DR
		#print self.__sharedVarsW
		self.__laddress = ''
		self.__visitingLPart = old_visitingLPart
		ret = '%s %s %s' % (lvalue, n.op, rvalue)
		return ret

	def visit_UnaryOp(self, n):
		if n.op == '&':         #POR
			self.__inReference = True  #POR
		operand = self._parenthesize_unless_simple(n.expr)
		ret = '%s%s' % (n.op, operand)
		if n.op == '&':         #POR
			self.__inReference = False  #POR
			return ret
		elif n.op == "*":
			if self.__visitingLPart == True:
				self.__laddress = operand
			if self.__visitingCE: #DR 
				if not self.__inReference and operand not in self.__sharedVarsR and operand not in  self.__laddress and operand not in self.__CEreadVars:  #DR
					if self.__CEadditionalCondition != '': self.__CEadditionalCondition +=' ||'
					self.__CEadditionalCondition +='( %s && __CPROVER_get_field(%s,"dr_write"))' % (self.__conditionCE, operand)    #DR
					self.__CEreadVars.append(operand)
			elif operand not in self.__sharedVarsR and self.__visitingLPart == False: 
				   self.__sharedVarsW.append(operand)
			return ret
		elif n.op == "++" or n.op == "--" or n.op == "p++" or n.op == "p--": #S: added on March 2, 2021
			if '&'+operand not in self.__sharedVarsW:    #S: added on March 2, 2021
				self.__sharedVarsW.append('&'+operand)   #S: added on March 2, 2021
			return super(self.__class__, self).visit_UnaryOp(n)
		else:
			return super(self.__class__, self).visit_UnaryOp(n) 


#DR added to handle properly conditional expressions

	def visit_TernaryOp(self, n):
		oldConditionCE = self.__conditionCE

		oldVisitingCE = self.__visitingCE
		self.__CEreadVars=[]
		self.__CEwriteVars=[]
		self.__visitingCE = True

		s = self._visit_expr(n.cond)
		if self.__conditionCE != '':
		   self.__conditionCE =  '( ' + self.__conditionCE + ' && (' + s + ') )'
		else: 
		   self.__conditionCE = '(' + s + ')'

		s  +=  ' ? '
		
		self.__CEreadVars=[]
		self.__CEwriteVars=[]
		s += '(' + self._visit_expr(n.iftrue) + ') : '

		self.__CEreadVars=[]
		self.__CEwriteVars=[]
		self.__conditionCE = '!( %s)'% self.__conditionCE
		s += '(' + self._visit_expr(n.iffalse) + ')'

		self.__visitingCE = oldVisitingCE
		self.__conditionCE = oldConditionCE

		return s