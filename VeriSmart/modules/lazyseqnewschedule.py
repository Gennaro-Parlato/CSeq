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
	- all loops should have been unrolled
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
	__compulsoryVP = {}              # compulsory visible points for each thread
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
	__stmtVPCompulsory = 0           # number of compulsory visible points

	__currentThread = ''             # name of the current thread (also used to build thread labels)

	__threadbound = 0             	# bound on the number of threads

	__firstThreadCreate = False      # set once the first thread creation is met
	__globalMemoryAccessed = False   # used to limit context-switch points (when global memory is not accessed, no need to insert them)
	__globalMemoryTest = False       # set to True when visiting AST when running method __globalAccess 

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

	__inReference = False            # True iff within & scope
	expList = []     #assigned with  the list of the expressions of an ExprList node
	__enableDR = False
	isSeqCode = False # GG: sequential code, i.e., no main driver, main function stays the same, no visible points, no program counter...

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
		self.addOutputParam('compulsoryVPs')
		self.addOutputParam('threadNames')
		self.addOutputParam('threadIndex')

	def initHeaderSwarm(env):
                 return core.utils.printFile('modules/lazyseqBnewschedule.c').replace('<insert-threadsizes-here>',"$THREADSIZE")

	#@staticmethod
	def initHeader(env,lines):
                 return core.utils.printFile('modules/lazyseqBnewschedule.c').replace('<insert-threadsizes-here>', lines)

	def additionalDefs(self):
            return ''

	def initFlags(self,count):
            return
 
	def loadfromstring(self, string, env):
		self.__enableDR = env.enableDR
		
		if self.getInputParamValue('deadlock') is not None:
			self._deadlockcheck = True

        
		threads = int(self.getInputParamValue('threads'))
		#print(threads)
		self.isSeqCode = threads == 0
		self.setOutputParam('isSeqCode', self.isSeqCode)
		rounds = env.rounds  #int(self.getInputParamValue('rounds'))
		backend = self.getInputParamValue('backend')

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

		super(lazyseqnewschedule, self).loadfromstring(string, env)
		if backend == 'cbmc' or backend is None:
			self.__extra_nondet = ''

		if self.isSeqCode:
			header = core.utils.printFile('modules/lazyseqBnewschedule_seqcode.c')
			self.setOutputParam('header', header)
		else:
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
					    #print(self.__class__)
					    #print(self.output)
					    #mainFunc=self.__createMainRoundRobin(rounds)
					    #print(mainFunc)
					    #sys.exit(0)
					    self.output += self.createMainRoundRobin(rounds)    #name changed form __createMainRoundRobin since this would not ovverride
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
				    if env.isSwarm:
					    header = lazyseqnewschedule.initHeaderSwarm(env)
				    else: 
					    header = lazyseqnewschedule.initHeader(env,lines)
			    else:
				    header = core.utils.printFile('modules/lazyseqBdeadlocknewschedule.c').replace('<insert-threadsizes-here>',lines)
			    header = header.replace('<insert-numthreads-here>', str(threads+1))

		    header += self.additionalDefs()	

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
		    self.setOutputParam('compulsoryVPs',self.__compulsoryVP)
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

	def additionalCode(self,threadIndex):
		return ''
	def alternateCode(self, n):
		return super(lazyseqnewschedule, self).visit(n)

	def needs_compulsory_visible_point(self, n):
		return type(n) == pycparser.c_ast.FuncCall and n.name.name in (core.common.changeID['pthread_join'],core.common.changeID['pthread_create'])

	def visit_Compound(self, n):
		compoundList = ["{\n"]
		# Insert the labels at the beginning of each statement,
		# with a few exclusions to reduce context-switch points...

		if n.block_items:
			for stmt in n.block_items:

				self.initFlags(self.__stmtCount)
				# Case 1: last statement in a thread (must correspond to last label)
				if type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == core.common.changeID['pthread_exit']: ##if type(stmt) == pycparser.c_ast.FuncCall and self._parenthesize_unless_simple(stmt.name) == core.common.changeID['pthread_exit']:
					self.__stmtCount += 1
					self.__maxInCompound = self.__stmtCount
					code = '@£@F ' + self.visit(stmt) + ';\n'
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
						s = self.visit(stmt.stmt)
						code = '@£@I1' + self.additionalCode(threadIndex) + '@£@I2' + s + '@£@I3' + self.alternateCode(stmt.stmt) + '@£@I4' + ';\n' 
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
#@@@@		code = self.visit(stmt)
						threadIndex = self.Parser.threadOccurenceIndex[self.__currentThread]
						s = self.visit(stmt.stmt)
						code = '@£@I1' + self.additionalCode(threadIndex) + '@£@I2' + s + '@£@I3' + self.alternateCode(stmt.stmt) + '@£@I4' + ';\n'
					else:
						code = self.visit(stmt.stmt) + ';\n'

					guard = ''
					if not self.__atomic:
						guard = '@£@G'
					code = self._make_indent() + stmt.name + ': ' + guard + code + '\n'
					compoundList.append(code)
				elif type(stmt) is pycparser.c_ast.Compound:
					code = self.visit(stmt) + ";\n"
					compoundList.append(code)
				# Case 3: all the rest....
				elif (type(stmt) not in (pycparser.c_ast.Compound, pycparser.c_ast.Goto, pycparser.c_ast.Decl)
					and not (self.__currentThread=='main' and not self.__enableDR and self.__firstThreadCreate == False) # and not running with datarace --dr => False
					or (self.__currentThread=='main' and self.__stmtCount == -1)) :

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
						s =  self.visit(stmt)
						code = '@£@I1' + self.additionalCode(threadIndex)+ '@£@I2' + s + '@£@I3' + self.alternateCode(stmt) + '@£@I4' + ';\n'
					elif not self.__visit_funcReference and (
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
						):
						is_compulsory_vp = self.needs_compulsory_visible_point(stmt)
						if is_compulsory_vp:
							self.__stmtVPCompulsory += 1
						self.__stmtCount += 1
						self.__maxInCompound = self.__stmtCount
						threadIndex = self.Parser.threadOccurenceIndex[self.__currentThread]
						s = self.visit(stmt)
						prefix = '@£@J1' if is_compulsory_vp else '@£@I1'
						code = prefix + self.additionalCode(threadIndex) + '@£@I2' + s + '@£@I3' + self.alternateCode(stmt) + '@£@I4' + ';\n'
	
					else:
						code = self.visit(stmt) + ";\n"
					compoundList.append(code)
				else:
					code = self.visit(stmt) + ";\n"
					compoundList.append(code)
		compoundList[len(compoundList)-1] = compoundList[len(compoundList)-1] + '\n}'
		listToStr = ''.join(stmt for stmt in compoundList)
		return listToStr

	def insertGlobalVarInit(self, s):
		return s

	def insertFieldDecl(self, s):
		return s

	def visit_FuncDef(self, n):
		if (n.decl.name.startswith('__CSEQ_atomic_') or
			self.isSeqCode or #no need for vps if sequential
			#n.decl.name.startswith(core.common.funcPrefixChange['__CSEQ_atomic']) or
			n.decl.name == '__CSEQ_assert' or
			n.decl.name in self.Parser.funcReferenced ):   # <--- functions called through pointers are not inlined yet
			# return self.Parser.funcBlock[n.decl.name]
			self.__currentThread = n.decl.name
			self.__visit_funcReference = True
			#ret = self.otherparser.visit(n)
			oldatomic = self.__atomic
			self.__atomic = True
			if self.isSeqCode and n.decl.name == "main" and hasattr(self, 'any_instrument') and self.any_instrument:
				body = self.visit(n.body)
				s = 'int main(void) { \n' + body + '}\n'
				s = self.insertFieldDecl(self.insertGlobalVarInit(s))
			else:
				decl = self.visit(n.decl)
				body = self.visit(n.body)
				s = decl + '\n' + body + '\n'
			self.__atomic = oldatomic
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
		self.__compulsoryVP[self.__currentThread] = self.__stmtVPCompulsory
		###print "THREAD %s, LINES %s \n\n" % (self._currentThread, self.__lines)

		#
		self.__stmtCount = -1
		self.__stmtVPCompulsory = 0
		if n.param_decls:
			knrdecls = ';\n'.join(self.visit(p) for p in n.param_decls)
			#body = body[:body.rfind('}')] + self._make_indent() + returnStmt + '\n}'
			f = decl + '\n' + knrdecls + ';\n'
		else:
			#body = body[:body.rfind('}')] + self._make_indent() + returnStmt + '\n}'
			f = decl + '\n'

		# Remove arguments (if any) for main() and transform them into local variables in main_thread.
		# TODO re-implement seriously.
		if self.__currentThread == 'main':
			main_fnc_name = "main" if self.isSeqCode else "main_thread"
			f = '%s %s(void)\n' % (self.Parser.funcBlockOut[
				self.__currentThread], main_fnc_name)
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
		
		if_header = 'if ('

		if n.cond:
			condition = self.visit(n.cond)
			if_header += condition

		if_header += ')\n'
		
		lbl_pre_then = self.__maxInCompound
		thenBlock = self._generate_stmt(n.iftrue, add_indent=True)
		lbl_post_then = self.__maxInCompound
		ifEnd = self.__maxInCompound   # label for the last stmt in the if block:  if () { block; }
		nextLabelID = ifEnd+1
		
		lbl_pre_else = self.__maxInCompound
		if n.iffalse:
			elseBlock = self._generate_stmt(n.iffalse, add_indent=True)
			elseEnd = self.__maxInCompound   # label for the last stmt in the if_false block if () {...} else { block; }
		lbl_post_else = self.__maxInCompound	
		
		vpThen = lbl_pre_then < lbl_post_then
		vpElse = lbl_pre_else < lbl_post_else
		
		if vpThen or vpElse:
		    if_header = '@£@Q' + if_header # VP jump ends after condition evaluation. To avoid spoiling the guard simplification algorithm, use the if structure to enter the relevant branch
		    thenBlock = thenBlock.replace('{', '{@£@H\n', 1) #jump to the first label in the branch
		    thenBlock = "@£@Q;}".join(thenBlock.rsplit('}', 1)) #put the label at the end of the branch -> avoids jumping into the else branch. Weird code because there isn't the rreplace function
		    
		
		s = if_header
		s += thenBlock
		
		
		
		
		

		

		#lbl_pre_else = self.__maxInCompound
		if n.iffalse:
			#elseBlock = self._generate_stmt(n.iffalse, add_indent=True)

			#elseEnd = self.__maxInCompound   # label for the last stmt in the if_false block if () {...} else { block; }

			if ifStart < ifEnd:
				#threadIndex = self.Parser.threadIndex[self.__currentThread] if self.__currentThread in self.Parser.threadIndex else 0
				# GUARD(%s,%s)
				if not self.__visit_funcReference:
					# elseHeader = '@G' + str(ifEnd+1) + ' '
					elseHeader = '@£@G '
					# if self.__decomposepc:
						## elseHeader = '__CSEQ_assume( __cs_pc_cs_%s >= %s );' % (threadIndex, str(ifEnd+1))
						# elseHeader = '__CSEQ_rawline(@G__cs_pc_cs_%s >= $$);\n' % (threadIndex)
					# elif self.__one_pc_cs:
						## elseHeader = '__CSEQ_assume( __cs_pc_cs >= %s );' % (str(ifEnd+1))
						# elseHeader = '__CSEQ_rawline(@G__cs_pc_cs_ >= $$);\n'
					# else:
						## elseHeader = '__CSEQ_assume( __cs_pc_cs[%s] >= %s );' % (threadIndex, str(ifEnd+1))
						# elseHeader = '__CSEQ_rawline(@G__cs_pc_cs_[%s] >= $$);\n' % (threadIndex)
						## elseHeader = (guard.replace('$$',str(self.__stmtCount+1))

			else:
				elseHeader = ''
			
			if vpThen or vpElse:
			    elseHeader += '\n@£@H '

			nextLabelID = elseEnd+1
			s += self._make_indent() + 'else\n'

			elseBlock = elseBlock.replace('{', '{ '+elseHeader, 1)
			if vpThen or vpElse:
			    elseBlock = "@£@Q;}".join(elseBlock.rsplit('}', 1))
			s += elseBlock

		header = ''

		if ifStart+1 < nextLabelID:
			#threadIndex = self.Parser.threadIndex[self.__currentThread] if self.__currentThread in self.Parser.threadIndex else 0
			# GUARD(%s,%s)
			if not self.__visit_funcReference:
				# footer = '@G' + str(nextLabelID) + ' '
				footer = '@£@G' + ' '
				#if self.__decomposepc:
					## footer = '__CSEQ_assume( __cs_pc_cs_%s >= %s );' % (threadIndex, nextLabelID)
					#footer = '__CSEQ_rawline(@G__cs_pc_cs_%s >= $$);\n' % (threadIndex)
				#elif self.__one_pc_cs:
					## footer = '__CSEQ_assume( __cs_pc_cs >= %s );' % (nextLabelID)
					#footer = '__CSEQ_rawline(@G__cs_pc_cs_ >= $$);\n'
				#else:
					## footer = '__CSEQ_assume( __cs_pc_cs[%s] >= %s );' % (threadIndex, nextLabelID)
					#footer = '__CSEQ_rawline(@G__cs_pc_cs_[%s] >= $$);\n' % (threadIndex)

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

	def fixArrayIndex(self,s):
		threadIndex = self.Parser.threadOccurenceIndex[self.__currentThread] if self.__currentThread in self.Parser.threadOccurenceIndex else 0 # 17 March 2021
		if s == '__cs_thread_index' and self.__currentThread != '':
			s = '%s' % threadIndex
		return s             

	def visit_ArrayRef(self, n):
		arrref = self._parenthesize_unless_simple(n.name)
		subscript = self.visit(n.subscript)
		#threadIndex = self.Parser.threadIndex[self.__currentThread] if self.__currentThread in self.Parser.threadIndex else 0
		subscript = self.fixArrayIndex(subscript)
		s = arrref + '[' + subscript + ']'
		return s

	def foo(self):
		return 0	

	def visit_ID(self, n):
		# If this ID corresponds either to a global variable,
		# or to a pointer...
		#
		if ((self._isGlobal(self.__currentThread, n.name) or self._isPointer(self.__currentThread, n.name)) and not
			n.name.startswith('__cz_thread_local_')):
			#print "variable %s in %s is global\n" % (n.name, self.__currentThread)
			self.__globalMemoryAccessed = True

		# Rename the IDs of main() arguments
		#if self._currentThread == 'main' and n.name in self.Parser.varNames['main'] and self.Parser.varKind['main',n.name] == 'p':
		#   return '__main_params_' + n.name

		return n.name

	def frefVisit(self,n):
		return self._parenthesize_unless_simple(n.name)

	def addRetFuncCall(self,fname,args,tindex=None):
		pass

	def visit_FuncCall(self, n):
		fref = self.frefVisit(n)

		args = self.visit(n.args)
		#print("FREF: " + fref)
		#if fref == '__cs_safe_malloc': 
		#	print("ARGS: " + args)
		#	n.show()
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
			#n.show()
			#print(fref + '\n' + str(self.expList))
			#sys.exit(0)
#			fName = args[:args.rfind(',')]
#			fName = fName[fName.rfind(',')+2:]
#			fName = fName.replace('&', '')
			fName = self.expList[2]
			fName = fName.strip()
			fName = fName.strip('()&')
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
			threadIndex = self.Parser.threadOccurenceIndex[self.__currentThread] if self.__currentThread in self.Parser.threadOccurenceIndex else 0
			self.addRetFuncCall(fref,args,threadIndex)
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
			self.addRetFuncCall(fref,args,threadIndex)
			return fref + '(' + args + ', %s)' % threadIndex

		#S: fake implementation of pthread_key_create
		#   it is replaced with  __cs_key_create and last argument (the destroyer function pointer) is removed
		#   the body of __cs_key_create differs from that of pthread_key_create in that the
		#   storing of the detroyer function is removed

		if (fref == core.common.changeID['pthread_key_create'] ):
			#print (fref + '(' + args + ')')
			args = args[:args.rfind(',')]
			#print (fref + '(' + args + ')')

#		if fref == core.common.changeID['pthread_create']: # TODO re-write AST-based (see other modules)
#			self.addRetFuncCall(fref,args, self.Parser.threadOccurenceIndex[fName])
#		else:
		self.addRetFuncCall(fref,args)
		#ret = fref + '(' + args + ')'
		#print("GMT: " + str(self.getGlobalMemoryTest() ))
		#print(ret)
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
				main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
					main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
				main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
					main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
				main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
					main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
				main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
					main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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

	def createMainRoundRobin(self, ROUNDS):  #name changed from __createMainRoundRobin since this would not ovverride
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
		cs_pc_cs_size = max(self._bitwidth.values()) + 1
		
		bw_tMain_r0 = self._bitwidth[('main', "__cs_tmp_t%s_r0"%(self.Parser.threadOccurenceIndex['main']))]
		main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
		main += "__CSEQ_rawline(\"    /* main */\");\n"
		#caledem
		main += "__cs_active_thread[%s] = 1;\n" % self.Parser.threadOccurenceIndex['main']
		main += "          unsigned int __cs_tmp_t%s_r0 %s;\n" % (self.Parser.threadOccurenceIndex['main'], self.__extra_nondet)
		main += "          __CPROVER_assign_bits(__cs_tmp_t%s_r0, &__cs_pc_cs[%s], %d);\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], bw_tMain_r0)
		main += "          __CSEQ_assume(__CPROVER_ugt_bits(__cs_pc_cs[%s], 0, %d));\n" % (self.Parser.threadOccurenceIndex['main'], bw_tMain_r0)
		main += "          __CSEQ_assume(__CPROVER_ule_bits(__cs_pc_cs[%s], %s, %d));\n" % (self.Parser.threadOccurenceIndex['main'], "@£@ML" + str(self.Parser.threadOccurenceIndex['main']), bw_tMain_r0)
		main += "          main_thread();\n"
		main += "          __CPROVER_assign_bits(__cs_pc_cs[%s], &__cs_pc[%s], %d);\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], bw_tMain_r0)
		main += "\n"
		# Other threads
		i = 0
		for t in self.__threadName:
			if t == 'main': continue
			if i <= self.__threadbound:
				bw_ti_r0 = self._bitwidth[('main', "__cs_tmp_t%s_r0"%(i))]
				main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
				main += "         unsigned int __cs_tmp_t%s_r0 %s;\n" % (i, self.__extra_nondet)
				main += "         if (__cs_active_thread[%s]) {\n" % (i)
				main += "             __CPROVER_assign_bits(__cs_tmp_t%s_r0, &__cs_pc_cs[%s], %d);\n" % (i, i, bw_ti_r0)
				main += "             __CSEQ_assume(__CPROVER_ule_bits(__cs_pc_cs[%s], %s, %d));\n" % (i, "@£@ML" + str(self.Parser.threadOccurenceIndex[t]), bw_ti_r0)
				main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
				main += "             __CPROVER_assign_bits(__cs_pc_cs[%s], &__cs_pc[%s], %d);\n" % (i, i, bw_ti_r0)
				main += "         }\n\n"
				i += 1

		''' Other rounds
		'''
		for round in range(1, ROUNDS):
			bw_tMain_rnd = self._bitwidth[('main', "__cs_tmp_t%s_r%s"%(self.Parser.threadOccurenceIndex['main'], round))]
			main += "__CSEQ_rawline(\"/* round  %s */\");\n" % round
			# For main thread
			main += "__CSEQ_rawline(\"    /* main */\");\n"
			main += "          unsigned int __cs_tmp_t%s_r%s %s;\n" % (self.Parser.threadOccurenceIndex['main'], round, self.__extra_nondet)
			main += "          if (__cs_active_thread[%s]) {\n" % self.Parser.threadOccurenceIndex['main']
			if self.__guess_cs_only:
				main += "             __CPROVER_assign_bits(__cs_tmp_t%s_r%s, &__cs_pc_cs[%s], %d);\n" % (self.Parser.threadOccurenceIndex['main'], round, self.Parser.threadOccurenceIndex['main'], bw_tMain_rnd)
				cmp_bits_tMain_rnd = bw_tMain_rnd
			else:
				main += "              __CPROVER_add_bits(__cs_pc[%s], __cs_tmp_t%s_r%s, &__cs_pc_cs[%s], %d);\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], round, self.Parser.threadOccurenceIndex['main'], bw_tMain_rnd + 1)
				cmp_bits_tMain_rnd = bw_tMain_rnd + 1
			main += "             __CSEQ_assume(__CPROVER_uge_bits(__cs_pc_cs[%s], __cs_pc[%s], %d));\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], cmp_bits_tMain_rnd)
			main += "             __CSEQ_assume(__CPROVER_ule_bits(__cs_pc_cs[%s], %s, %d));\n" % (self.Parser.threadOccurenceIndex['main'], "@£@ML" + str(self.Parser.threadOccurenceIndex['main']), cmp_bits_tMain_rnd)
			main += "             main_thread();\n"
			main += "             __CPROVER_assign_bits(__cs_pc_cs[%s], &__cs_pc[%s], %d);\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], bw_tMain_rnd)
			main += "          }\n\n"
			main += "\n"
			# For other threads
			i = 0
			for t in self.__threadName:
				if t == 'main': continue
				if i <= self.__threadbound:
					bw_ti_rnd = self._bitwidth[('main', "__cs_tmp_t%s_r%s"%(i, round))]
					main += "__CSEQ_rawline(\"    /* %s */\");\n" % t
					main += "         unsigned int __cs_tmp_t%s_r%s %s;\n" % (i, round, self.__extra_nondet)
					main += "         if (__cs_active_thread[%s]) {\n" % (i)
					if self.__guess_cs_only:
						main += "             __CPROVER_assign_bits(__cs_tmp_t%s_r%s, &__cs_pc_cs[%s], %d);\n" % (i, round, i, bw_ti_rnd)
						cmp_bits_ti_rnd = bw_ti_rnd
					else:
						main += "             __CPROVER_add_bits(__cs_pc[%s], __cs_tmp_t%s_r%s, &__cs_pc_cs[%s], %d);\n" % (i, i, round, i, bw_ti_rnd + 1)
						cmp_bits_ti_rnd = bw_ti_rnd + 1
					main += "             __CSEQ_assume(__CPROVER_uge_bits(__cs_pc_cs[%s], __cs_pc[%s], %d));\n" % (i, i, cmp_bits_ti_rnd)
					main += "             __CSEQ_assume(__CPROVER_ule_bits(__cs_pc_cs[%s], %s, %d));\n" % (i, "@£@ML" + str(self.Parser.threadOccurenceIndex[t]), cmp_bits_ti_rnd)
					main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
					main += "             __CPROVER_assign_bits(__cs_pc_cs[%s], &__cs_pc[%s], %d);\n" % (i, i, bw_ti_rnd)
					main += "         }\n\n"
					i += 1


		''' Last called to main
		'''

		# For the last call to main thread
		k = int(math.floor(math.log(self.__lines['main'],2)))+1
		main += "          unsigned int __cs_tmp_t%s_r%s %s;\n" % (self.Parser.threadOccurenceIndex['main'], ROUNDS, self.__extra_nondet)
		self._bitwidth['main','__cs_tmp_t%s_r%s' % (self.Parser.threadOccurenceIndex['main'], ROUNDS)] = k
		bw_tMain_rlast = k
		main += "           if (__cs_active_thread[%s] == 1) {\n" % self.Parser.threadOccurenceIndex['main']
		if self.__guess_cs_only:
			main += "             __CPROVER_assign_bits(__cs_tmp_t%s_r%s, &__cs_pc_cs[%s], %d);\n" % (self.Parser.threadOccurenceIndex['main'], ROUNDS, self.Parser.threadOccurenceIndex['main'], bw_tMain_rlast)
			cmp_bits_tMain_rlast = bw_tMain_rlast
		else:
			main += "             __CPROVER_add_bits(__cs_pc[%s], __cs_tmp_t%s_r%s, &__cs_pc_cs[%s], %d);\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], ROUNDS, self.Parser.threadOccurenceIndex['main'], bw_tMain_rlast+1)
			cmp_bits_tMain_rlast = bw_tMain_rlast + 1
		main += "             __CSEQ_assume(__CPROVER_uge_bits(__cs_pc_cs[%s], __cs_pc[%s], %d));\n" % (self.Parser.threadOccurenceIndex['main'], self.Parser.threadOccurenceIndex['main'], cmp_bits_tMain_rlast)
		main += "             __CSEQ_assume(__CPROVER_ule_bits(__cs_pc_cs[%s], %s, %d));\n" % (self.Parser.threadOccurenceIndex['main'], "@£@ML" + str(self.Parser.threadOccurenceIndex['main']), cmp_bits_tMain_rlast)
		main += "             main_thread();\n"
		main += "           }\n"
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
		main += "          __CSEQ_assume(__cs_pc_cs[0] <= %s);\n" % "@£@MLM"
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
				main += "             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (i, "@£@ML" + str(self.Parser.threadOccurenceIndex[t]))
				main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
			main += "             __CSEQ_assume(__cs_pc_cs[0] <= %s);\n" % "@£@MLM"
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
					main += "             __CSEQ_assume(__cs_pc_cs[%s] <= %s);\n" % (i,"@£@ML" + str(self.Parser.threadOccurenceIndex[t]))
					main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
		main += "             __CSEQ_assume(__cs_pc_cs[0] <= %s);\n" % "@£@MLM"
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
				main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
					main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
				main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
					main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
				main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
					main += "             %s(__cz_threadargs[%s]);\n" % (t, i)
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
	def _isPointer(self, f, v):
		if self.__donotcheckpointer: return False
		if v in self.Parser.varNames[f] and self.Parser.varType[f,v].endswith('*'): return True
		elif v in self.Parser.varNames[''] and self.Parser.varType['',v].endswith('*'): return True
		else: return False

	# Checks whether variable  v  from function  f  is global.
	def _isGlobal(self, f, v):
		if (v in self.Parser.varNames[''] and v not in self.Parser.varNames[f]): return True
		else: return False
	#	return False

	# Check whether the given AST node accesses global memory or uses a pointer.
	#
	# TODO: this overapproximation is very rough,
	#      (variable dependency, pointer analysis etc,
	#       could be useful for refinement)
	#
	def __globalAccess(self, stmt):
		old_gmt = self.__globalMemoryTest 
		self.__globalMemoryTest = True

		if self.__atomic: 
			self.__globalMemoryTest = old_gmt
			return False  # if between atomic_begin() and atomic_end() calls no context switchs needed..

		oldStmtCount = self.__stmtCount             # backup counters
		oldStmtVPCompulsory = self.__stmtVPCompulsory
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
		self.__stmtVPCompulsory = oldStmtVPCompulsory
		self.__maxInCompound = oldMaxInCompound
		self.__globalMemoryAccessed = oldGlobalMemoryAccessed
		
		self.__globalMemoryTest = old_gmt
		return globalAccess


	def visit_ExprList(self, n):
		visited_subexprs = []
		for expr in n.exprs:
			visited_subexprs.append(self._visit_expr(expr))
		self.expList = visited_subexprs.copy()
		return ', '.join(visited_subexprs)


# access methods
	def getThreadbound(self):
		return self.__threadbound

	def getLines(self):
		return self.__lines

	def getThreadName(self):
		return self.__threadName

	def getCurrentThreadIndex(self):
		return  self.Parser.threadOccurenceIndex[self.__currentThread]

	def getExtra_nondet(self):
		return self.__extra_nondet

	def setExpList(self,list):
		self.expList = list.copy()

	def getGlobalMemoryTest(self):
		return self.__globalMemoryTest

	def getCurrentThread(self):
		return self.__currentThread
	
	def getGuessCsOnly(self):
		return self.__guess_cs_only
	
# predicate methods
	def isThread(self,name):
		return (name == 'main' or name in self.Parser.threadName)
	def isAtomic(self):
		return self.__atomic
