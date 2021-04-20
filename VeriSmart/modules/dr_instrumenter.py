""" CSeq backend instrumentation module
	written by Omar Inverso, Truc Nguyen Lam, University of Southampton.
	adapted to data race detection by translating CSEQ_assert added in the translation 
	to verifier-specific assume
"""
import os
import sys

from bin import utils

VERSION = 'instrumenter-0.1-2016.08.09'
# VERSION = 'instrumenter-0.0-2015.07.15'
# VERSION = 'instrumenter-0.0-2015.07.09'
#VERSION = 'instrumenter-0.0-2015.06.25'
"""
	Transformation 1 (convert function calls and add implementation):
		__CSEQ_assert()   -->   verifier-specific assume  (assert are removed for datarace detection) 
		__CSEQ_assume()   -->   verifier-specific assume

	Transformation 2 (convert bitvectors)
		convert any  int  or  unsigned int  for which there is
		__CSEQ_bitvector[k] --> ...

	Transformation 3 (raw line injections and indentation):
		__CSEQ_rawline("string"); --> string

		this transformation uses
		separate indentation for raw and non-raw lines, where
		a raw line is a line inserted by __CSEQ_rawline()
		any other line is non-raw.
		Raw line are indentend fully left,
		non-raw are shifted to the right.

TODO:
	- Add bitvector option to esbmc backend
	- Deal with typedef

Changelog:
	2017.04.07  add linearizability header
	2017.02.24  add smack backend
	2017.02.23  add UAutomizer backend
	2016.12.06  add fix to type not integer (long)
	2016.12.02  add round integer types options
	2016.11.30  add svcomp option (disable assertions in lock/unlock)
	2016.11.29  disable hashed file number
	2016.09.26  add option to get more (system) headers
	2016.09.14  add more entry to nondet, and extra header to CBMC
	2016.08.15  set bits for structure and array
	2016.08.09  add backend Frama-C
	2015.07.15  back to output.strip to remove fake header content

"""
from time import gmtime, strftime
import math, re
import core.module, core.utils, core.common
import pycparser.c_ast


_backends = ['cbmc', 'esbmc', 'llbmc', 'blitz', 'satabs',
			'2ls', 'klee', 'cpachecker', 'framac', 'uautomizer',
			'smack']

fmap = {}

fmap['cbmc', '__CSEQ_assume'] = '__CPROVER_assume'
fmap['cbmc', '__CSEQ_assertext'] = '__CPROVER_assume'
fmap['cbmc', '__CSEQ_assert'] = '__CPROVER_assume'
fmap['cbmc', '__CSEQ_nondet_int'] = 'nondet_int'
fmap['cbmc', '__CSEQ_nondet_uint'] = 'nondet_uint'
fmap['cbmc', '__CSEQ_nondet_bool'] = 'nondet_bool'
fmap['cbmc', '__CSEQ_nondet_char'] = 'nondet_char'
fmap['cbmc', '__CSEQ_nondet_uchar'] = 'nondet_uchar'

fmap['esbmc', '__CSEQ_assume'] = '__ESBMC_assume'
fmap['esbmc', '__CSEQ_assertext'] = '__ESBMC_assume'
fmap['esbmc', '__CSEQ_assert'] = '__ESBMC_assume'
fmap['esbmc', '__CSEQ_nondet_int'] = '__VERIFIER_nondet_int'
fmap['esbmc', '__CSEQ_nondet_uint'] = '__VERIFIER_nondet_uint'
fmap['esbmc', '__CSEQ_nondet_bool'] = '__VERIFIER_nondet_bool'
fmap['esbmc', '__CSEQ_nondet_char'] = '__VERIFIER_nondet_char'
fmap['esbmc', '__CSEQ_nondet_uchar'] = '__VERIFIER_nondet_uchar'

fmap['llbmc', '__CSEQ_assume'] = '__llbmc_assume'
fmap['llbmc', '__CSEQ_assertext'] = '__llbmc_assume'
fmap['llbmc', '__CSEQ_assert'] = '__llbmc_assume'
fmap['llbmc', '__CSEQ_nondet_int'] = 'nondet_int'
fmap['llbmc', '__CSEQ_nondet_uint'] = 'nondet_int'
fmap['llbmc', '__CSEQ_nondet_bool'] = 'nondet_bool'
fmap['llbmc', '__CSEQ_nondet_char'] = 'nondet_char'
fmap['llbmc', '__CSEQ_nondet_uchar'] = 'nondet_uchar'

fmap['blitz', '__CSEQ_assume'] = '__CPROVER_assume'
fmap['blitz', '__CSEQ_assertext'] = '__CPROVER_assume'
fmap['blitz', '__CSEQ_assert'] = '__CPROVER_assume'
fmap['blitz', '__CSEQ_nondet_int'] = 'nondet_int'
fmap['blitz', '__CSEQ_nondet_uint'] = 'nondet_uint'
fmap['blitz', '__CSEQ_nondet_bool'] = 'nondet_bool'
fmap['blitz', '__CSEQ_nondet_char'] = 'nondet_char'
fmap['blitz', '__CSEQ_nondet_uchar'] = 'nondet_uchar'

fmap['satabs', '__CSEQ_assume'] = '__CPROVER_assume'
fmap['satabs', '__CSEQ_assertext'] = '__CPROVER_assume'
fmap['satabs', '__CSEQ_assert'] = '__CPROVER_assume'
fmap['satabs', '__CSEQ_nondet_int'] = 'nondet_int'
fmap['satabs', '__CSEQ_nondet_uint'] = 'nondet_uint'
fmap['satabs', '__CSEQ_nondet_bool'] = 'nondet_bool'
fmap['satabs', '__CSEQ_nondet_char'] = 'nondet_char'
fmap['satabs', '__CSEQ_nondet_uchar'] = 'nondet_uchar'

# fmap['2ls', '__CSEQ_assume'] = '__CPROVER_assume'
# fmap['2ls', '__CSEQ_assertext'] = 'assert'
# fmap['2ls', '__CSEQ_assert'] = 'assert'
# fmap['2ls', '__CSEQ_nondet_int'] = 'nondet_int'
# fmap['2ls', '__CSEQ_nondet_uint'] = 'nondet_uint'

fmap['klee', '__CSEQ_assume'] = 'KLEE_assume'
fmap['klee', '__CSEQ_assertext'] = 'KLEE_assume'
fmap['klee', '__CSEQ_assert'] = 'KLEE_assume'
fmap['klee', '__CSEQ_nondet_int'] = 'KLEE_nondet_int'
fmap['klee', '__CSEQ_nondet_uint'] = 'KLEE_nondet_uint'
fmap['klee', '__CSEQ_nondet_bool'] = 'KLEE_nondet_bool'
fmap['klee', '__CSEQ_nondet_char'] = 'KLEE_nondet_char'
fmap['klee', '__CSEQ_nondet_uchar'] = 'KLEE_nondet_uchar'

fmap['cpachecker', '__CSEQ_assume'] = '__VERIFIER_assume'
fmap['cpachecker', '__CSEQ_assertext'] = '__VERIFIER_assume'
fmap['cpachecker', '__CSEQ_assert'] = '__VERIFIER_assume'
fmap['cpachecker', '__CSEQ_nondet_int'] = '__VERIFIER_nondet_int'
fmap['cpachecker', '__CSEQ_nondet_uint'] = '__VERIFIER_nondet_uint'
fmap['cpachecker', '__CSEQ_nondet_bool'] = '__VERIFIER_nondet_bool'
fmap['cpachecker', '__CSEQ_nondet_char'] = '__VERIFIER_nondet_char'
fmap['cpachecker', '__CSEQ_nondet_uchar'] = '__VERIFIER_nondet_uchar'

fmap['framac', '__CSEQ_assume'] = '__FRAMAC_assume'
fmap['framac', '__CSEQ_assertext'] = '__FRAMAC_assume'
fmap['framac', '__CSEQ_assert'] = '__FRAMAC_assume'
fmap['framac', '__CSEQ_nondet_int'] = '__VERIFIER_nondet_int'
fmap['framac', '__CSEQ_nondet_uint'] = '__VERIFIER_nondet_uint'
fmap['framac', '__CSEQ_nondet_bool'] = '__VERIFIER_nondet_bool'
fmap['framac', '__CSEQ_nondet_char'] = '__VERIFIER_nondet_char'
fmap['framac', '__CSEQ_nondet_uchar'] = '__VERIFIER_nondet_uchar'

fmap['uautomizer', '__CSEQ_assume'] = '__VERIFIER_assume'
fmap['uautomizer', '__CSEQ_assertext'] = '__VERIFIER_assume'
fmap['uautomizer', '__CSEQ_assert'] = '__VERIFIER_assume'
fmap['uautomizer', '__CSEQ_nondet_int'] = '__VERIFIER_nondet_int'
fmap['uautomizer', '__CSEQ_nondet_uint'] = '__VERIFIER_nondet_uint'
fmap['uautomizer', '__CSEQ_nondet_bool'] = '__VERIFIER_nondet_bool'
fmap['uautomizer', '__CSEQ_nondet_char'] = '__VERIFIER_nondet_char'
fmap['uautomizer', '__CSEQ_nondet_uchar'] = '__VERIFIER_nondet_uchar'

fmap['smack', '__CSEQ_assume'] = '__VERIFIER_assume'
fmap['smack', '__CSEQ_assertext'] = '__VERIFIER_assume'
fmap['smack', '__CSEQ_assert'] = '__VERIFIER_assume'
fmap['smack', '__CSEQ_nondet_int'] = '__VERIFIER_nondet_int'
fmap['smack', '__CSEQ_nondet_uint'] = '__VERIFIER_nondet_uint'
fmap['smack', '__CSEQ_nondet_bool'] = '__VERIFIER_nondet_bool'
fmap['smack', '__CSEQ_nondet_char'] = '__VERIFIER_nondet_char'
fmap['smack', '__CSEQ_nondet_uchar'] = '__VERIFIER_nondet_uchar'

_maxrightindent = 40   # max columns right for non-raw lines
_rawlinemarker = '__CSEQ_removeindent'


class dr_instrumenter(core.module.Translator):
	__visiting_struct = False
	__struct_stack = []               # stack of struct name
	__svcomp = False
	__roundint = False

	__avoid_type = []
	__ignore_list = []
	__bit_pthread = False

	__swarmdirname = ""
	__filename = ""
	__confignumber = ""
	__intervals = {}

	def init(self):
		self.addInputParam('backend','backend to use for analysis, available choices are:\n  bounded model-checkers: (blitz, cbmc, esbmc, llbmc, smack)\n  abstraction-based: (cpachecker, satabs, uautomizer, framac)\n  testing: (klee)','b','cbmc',False)
		self.addInputParam('bitwidth','custom bidwidths for integers','w',None,True)
		self.addInputParam('header', 'raw text file to add on top of the instrumented file', 'h', '', True)
		self.addInputParam('svcomp', 'extra instrumentation for SVCOMP', '', None, True)
		self.addInputParam('roundint', 'round to integer built-in types', '', None, True)
		self.addInputParam('bit-pthread', 'set bit vector for pthread types', '', None, True)
		self.addInputParam('threads', 'max no. of thread creations (0 = auto)', 't', '0', False)

	#Caledem
	def setInstanceInfo(self, swarmdirname, filename, confignumber, configintervals):
		self.__swarmdirname = swarmdirname
		self.__filename = filename
		self.__confignumber = confignumber
		self.__intervals = configintervals

	def loadfromstring(self,string,env):
		self.env = env
		self.backend = self.getInputParamValue('backend')
		self.bitwidths = self.getInputParamValue('bitwidth')
		self.extheader = self.getInputParamValue('header')

		if self.getInputParamValue('svcomp') is not None:
			self.__svcomp = True

		if self.getInputParamValue('roundint') is not None:
			self.__roundint = True

		if self.getInputParamValue('bit-pthread') is not None:
			self.__bit_pthread = True

		#Caledem
		#self.__intervals = env.intervals if hasattr(env, 'intervals') else {}

		if self.backend not in _backends:
			raise core.module.ModuleError("backend '%s' not supported" % self.backend)

		self.__avoid_type = [core.common.changeID[x] for x in core.common.changeID]
		self.__ignore_list = [
			'__cs_active_thread',
			'__cs_pc',
			'__cs_pc_cs',
			'__cs_last_thread',
			'__cs_thread_lines',
			'__cs_thread_index'
		]

		super(self.__class__, self).loadfromstring(string, env)
		
		self.lastoutputlineno = 0
		self.removelinenumbers()
		# self.output = core.utils.strip(self.output)
		# self.inputtooutput = {}
		# self.outputtoinput = {}
		# self.generatelinenumbers()

		# Transformation 3:
		# shift indentation of raw lines fully left
		# removing the trailing marker _rawlinemarker+semicolon, and
		# shift any other line to the right depending to the longest rawline, and
		# in any case no longer than _maxrightindent.
		maxlinemarkerlen = max(len(l) for l in self.output.splitlines()) - len(_rawlinemarker + ';') - 2
		maxlinemarkerlen = min(maxlinemarkerlen, _maxrightindent)

		newstring = ''

		for l in self.output.splitlines():
			if l.endswith(_rawlinemarker+';'):
				newstring += l[:-len(_rawlinemarker+';')].lstrip() + '\n'
			else:
				newstring += ' '*(maxlinemarkerlen)+l+'\n'

		self.output = newstring

		self.insertheader(self.extheader)          # header passed by previous module
		if self.env.local == 1: 
			self.insertheader("#include <string.h>")  #S needed for memcpy in local init #1
		
		# linearizability instrumentation
		liheaderfile = self.getInputParamValue("liheader")
		if liheaderfile is not None:
			header = core.utils.printFile(liheaderfile)
			header = header.replace("__CSEQ_assume", fmap[self.backend, "__CSEQ_assume"])
			header = header.replace("__CSEQ_assert", fmap[self.backend, "__CSEQ_assert"])
			self.insertheader(header)
			if not env.debug:
				core.utils.removeFile(liheaderfile)

		# Specific instrumentation for backend
		if self.backend == 'klee':
			self.insertheader(core.utils.printFile('modules/klee_extra.c'))
		elif self.backend == 'cpachecker':
			self.insertheader(core.utils.printFile('modules/cpa_extra.c'))
		elif self.backend == 'framac':
			self.insertheader(core.utils.printFile('modules/framac_extra.c'))
		elif self.backend == 'uautomizer':
			self.insertheader(core.utils.printFile('modules/uautomizer_extra.c'))
		elif self.backend == 'cbmc':
			self.insertheader(core.utils.printFile('modules/cbmc_extra.c'))
		elif self.backend == 'smack':
			self.insertheader(core.utils.printFile('modules/smack_extra.c'))

		if self.env.paths: 
		   self.insertheader(core.utils.printFile('modules/cbmc_extra_paths.c'))
		
		# Insert external 'system' header if there are (from the file)
		if hasattr(self.env, "systemheaders"):
			self.insertheader(getattr(self.env, "systemheaders"))
		
		self.insertheader(core.utils.printFile('modules/pthread_defs.c'))

		self.insertheader(self._generateheader())  # top comment with translation parameters


	def _get_type_by_bits(self, numbit):
		if numbit <= 8: return 'char'
		if numbit <= 16: return 'short'
		if numbit <= 32: return 'int'
		return 'int'

	def visit_Decl(self,n,no_type=False):
		# no_type is used when a Decl is part of a DeclList, where the type is
		# explicitly only for the first delaration in a list.
		#
		s = n.name if no_type else self._generate_decl(n)

		# In case  x  has a custom bitwidth (passed by a previous module), convert
		# 'int x'  to  'bitvectors[k] x' or
		# 'unsigned int x'  to  'unsigned bitvectors[k] x'.
		ninitextra = ''
		prefix = ''

		if self.backend == 'cbmc':
			if s.startswith('static '):
				s = s[7:]    # remove static
				prefix = 'static '
			if s.startswith("_Bool "): pass
			elif self.bitwidths is not None:
				if self.__visiting_struct:
					if (self.__struct_stack[-1], n.name) in self.bitwidths:
						if s.startswith("unsigned int "):
							if (self.__roundint
									# not (n.name in self.__ignore_list or
									#     n.name.startswith('__cs_tmp_t') or
									#     n.name.startswith('__cs_run_t'))
								):
								s = s.replace("unsigned int ","unsigned %s " % (self._get_type_by_bits(self.bitwidths[self.__struct_stack[-1],n.name])),1)
							else:
								s = s.replace("unsigned int ","unsigned __CPROVER_bitvector[%s] " % self.bitwidths[self.__struct_stack[-1],n.name],1)
						elif s.startswith("int "):
							if (self.__roundint
									# not (n.name in self.__ignore_list or
									#     n.name.startswith('__cs_tmp_t') or
									#     n.name.startswith('__cs_run_t'))
								):
								s = s.replace("int ","%s " % (self._get_type_by_bits(self.bitwidths[self.__struct_stack[-1],n.name])),1)
							else:
								s = s.replace("int ","__CPROVER_bitvector[%s] " % self.bitwidths[self.__struct_stack[-1],n.name],1)
						else:
							temp = s.split()   # split the declaration
							for i, item in enumerate(temp):
								if item.lstrip('*') == n.name and i > 0 and temp[i-1] not in self.__avoid_type and temp[i-1] in ('long', 'short', 'char',):   # temp[i-1] is the type
									if (self.__roundint
											# not (n.name in self.__ignore_list or
											#     n.name.startswith('__cs_tmp_t') or
											#     n.name.startswith('__cs_run_t'))
										):
										temp[i-1] = '%s' % self._get_type_by_bits(self.bitwidths[self.__struct_stack[-1],n.name])
									else:
										temp[i-1] = '__CPROVER_bitvector[%s]' % self.bitwidths[self.__struct_stack[-1],n.name]
									break
							s = " ".join(temp)
				else:
					currentFunct = self.currentFunct if self.currentFunct != '__cs_main_thread' else 'main'
					if s.startswith("unsigned int ") and (currentFunct,n.name) in self.bitwidths:
						if (self.__roundint
								# not (n.name in self.__ignore_list or
								#     n.name.startswith('__cs_tmp_t') or
								#     n.name.startswith('__cs_run_t'))
							):
							s = s.replace("unsigned int ","unsigned %s " % self._get_type_by_bits(self.bitwidths[currentFunct,n.name]),1)
							ninitextra = '(unsigned %s)' % self._get_type_by_bits(self.bitwidths[currentFunct,n.name])
						else:
							s = s.replace("unsigned int ","unsigned __CPROVER_bitvector[%s] " % self.bitwidths[currentFunct,n.name],1)
							ninitextra = '(unsigned __CPROVER_bitvector[%s])' % self.bitwidths[currentFunct,n.name]
					elif s.startswith("int ") and (currentFunct, n.name) in self.bitwidths:
						numbit = self.bitwidths[currentFunct, n.name]
						if (self.__roundint
								# not (n.name in self.__ignore_list or
								#     n.name.startswith('__cs_tmp_t') or
								#     n.name.startswith('__cs_run_t'))
							):
							s = s.replace("int ","%s " % self._get_type_by_bits(numbit),1)
							ninitextra = '(%s)' % self._get_type_by_bits(numbit)
						else:
							s = s.replace("int ","__CPROVER_bitvector[%s] " % numbit,1)
							ninitextra = '(__CPROVER_bitvector[%s])' % numbit
					elif (currentFunct, n.name) in self.bitwidths:
						numbit = self.bitwidths[currentFunct, n.name]
						temp = s.split()
						for i, item in enumerate(temp):
							if item.lstrip('*') == n.name and i > 0 and temp[i-1] not in self.__avoid_type and temp[i-1] in ('long', 'short', 'char',):
								if (self.__roundint
										# not (n.name in self.__ignore_list or
										#     n.name.startswith('__cs_tmp_t') or
										#     n.name.startswith('__cs_run_t'))
									):
									temp[i-1] = '%s' % self._get_type_by_bits(numbit)
								else:
									temp[i-1] = '__CPROVER_bitvector[%s]' % numbit
								break
						s = " ".join(temp)
			if prefix != '':
				s = prefix + s

		if n.bitsize: s += ' : ' + self.visit(n.bitsize)
		if n.init:
			if isinstance(n.init,pycparser.c_ast.InitList):
				s += ' = {' + self.visit(n.init) + '}'
			elif isinstance(n.init,pycparser.c_ast.ExprList):
				s += ' = (' + self.visit(n.init) + ')'
			else:
				s += ' = ' + ninitextra + '(' + self.visit(n.init) + ')'
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

	def visit_Typedef(self, n):
		s = ''
		if n.storage: s += ' '.join(n.storage) + ' '
		s += self._generate_type(n.type)
		if (self.backend == 'cbmc' and self.__bit_pthread and
				('int __cs_t' in s or
				'int __cs_mutex_t' in s or
				'int __cs_cond_t' in s )
			):
			import math
			k = int(math.floor(math.log(len(self.Parser.threadName) + 1, 2)))+1

			if '__cs_t' in s: k += 1
			if '__cs_mutex_t' in s: k += 1
			if '__cs_cond_t' in s: k = 3

			if self.__roundint:
				s = s.replace('int ', '%s ' % self._get_type_by_bits(k), 1)
			else:
				s = s.replace('int ', '__CPROVER_bitvector[%s] ' % k, 1)
		return s

	''' converts function calls '''
	def visit_FuncCall(self,n):
		fref = self._parenthesize_unless_simple(n.name)

		# Transformation 3.
		if fref == '__CSEQ_rawline':
			return self.visit(n.args)[1:-1]+_rawlinemarker

		sync_dict = {
			'__cs_mutex_destroy' : True,
			'__cs_mutex_lock' : True,
			'__cs_mutex_unlock' : True,
			'__cs_cond_wait_1' : True,
			'__cs_cond_wait_2' : True,
			'__cs_barrier_init' : True,
			'__cs_barrier_wait_1' : True,
			'__cs_barrier_wait_2' : True
		}
		if (fref == '__CSEQ_assertext' and
				self.__svcomp and
				self.backend != 'framac' and
				self.currentFunct in sync_dict):
			return fmap[self.backend, '__CSEQ_assume'] + '(' + self.visit(n.args.exprs[0]) + ')'

		args = self.visit(n.args)

		if (fref == '__CSEQ_assertext' and
				self.backend not in ('cbmc', 'esbmc')):
			args = self.visit(n.args.exprs[0])   # Only get the first expression

		if (self.backend, fref) in fmap:
			fref = fmap[self.backend, fref]

		if (fref == '__VERIFIER_error' and
				self.backend == 'framac'
			):
			return '__FRAMAC_assert(0)'
		#POR start
		ts = (int(self.getInputParamValue('rounds'))+1) * int(self.getInputParamValue('threads')+1)
		if fref == '__CPROVER_field_decl':
				args = self.visit(n.args.exprs[0])
				if (args == "\"ts_read\"" or
					args == "\"ts_write\""):
					args += ", (unsigned __CPROVER_bitvector[%d]) 0" % (math.ceil(math.log(ts,2)))
		#POR end
		return fref + '(' + args + ')'

	def _generateheader(self):
		masterhash_framework = '0000'
		masterhash_modulechain = '0000'

		#swarm
		instanceVersion = ''
		import json
		instanceVersion = json.dumps(self.__intervals)

		h = '/*\n'
		h += ' *  generated by CSeq [ %s / %s ]\n' % (masterhash_framework,masterhash_modulechain)
		h += ' * \n'
		h += ' *  instance version    %s\n' % instanceVersion
		# h += ' *                      %s %s\n' % (core.utils.shortfilehash('core/merger.py'),core.merger.VERSION)
		# h += ' *                      %s %s\n' % (core.utils.shortfilehash('core/parser.py'),core.parser.VERSION)
		# h += ' *                      %s %s ]\n' % (core.utils.shortfilehash('core/module.py'),core.module.VERSION)
		h += ' *\n'
		h += ' *  %s\n' %strftime("%Y-%m-%d %H:%M:%S",gmtime())
		h += ' *\n'
		h += ' *  params:\n'

		h += ' *    '
		for o,a in self.env.opts:
			 h+='%s %s, ' % (o,a)
		h+= '\n'
		h += ' *\n'

		# h += ' *  modules:\n'
		# h += ' *'

		# for transforms,m in enumerate(self.env.modules):
		#     paramin = ' '.join(p.id for p in m.inputparamdefs)
		#     params = '(%s)'  % paramin
		#     h += '  %s %s-%s %s' %(core.utils.shortfilehash('modules/%s.py' % m.getname()),m.getname(),'0.0',params) # m.VERSION
		# h += '\n'
		# h += ' *\n'

		h += ' */\n'
		return h
