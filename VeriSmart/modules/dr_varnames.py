""" CSeq C Sequentialization Framework
	scope-based variable renaming module
"""
"""

	This module performs just defines the prefixes for the variable renaming 
        done by the superclass
"""

from modules import varnames


class dr_varnames(varnames.varnames):

	nondetprefix = '__dr_nondet_'  # prefix for uninitialized local variables 
	prefix = '__dr_local_'        # prefix for initialized local variables
	paramprefix = '__dr_param_'   # prefix for function params


	def loadfromstring(self, string, env, fill_only_fields=None):
		super(self.__class__, self).loadfromstring(string, env)



