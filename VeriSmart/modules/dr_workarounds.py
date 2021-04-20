""" Extends workarounds.py
    written and maintained by CSeq team


    In addition to workarounds.py this module:
      1. transforms asserts into assumes:
        assert --> __CPROVER_assume
        __CPROVER_assert --> __CPROVER_assume
       
"""
from modules import workarounds
import pycparser.c_parser, pycparser.c_ast, pycparser.c_generator


class dr_workarounds(workarounds.workarounds):

    def visit_FuncCall(self, n):
        fref = self._parenthesize_unless_simple(n.name)

        if (fref.startswith("assert") or fref.startswith("__CPROVER_assert")):
            return '__CPROVER_assume' + '(' + self.visit(n.args) + ')'
           
        return super(self.__class__, self).visit_FuncCall(n)    


