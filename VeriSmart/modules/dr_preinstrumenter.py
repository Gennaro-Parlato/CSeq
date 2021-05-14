""" Extends preinstrumenter.py
    written and maintained by CSeq team

    In addition to preinstrumenter.py this module:
      1. transforms asserts into assumes:
        a.  assert --> __CPROVER_assume
        b. __CPROVER_assert --> __CPROVER_assume
        c. __VERIFIER_assert --> __CPROVER_assume

      2. overrules a transformation by preinstrumenter.py, namely
       it removes all ERROR labels as follows:
            - goto ERROR; ---> __CSEQ_assume(0);
            - ERROR :;    ----> __CSEQ_assume(0);
    (preinstrumenter.py changes them to __CSEQ_assert)
"""
from modules import preinstrumenter
#import pycparser.c_parser, pycparser.c_ast, pycparser.c_generator

class dr_preinstrumenter(preinstrumenter.preinstrumenter):

    def visit_FuncCall(self, n):
        fref = self._parenthesize_unless_simple(n.name)

        if (fref.startswith("assert") or fref.startswith("__CPROVER_assert") or fref.startswith("__VERIFIER_assert")):
            return '__CPROVER_assume' + '(' + self.visit(n.args) + ')'

        return super(self.__class__, self).visit_FuncCall(n)


    def visit_Goto(self, n):
        if n.name == self.getErrorLabel():
            return '__CSEQ_assume(0);'
        else:
            return 'goto ' + n.name + ';'

    def visit_Label(self, n):
        ##### print "visiting LABEL, coords = %s\n" % self.Parser.nodecoords[n]

        if n.name == self.getErrorLabel():
            return '__CSEQ_assume(0);'
        else:
            return n.name + ':\n' + self._generate_stmt(n.stmt)


