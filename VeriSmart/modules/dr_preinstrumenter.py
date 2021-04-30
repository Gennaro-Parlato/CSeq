""" Extends preinstrumenter.py
    written and maintained by CSeq team


    This module overrules a transformation of preinstrumenter.py, namely
       it removes all ERROR labels as follows:
            - goto ERROR; ---> __CSEQ_assume(0);
            - ERROR :;    ----> __CSEQ_assume(0);
    (preinstrumenter.py was changing them to __CSEQ_assert)
"""
from modules import preinstrumenter
#import pycparser.c_parser, pycparser.c_ast, pycparser.c_generator

class dr_preinstrumenter(preinstrumenter.preinstrumenter):

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


