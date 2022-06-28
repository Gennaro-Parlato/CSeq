""" Lazy-CSeq
    thread Duplicator module

    written by Omar Inverso, University of Southampton.
"""
VERSION = 'duplicator-0.0-2015.07.15'
#VERSION = 'duplicator-0.0-2015.07.13'
#VERSION = 'duplicator-0.0-2015.07.08'
#VERSION = 'duplicator-0.0-2015.06.23'
#VERSION = 'duplicator-0.0-2014.12.24'    # CSeq-1.0beta
#VERSION = 'duplicator-0.0-2014.10.26'    # CSeq-Lazy-0.6: newseq-0.6a, newseq-0.6c, SVCOMP15
#VERSION = 'duplicator-0.0-2014.10.15'
#VERSION = 'duplicator-0.0-2014.03.14' (CSeq-Lazy-0.4)
#VERSION = 'duplicator-0.0-2014.02.25' (CSeq-Lazy-0.2)

#
# Duplicator where thread function arguments are char* such as the shared memory state is accessible
#

from modules import duplicator
import copy
import core.common, core.module, core.parser, core.utils
import pycparser.c_parser, pycparser.c_ast, pycparser.c_generator


class abstr_duplicator(duplicator.duplicator):

    def postprocess(self):
        #for t in self.Parser.threadName:
        #   print "thread %s times %s" % (t, self.Parser.threadCallCnt[t])

        # The thread functions prototypes of duplicated threads
        # need to be duplicated too.
        #
        for f in self.Parser.threadName:
            if f in self.Parser.funcDecl:
                oldPrototype = self.Parser.funcDecl[f] + ';'
                newPrototype = ''

                # TODO: this needs AST-based implemetation
                for i in range(0, self.Parser.threadCallCnt[f]):
                    s = oldPrototype.replace(f+'(', f+'_'+str(i)+'(', 1)
                    newPrototype += s[:5]+s[5:].replace("void *","char *")

                #print "replacing '%s' with '%s'\n\n\n\n" %( oldPrototype, newPrototype)
                self.output = self.output.replace(oldPrototype, newPrototype)

    def visit_FuncDecl(self, n):
        if n.name == 'main' or n.name not in self.Parser.threadName:
            return super().visit_FuncDecl(n)
        else:
            n.type.args.params[0].type.type.type.names[0] = "char"
            return super().visit_FuncDecl(n)
            
    def visit_FuncDef(self, n):
        #print(self.Parser.threadName, n.decl.name, n.decl)
        # int __cs_create(__cs_t *__cs_new_thread_id, void *__cs_attr, void *(*__cs_thread_function)(void *), void *__cs_arg, int __cs_threadID)
        #print(n.decl)
        if n.decl.name == core.common.changeID['pthread_create']:
            #print(n)
            n.decl.type.args.params[3].type.type.type.names[0] = "char"
            return super().visit_FuncDef(n)
        elif n.decl.name == 'main' or n.decl.name not in self.Parser.threadName or type(n.decl.type.args.params[0].type.type) is pycparser.c_ast.IdentifierType:
            return super().visit_FuncDef(n)
        else:
            #print(n)
            #print(n.decl.type.args.params[0].type.type.type.names[0])
            n.decl.type.args.params[0].type.type.type.names[0] = "char"
            return super().visit_FuncDef(n)
            
    def visit_FuncCall(self, n):
        fref = self._parenthesize_unless_simple(n.name)

        if fref == core.common.changeID['pthread_create']:
            if type(n.args.exprs[3]) is pycparser.c_ast.Cast:
                n.args.exprs[3].to_type.type.type.type.names[0] = "char"
        return super().visit_FuncCall(n)
