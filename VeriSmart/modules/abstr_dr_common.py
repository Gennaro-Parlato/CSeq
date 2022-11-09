from modules import lazyseqnewschedule
from pycparser import c_ast
import pycparser.c_parser, pycparser.c_ast, pycparser.c_generator
import core.common, core.module, core.parser, core.utils
from pycparser.c_generator import CGenerator
from core import abs_dr_rules
import os
from core.support_file import SupportFileManager
import copy
from core.var_simplifier import Cleaner

'''
Utility class that allows to set a field to a specific value in a block and restore it when left.
Those two codes are equivalent:
```
x = ...1...
with BakAndRestore(x,'y',1):
    ...2...
```
and
```
x = ...1...
bak = x.y
x.y = 1
...2...
x.y = bak
```
'''
class NoBaks:
    def __enter__(self):
        pass
    def __exit__(self, exc_type, exc_value, exc_traceback):
        pass
        
class BakAndRestore:
    def __init__(self, obj, *parts): #filed, tmpval...
        self.obj = obj
        self.fields = []
        self.tmpvals = []
        for i in range(0,len(parts),2):
            self.fields.append(parts[i])
            self.tmpvals.append(parts[i+1])
    def __enter__(self):
        self.baks = []
        for i in range(len(self.fields)):
            self.baks.append(getattr(self.obj, self.fields[i]))
            setattr(self.obj, self.fields[i], self.tmpvals[i])
    def __exit__(self, exc_type, exc_value, exc_traceback):
        for i in range(len(self.fields)):
            setattr(self.obj, self.fields[i], self.baks[i])
        
def getType(node_info):
    return str(type(node_info)).split('.')[-1].replace('>', ' ').replace("'", '').replace(' ', '')
    
class MacroFileManager:
    def __init__(self, mf_name_pfx, configs, adrs, debug=False):
        self.mf_name_pfx = os.path.abspath(mf_name_pfx)
        self.config = configs
        self.progr = 0
        self.macroToExprs = dict()
        self.macroToNodes = dict()
        self.exprsToMacro = dict()
        self.listOfMacro = []
        self.adrs = adrs
        self.dbg_visitor = CGenerator() if debug else None
        
    def auxvars(self, transs):
        self.macroToExprs["AUXVARS"] = ["main(void); "+t.strip().replace("\n"," \\\n") for t in transs]
        return "int AUXVARS();"
    
    def expression(self, n, transs, passthrough, typlbl=None):
        if passthrough:
            assert(len(transs)==1)
            return transs[0]
        else:
            #assert(len(transs)>1)
            tp = typlbl if typlbl is not None else str(type(n)).split(".")[-1][:-2]
            exprsJoin = ";".join(transs)
            if exprsJoin in self.exprsToMacro:
                self.macroToNodes[self.exprsToMacro[exprsJoin]].add(self.dbg_visitor.visit(n))
                return self.exprsToMacro[exprsJoin]+"()"
            else:
                macro_name = "EXPR_"+tp+"_"+str(self.progr)
                self.progr += 1
                self.listOfMacro.append(macro_name)
                self.macroToExprs[macro_name] = transs[:]
                self.macroToNodes[macro_name] = {self.dbg_visitor.visit(n)}
                self.exprsToMacro[exprsJoin] = macro_name
                return macro_name+"()"

    def expression_comma(self, n, transs, passthrough):
        if passthrough:
            assert(len(transs)==1)
            return transs[0]
        else:
            #assert(len(transs)>1)
            transs = [[t, None] if isinstance(t, str) else t for t in transs]
            firstArgs = [t[0] for t in transs]
            anySecondArg = ([t[1] for t in transs if t[1] is not None]+[None])[0]
            tp = str(type(n)).split(".")[-1][:-2]
            exprsJoin = ";".join(firstArgs)
            if exprsJoin in self.exprsToMacro:
                self.macroToNodes[self.exprsToMacro[exprsJoin]].add(self.dbg_visitor.visit(n))
                return [self.exprsToMacro[exprsJoin]+"()", anySecondArg]
            else:
                macro_name = "EXPR_"+tp+"_"+str(self.progr)
                self.progr += 1
                self.listOfMacro.append(macro_name)
                self.macroToExprs[macro_name] = firstArgs
                self.macroToNodes[macro_name] = {self.dbg_visitor.visit(n)}
                self.exprsToMacro[exprsJoin] = macro_name
                return [macro_name+"()", anySecondArg]
                
    def get_macro_file_name(self, i):
        return self.mf_name_pfx+"_"+self.config[i]+".h"
                
    def save(self):
        for i in range(len(self.config)):
            for (macro_name, transs) in self.macroToExprs.items():
                #print(transs, self.config)
                if transs[i] != "" and macro_name != "AUXVARS" and "JmpElse" not in macro_name:
                    self.adrs[i].cleaner.add_code_to_clean(macro_name, transs[i])
            self.adrs[i].cleaner.do_clean_codes()
            clean_codes = self.adrs[i].cleaner.get_clean_codes()
            with open(self.get_macro_file_name(i), "w") as f:
                print("#ifndef NULL\n#define NULL 0\n#endif\n#ifndef bool\n#define bool _Bool\n#endif\n", file=f)
                print(self.adrs[i].getAbstractionMacros(), file=f)
                for macro_name in self.macroToExprs.keys():
                    trans = clean_codes[macro_name] if self.macroToExprs[macro_name][i] != "" and macro_name != "AUXVARS" and "JmpElse" not in macro_name else self.macroToExprs[macro_name][i]
                    trans = trans.replace("(;)","((void)0)")
                    if trans != ";" and macro_name != "AUXVARS" and "JmpElse" not in macro_name:
                        trans = "("+trans+")"
                    if trans == "()":
                        trans = ";"
                    if self.dbg_visitor and self.macroToExprs[macro_name][i] != "" and macro_name != "AUXVARS" and "JmpElse" not in macro_name:
                        print("/*"+" ; ".join("("+c+")" for c in self.macroToNodes[macro_name])+"*/", file=f)
                    print("#define "+macro_name+"() "+trans, file=f)

class abstr_dr_common(lazyseqnewschedule.lazyseqnewschedule): 
    def get_current_idx(self):
        try:
            from mpi4py import MPI
            comm = MPI.COMM_WORLD
            rank = comm.Get_rank()
            return str(rank)
        except ImportError:
            return "0"
        
    def init(self, abs_on, dr_on):
        super().init()
        #Instrument this node and its children
        self.any_instrument = abs_on or dr_on
        
        
        #self.abs_on = abs_on
        self.dr_on = dr_on
        self.abs_dr_vpstate = None
        self.elseLblProgr = 0 #used in underapproximation to do the jump between then and else
        
        # Antonio var. Don't touch those functions. Extend the following list when special function or void function are found during parsing
        self.funcCall_to_exclude = ['sscanf',
                                    'exit',
                                    'fprintf',
                                    'printf',
                                    'free',
                                    'abort',
                                    '__CSEQ_rawline',
                                    '__CSEQ_assume',
                                    'assume_abort_if_not'
                                    ]
        
        # List of all functions observed. When visiting their ID, you should return them verbatim as their address is known (they are effectively constants)                            
        self.funcNames = ['__cs_create', '__cs_join', '__cs_exit']
        
        # variable scope (global/local)                            
        self.scope = "global"
        
        # vanilla CGenerator to copy the original code (pre-lazy)
        self.cGen_original = CGenerator()
        
        # Global expressions for which I should evaluate the type support macros
        self.global_support_macro_declarations = ''
        
        # Local expressions for which I should evaluate the type
        self.string_support_macro = ""
        # Header for local expressions type file
        self.string_support_macro_headers = """
#include <stdio.h>
#define PRINT_DT(E,ID, EXP) printf("%s_%d, %d\\n",EXP,ID,typename(E) )
void __CPROVER_get_field(void *a, char field[100] ){return;}
void __CPROVER_set_field(void *a, char field[100], _Bool c){return;}        
        
        """
        
        rank = self.get_current_idx()
        # Macro file name. TODO make it parametric (see abstraction_prep.loadfromstring)
        self.macro_file_name = "macro_plain_"+rank+".h"
        self.macro_file_pfx = "macro_"+rank
        
        # Support file name. TODO make it parametric (see abstraction_prep.loadfromstring)
        self.support_file_name = "support_file_"+rank+".c"
        # Support file name. TODO make it parametric (see abstraction_prep.loadfromstring)
        self.support_file_runnable = "support_file_"+rank
        
        # set of arrays (they have a known address)
        self.program_arrays = []
        
        # set of pointers (they are generally set at runtime, hence can be abstract)
        self.program_pointers = []
        
        # TODO from Antonio's code: role unclear
        self.integral_type_list = ['int',
                                   'signed',
                                   'signed int',
                                   'unsigned',
                                   'unsigned int',
                                   'char',
                                   'signed char',
                                   'unsigned char',
                                   'short',
                                   'short int',
                                   'signed short',
                                   'signed short int',
                                   'unsigned short'
                                   'unsigned short int',
                                   'long int',
                                   'long',
                                   'long long',
                                   'long long int',
                                   'signed long int',
                                   'signed long',
                                   'signd long long',
                                   'signed long long int',
                                   'unsigned long',
                                   'unsigned long int',
                                   'unsigned long long int',
                                   '_Bool'
                                ]
                                
        # TODO Global variables (also consider thread locals?). Unclear role
        self.interest_variables_list = {}
        
        self.global_var_initializations = ""
        
        # are we instrumenting a full statement?
        self.full_statement = True
        
        self.atomicLvl = 0 # this counts how much nesting in __CSEQ_atomic_ functions we are. If =0: we are not in an atomic function; otherwise that's atomic and we need to disable Visible Points
        
    def insertGlobalVarInit(self, x):
        return x.replace("int main(void) {", "int main(void) {\n"+self.global_var_initializations, 1)
    def __createMainKLEERoundRobinDecomposePC(self, rounds):
        return self.insertGlobalVarInit(super().__createMainKLEERoundRobinDecomposePC(rounds))
    def __createMainKLEERoundRobinOnePCCS(self, rounds):
        return self.insertGlobalVarInit(super().__createMainKLEERoundRobinOnePCCS(rounds))
    def __createMainKLEERoundRobin(self, rounds):
        return self.insertGlobalVarInit(super().__createMainKLEERoundRobin(rounds))
    def __createMainRoundRobinDecomposePC(self, rounds):
        return self.insertGlobalVarInit(super().__createMainRoundRobinDecomposePC(rounds))
    def __createMainRoundRobinOnePCCS(self, rounds):
        return self.insertGlobalVarInit(super().__createMainRoundRobinOnePCCS(rounds))
    def createMainRoundRobin(self, rounds):
        return self.insertGlobalVarInit(super().createMainRoundRobin(rounds))
    def __createMainDecomposePC(self, rounds):
        return self.insertGlobalVarInit(super().__createMainDecomposePC(rounds))
    def __createMainOnePCCS(self, rounds):
        return self.insertGlobalVarInit(super().__createMainOnePCCS(rounds))
    def __createMain(self, rounds):
        return self.insertGlobalVarInit(super().__createMain(rounds))
        
    def get_conf_adr(self, descr):
        if descr == "plain":
            return abs_dr_rules.AbsDrRules(self, False, self.dr_on, self.dr_on and self.cca, None, self.support_file_mgr, self.macro_file_name, underapprox=False, debug=self.env.debug)
        parts = descr.split("_")
        bw = int(parts[1])
        assert(parts[0] in ("under","over"))
        return abs_dr_rules.AbsDrRules(self, True, self.dr_on, self.dr_on and self.cca, bw, self.support_file_mgr, self.macro_file_name, underapprox=parts[0]=="under", debug=self.env.debug)
        
    def loadfromstring(self, string, env):
        self.env = env  
        self.cca = self.dr_on and self.codeContainsAtomic()
        self.support_file_mgr = SupportFileManager()
        #self.underapprox = env.enableAbstrUnderapprox #underapproximation
        #self.abs_bitwidth = env.bit_width
        #self.abs_dr_rules = abs_dr_rules.AbsDrRules(self, self.abs_on, self.dr_on, self.dr_on and self.codeContainsAtomic(), self.abs_bitwidth, SupportFileManager(), self.macro_file_name, underapprox=self.underapprox, debug=env.debug)
        self.configs = self.env.cases_abstr #["plain"]+[sch+"_"+bw for sch in ["over","under"] for bw in ["4","8","16"]] 
        self.conf_adr = [self.get_conf_adr(descr) for descr in self.configs]
        self.macro_file_manager = MacroFileManager(self.macro_file_pfx, self.configs, self.conf_adr, debug=True)
        self.plain_adr = abs_dr_rules.AbsDrRules(self, False, False, False, None, self.support_file_mgr, self.macro_file_name, underapprox=False, debug=self.env.debug)
        
        # Instrumentation arguments: {'abs_mode':abs_mode, 'dr_mode':dr_mode} or {'abs_mode':'GET_VAL', 'dr_mode':'NO_ACCESS'} when translating a statement
        self.abs_dr_mode = [{'abs_mode':'GET_VAL' if adr.abs_on else None, 'dr_mode':'NO_ACCESS' if adr.dr_on else None} for adr in self.conf_adr]
        self.abs_dr_state = [abs_dr_rules.CPState() for adr in self.conf_adr]
        super().loadfromstring(string, env)
        
        self.macro_file_manager.save()
        #abs_mfn = self.abs_dr_rules.macroFile.save_get_path()
        abs_mfn2 = self.macro_file_manager.get_macro_file_name(0)#.save_get_path()
        if True:# abs_mfn2 is not None:
            #os.path.abspath(self.macro_file_name)
            self.setOutputParam('header_abstraction','#include "%s"\n' % abs_mfn2)
            #with open(abs_mfn, "w") as f:
            #    f.write(self.abs_dr_rules.macro_file_content())
    
    # allows to create blocks where abstraction instrumentation is avoided                                
    def no_any_instrument(self): 
        #return BakAndRestore(self, 'any_instrument', False)
        return BakAndRestore(self, 'conf_adr', [self.plain_adr], 'abs_dr_mode', [{'abs_mode':None, 'dr_mode':None}], 'abs_dr_state', [abs_dr_rules.CPState()])
        
    #def clean_cp_state_on_statement(self, args): 
    #    if 'in_expr' not in args or not args['in_expr']:
    #        return BakAndRestore(self, 'abs_dr_state', abs_dr_rules.CPState())
    #    else:
    #        return NoBaks()
            
    def clean_cp_state(self): 
        return BakAndRestore(self, 'abs_dr_state', [abs_dr_rules.CPState() for adr in self.conf_adr])
        
    def visit_with_absdr_args(self, state, n, adr, abs_mode, dr_mode, full_statement, **kwargs):
        assert(full_statement == False)
        new_abs_dr_mode = [{'abs_mode':abs_mode, 'dr_mode':dr_mode}]
        with BakAndRestore(self, 'conf_adr', [adr], 'abs_dr_mode', new_abs_dr_mode, 'abs_dr_state', [state], 'full_statement', full_statement):
            return self.visit(n)
                
    def visit_noinstr(self, n, full_statement):
        with self.no_any_instrument():
            #print("NOINSTR1", n)
            with BakAndRestore(self, 'full_statement', full_statement):
                ans = self.visit(n)
                return ans
                
    def dr_mode_set(self, dr_mode):
        new_abs_dr_mode = [{'abs_mode':adm['abs_mode'], 'dr_mode':dr_mode if adm['dr_mode'] is not None else None} for adm in self.abs_dr_mode]
        return BakAndRestore(self, 'abs_dr_mode', new_abs_dr_mode)
        
    def abs_dr_mode_set(self, abs_mode, dr_mode):
        new_abs_dr_mode = [{'abs_mode':abs_mode if adm['abs_mode'] is not None else None, 'dr_mode':dr_mode if adm['dr_mode'] is not None else None} for adm in self.abs_dr_mode]
        return BakAndRestore(self, 'abs_dr_mode', new_abs_dr_mode)
        
    def do_rule(self, rule, n, **extra_args):
        with BakAndRestore(self, 'full_statement', False):
            ans = []
            for i in range(len(self.conf_adr)):
                if rule == "rule_IfCond" or self.conf_adr[i].dr_on or self.conf_adr[i].abs_on or self.conf_adr[i].underapprox:
                    ans.append(getattr(self.conf_adr[i], rule)(self.abs_dr_state[i], n, self.abs_dr_mode[i]['abs_mode'], self.abs_dr_mode[i]['dr_mode'], self.full_statement, **extra_args))
                else:
                    typ = str(type(n)).split(".")[-1][:-2]
                    with self.no_any_instrument():
                        if typ == "ExprList":
                            ans.append((getattr(super(), "visit_"+typ)(n),None))
                        else:
                            ans.append(getattr(super(), "visit_"+typ)(n))
            return ans
                
    def visit_Return(self, n):
        if self._lazyseqnewschedule__currentThread != '__CSEQ_assert' and self._lazyseqnewschedule__currentThread not in self.Parser.funcReferenced and not (self._lazyseqnewschedule__atomic or self.atomicLvl > 0):
            self.error("error: %s: return statement in thread '%s'.\n" % (self.getname(), self._lazyseqnewschedule__currentThread))

        s = 'return'
        with self.dr_mode_set("TOP_ACCESS"):
            with BakAndRestore(self, 'full_statement', True):
                if n.expr: s += ' ' + self.visit(n.expr)
        return s + ';'
        
    def visit_FileAST(self, n):
        #if not self.any_instrument or not (self.dr_on or self.abs_on):
        #    return super().visit_FileAST(n)
            
        self.support_file_mgr.compile(n, self.support_file_name, self.support_file_runnable)

        #Print on macro file, the first set of variables,define and so on...
        # TODO self.transformation_rule.utility.printFirsMacroSet(self.support_variables)

        s = ''
        
        auxvars1 = {adr: "" if adr is None else adr.aux_vars_decl() for adr in self.conf_adr}

        s3 = ''
        for ext in n.ext:
            if isinstance(ext, c_ast.FuncDef):
                s3 += self.visit(ext)
                self.scope = 'global'
            elif isinstance(ext, c_ast.Pragma):
                s3 += self.visit(ext) + '\n'
            else:
                s3 += self.visit(ext) + ';\n'
                
        s += self.macro_file_manager.auxvars(['\n'.join([auxvars1[adr], adr.cond_vars_decl(), adr.bav1_vars_decl(), adr.bap1_vars_decl()]) for adr in self.conf_adr])

        #TODO check what it means
        #ris = self.faked_typedef_start \
        #      + '\n'.join([item for item in self.transformation_rule.getFakedDefinition()]) \
        #      + '\n' \
        #      + self.faked_typedef_end \
        #      + '\n' \
        #      + s
        ris = s + s3

        #self.addOutputParam('abstraction')
        #self.setOutputParam('abstraction', self)
        #logging.info("Performed transformation: %s" % json.dumps(self.transformation_rule.rules_counter, indent=4))

        #TODO self.dynamicSelection()
        
        self.dynamicSelectionInfoForDebug()

        return ris
        
    def additionalCode(self,threadIndex):
        s = ''
        
        if self.dr_on and self.abs_dr_vpstate is not None:
            if self.abs_dr_vpstate.VP1required:
                s += '__cs_dataraceActiveVP1 = ( @£@L1 == (__cs_pc_cs[%s]-1) ) ; \n' % threadIndex
            if self.abs_dr_vpstate.VP2required:
                s += '__cs_dataraceActiveVP2 = ( @£@L2 == __cs_pc[%s] ) ; \n' % threadIndex   #DR
        return s
        
    def visit_Compound(self, n): # copied to reset cp state between statements TODO once accepted, move this in lazyseqnewschedule and replace self._lazyseqnewschedule__<x> with self.__<x>
        assert(self.full_statement)
        compoundList = ["{\n"]
        # Insert the labels at the beginning of each statement,
        # with a few exclusions to reduce context-switch points...

        if n.block_items:
            for stmt in n.block_items:
                assert(self.full_statement)
                if type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == "__CSEQ_ROWLINE" and stmt.args is not None and type(stmt.args.exprs[0]) is c_ast.UnaryOp and stmt.args.exprs[0].expr.name == "atomiclvl":
                    if stmt.args.exprs[0].op == "p++":
                        self.atomicLvl += 1
                        continue
                    elif stmt.args.exprs[0].op == "p--":
                        self.atomicLvl -= 1
                        continue
                    else:
                        assert(False)
                self.initFlags(self._lazyseqnewschedule__stmtCount)
                # Case 1: last statement in a thread (must correspond to last label)
                if type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == core.common.changeID['pthread_exit']: ##if type(stmt) == pycparser.c_ast.FuncCall and self._parenthesize_unless_simple(stmt.name) == core.common.changeID['pthread_exit']:
                    self._lazyseqnewschedule__stmtCount += 1
                    self._lazyseqnewschedule__maxInCompound = self._lazyseqnewschedule__stmtCount
                    with self.clean_cp_state():
                        code = '@£@F ' + self.visit(stmt) + ';\n'
                    compoundList.append(code)

                # Case 2: labels
                elif (type(stmt) in (pycparser.c_ast.Label,)):
                    # --1-- Simulate a visit to the stmt block to see whether it makes any use of pointers or shared memory.
                    with self.clean_cp_state():
                        #with BakAndRestore(self, 'full_statement', False):
                        globalAccess = self._lazyseqnewschedule__globalAccess(stmt)
                    newStmt = ''
                    # --2-- Now rebuilds the stmt block again,
                    #       this time using the proper formatting
                    #       (now we know if the statement is accessing global memory,
                    #       so to insert the stamp at the beginning when needed)
                    #
                    if not (self._lazyseqnewschedule__atomic or self.atomicLvl > 0) and self._lazyseqnewschedule__stmtCount == -1:   # first statement in a thread
                        self._lazyseqnewschedule__stmtCount += 1
                        self._lazyseqnewschedule__maxInCompound = self._lazyseqnewschedule__stmtCount
                        threadIndex = self.Parser.threadOccurenceIndex[self._lazyseqnewschedule__currentThread]
                        with self.clean_cp_state():
                            s = self.visit(stmt.stmt)
                        with self.clean_cp_state():
                            #if s.count('\n') > 2:
                            #    print(1, stmt)
                            #print(stmt.stmt, self.abs_dr_vpstate)
                            code = '@£@I1' + self.additionalCode(threadIndex) + '@£@I2' + s + '@£@I3' + self.alternateCode(stmt.stmt) + '@£@I4' + ';\n' 
                    elif (not self._lazyseqnewschedule__visit_funcReference and (
                        (type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == '__CSEQ_atomic_begin') or
                        (not (self._lazyseqnewschedule__atomic or self.atomicLvl > 0) and
                            (globalAccess or
                            (type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == core.common.changeID['pthread_create']) or
                            (type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == core.common.changeID['pthread_join']) or
                            (type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name.startswith('__CSEQ_atomic') and not stmt.name.name == '__CSEQ_atomic_end') or
                            (type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name.startswith('__CSEQ_assume')) or
                            (type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == '__cs_cond_wait_2')
                            )
                        )
                        )):
                        self._lazyseqnewschedule__stmtCount += 1
                        self._lazyseqnewschedule__maxInCompound = self._lazyseqnewschedule__stmtCount
#@@@@        code = self.visit(stmt)
                        threadIndex = self.Parser.threadOccurenceIndex[self._lazyseqnewschedule__currentThread]
                        with self.clean_cp_state():
                            s = self.visit(stmt.stmt)
                        #if s.count('\n') > 2:
                        #    print(2, stmt)
                        with self.clean_cp_state():
                            #print(stmt.stmt, self.abs_dr_vpstate)
                            code = '@£@I1' + self.additionalCode(threadIndex) + '@£@I2' + s + '@£@I3' + self.alternateCode(stmt.stmt) + '@£@I4' + ';\n'
                    else:
                        with self.clean_cp_state():
                            code = self.visit(stmt.stmt) + ';\n'

                    guard = ''
                    if not (self._lazyseqnewschedule__atomic or self.atomicLvl > 0):
                        guard = '@£@G'
                    code = self._make_indent() + stmt.name + ': ' + guard + code + '\n'
                    compoundList.append(code)

                # Case 3: all the rest....
                elif (type(stmt) not in (pycparser.c_ast.Compound, pycparser.c_ast.Goto, pycparser.c_ast.Decl)
                    and not (self._lazyseqnewschedule__currentThread=='main' and not self._lazyseqnewschedule__enableDR and self._lazyseqnewschedule__firstThreadCreate == False) # and not running with datarace --dr => False 
                    or (type(stmt) not in (pycparser.c_ast.Compound,) and (self._lazyseqnewschedule__currentThread=='main' and self._lazyseqnewschedule__stmtCount == -1))
                    ) :
                    is_compulsory_vp = self.needs_compulsory_visible_point(stmt)

                    # --1-- Simulate a visit to the stmt block to see whether it makes any use of pointers or shared memory.
                    with self.clean_cp_state():
                        #with BakAndRestore(self, 'full_statement', False):
                        globalAccess = self._lazyseqnewschedule__globalAccess(stmt)
                    newStmt = ''

                    self.lines = set()   # override core.module marking behaviour, otherwise  module.visit()  won't insert any marker

                    # --2-- Now rebuilds the stmt block again,
                    #       this time using the proper formatting
                    #      (now we know if the statement is accessing global memory,
                    #       so to insert the stamp at the beginning when needed)
                    if (not self._lazyseqnewschedule__atomic or self.atomicLvl > 0) and self._lazyseqnewschedule__stmtCount == -1:   # first statement in a thread
                        self._lazyseqnewschedule__stmtCount += 1
                        self._lazyseqnewschedule__maxInCompound = self._lazyseqnewschedule__stmtCount
                        threadIndex = self.Parser.threadOccurenceIndex[self._lazyseqnewschedule__currentThread]
                        with self.clean_cp_state():
                            s =  self.visit(stmt)
                        #if s.count('\n') > 2:
                        #    print(3, stmt)
                        with self.clean_cp_state():
                            #print(stmt, self.abs_dr_vpstate)
                            code = '@£@I1' + self.additionalCode(threadIndex)+ '@£@I2' + s + '@£@I3' + self.alternateCode(stmt) + '@£@I4' + ';\n'
                    elif is_compulsory_vp or (not self._lazyseqnewschedule__visit_funcReference and (
                        (type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == '__CSEQ_atomic_begin') or
                        (not (self._lazyseqnewschedule__atomic or self.atomicLvl > 0) and
                            (globalAccess or
                            (type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == core.common.changeID['pthread_create']) or
                            (type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == core.common.changeID['pthread_join']) or
                            (type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name.startswith('__CSEQ_atomic') and not stmt.name.name == '__CSEQ_atomic_end') or
                            (type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name.startswith('__CSEQ_assume')) or
                            (type(stmt) == pycparser.c_ast.FuncCall and stmt.name.name == '__cs_cond_wait_2')
                            )
                        )
                        )):
                        
                        if is_compulsory_vp:
                            self._lazyseqnewschedule__stmtVPCompulsory += 1
                        self._lazyseqnewschedule__stmtCount += 1
                        self._lazyseqnewschedule__maxInCompound = self._lazyseqnewschedule__stmtCount
                        threadIndex = self.Parser.threadOccurenceIndex[self._lazyseqnewschedule__currentThread]
                        with self.clean_cp_state():
                            s = self.visit(stmt)
                            
                        #if s.count('\n') > 2:
                        #    print(4, stmt)
                        with self.clean_cp_state():
                            #print(stmt, self.abs_dr_vpstate)
                            prefix = '@£@J1' if is_compulsory_vp else '@£@I1'
                            code = prefix + self.additionalCode(threadIndex) + '@£@I2' + s + '@£@I3' + self.alternateCode(stmt) + '@£@I4' + ';\n'
    
                    else:
                        with self.clean_cp_state():
                            code = self.visit(stmt) + ";\n"
                    compoundList.append(code)
                else:
                    with self.clean_cp_state():
                        code = self.visit(stmt) + ";\n"
                    compoundList.append(code)
        compoundList[len(compoundList)-1] = compoundList[len(compoundList)-1] + '\n}'
        listToStr = ''.join(stmt for stmt in compoundList)
        return listToStr
        
    def dynamicSelectionInfoForDebug(self):
        #OLD print("Starting SSM:",self.string_support_macro)
        #this will be the text to put into a main
        str_to_append = '' # TODO ?
        global_text = '' # global and local variables
        inRecording = False
        # TODO check if that's the reasoning: do this such as, when evaluate local variable types, you see the global variables? NOPE

        for line in self.string_support_macro.split('\n'):

            if line.startswith('}'):
                inRecording=False
                str_to_append+=line+'\n'

            elif line.startswith('{'):
                inRecording = True

            if inRecording:
                str_to_append += line +'\n'

            elif not inRecording and not line.startswith('}'):
                global_text += line+'\n'

        # Create type evaluation file
        pthread_defs_path = os.path.abspath(os.getcwd()) + '/modules/pthread_defs.c'
        self.string_support_macro = '#include "'+self.macro_file_name + '"' + self.string_support_macro_headers + '\n' + '#include "' + pthread_defs_path + '"\n' + self.global_support_macro_declarations + '\n' + global_text + '\n' + 'int main(){\n' + str_to_append + '\n' +'return 0;' + '\n' + '}'
        
        # OLD print("Type macro SSM:",self.string_support_macro)
        #print("Type macro SSM:",self.abs_dr_rules.support.getFile())
        
    '''# destroy constant propagation state between statements, as with visible points we do not know whether they will be executed sequentially
    def additionalCode(self,threadIndex):
        self.abs_dr_state = abs_dr_rules.State()
        return super().additionalCode(threadIndex)
        
    def alternateCode(self, n):
        self.abs_dr_state = abs_dr_rules.State()
        return super().alternateCode(n)'''
        
    def visit_FuncDef(self, n):
        #if not self.any_instrument or not (self.dr_on or self.abs_on):
        #    return super().visit_FuncDef(n)
        self.scope = 'local'
        func_name = n.decl.name
        if func_name.startswith('__cs_') or func_name == 'assume_abort_if_not':
            # those functions are made by us: won't touch them
            with self.no_any_instrument():
                with BakAndRestore(self, 'full_statement', False):
                    #print("NOINSTR2", n)
                    ans = super().visit_FuncDef(n)
            return ans
        else: # thread functions
            ans = super().visit_FuncDef(n)
            return ans
            
    def saveDeclarationIntoTypeGeneration(self, type, node): 
        #old checkForWriting in Antonio's code. Now it writes the struct declarations in the type file
        to_write = False
        # TODO that's the vanilla code (pre-lazy). It should be ok as it is just a declaration
        node_decl_vanilla = self.cGen_original.visit(node) 
        
        assert(type == 'TypeDecl' or type == 'FuncDecl' or type == 'PtrDecl' or type == 'ArrayDecl' or type == 'Struct', 'Invalid type: '+type)
        
        if self.scope == 'global':
            self.global_support_macro_declarations += node_decl_vanilla + ';\n'
        else:
            self.string_support_macro += node_decl_vanilla + ';\n'
            
    def visit_Assignment(self, n):
        #if not self.any_instrument or not (self.dr_on or self.abs_on):
        #    return self.macro_file_manager.expression(n, [super().visit_Assignment(n)], passthrough=not self.full_statement)
        rvalue_noinstr = self.cGen_original.visit(n.rvalue)
        lvalue_noinstr = self.cGen_original.visit(n.lvalue)
        '''if rvalue_noinstr.startswith("__cs_create("):
            # I should check whether the first argument has a valid bav
            extra_args_r = {"bavtest": n.rvalue.args.exprs[0]}
            if self.dr_on:
                extra_args_r['dr_vp_state'] = self.abs_dr_vpstate
            return self.cGen_original.visit(n.lvalue) + " = " + \
                    self.abs_dr_rules.rule_SpecialFuncCall(self.abs_dr_state, n.rvalue, self.abs_dr_mode['abs_mode'], self.abs_dr_mode['dr_mode'], self.full_statement, **extra_args_r)'''
        if lvalue_noinstr.startswith("__cs_staticlocalinit_") or (rvalue_noinstr.startswith("__cs_") and not rvalue_noinstr.startswith("__cs_local") and not rvalue_noinstr.startswith("__cs_staticlocal") and not rvalue_noinstr.startswith("__cs_retval") and not rvalue_noinstr.startswith("__cs_param")):
            lvalue_ni = self.visit_noinstr(n.lvalue, False)
            rvalue_ni = self.visit_noinstr(n.rvalue, False)
            return lvalue_ni + " " + n.op + " " + rvalue_ni
        extra_args = {}
        if self.dr_on:
            extra_args['dr_vp_state'] = self.abs_dr_vpstate
            extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
        return self.macro_file_manager.expression(n, self.do_rule('rule_Assignment',n, **extra_args), passthrough=not self.full_statement)
        
    def visit_BinaryOp(self, n):
        #if not self.any_instrument or not (self.dr_on or self.abs_on):
        #    return self.macro_file_manager.expression(n, [super().visit_BinaryOp(n)], passthrough=not self.full_statement)
        if n.op in ('||','&&'):
            extra_args = {}
            if self.dr_on:
                extra_args['dr_vp_state'] = self.abs_dr_vpstate
                extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
            return self.macro_file_manager.expression(n, self.do_rule('rule_OrAnd',n, **extra_args), passthrough=not self.full_statement)
        else:
            extra_args = {}
            if self.dr_on:
                extra_args['dr_vp_state'] = self.abs_dr_vpstate
                extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
            return self.macro_file_manager.expression(n, self.do_rule('rule_BinaryOp', n, **extra_args), passthrough=not self.full_statement)
            
    def visit_UnaryOp(self, n):
        #if not self.any_instrument or not (self.dr_on or self.abs_on):
        #    return self.macro_file_manager.expression(n, [super().visit_UnaryOp(n)], passthrough=not self.full_statement)
        if n.op in ('--','++'):
            extra_args = {}
            if self.dr_on:
                extra_args['dr_vp_state'] = self.abs_dr_vpstate
                extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
            return self.macro_file_manager.expression(n, self.do_rule('rule_preOp', n, **extra_args), passthrough=not self.full_statement)
        elif n.op in ('p--','p++'):
            extra_args = {}
            if self.dr_on:
                extra_args['dr_vp_state'] = self.abs_dr_vpstate
                extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
            return self.macro_file_manager.expression(n, self.do_rule('rule_postOp', n, **extra_args), passthrough=not self.full_statement)
        elif n.op in ('+','-','~'):
            extra_args = {}
            if self.dr_on:
                extra_args['dr_vp_state'] = self.abs_dr_vpstate
                extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
            return self.macro_file_manager.expression(n, self.do_rule('rule_UnOp', n, **extra_args), passthrough=not self.full_statement)
        elif n.op in ('!',):
            extra_args = {}
            if self.dr_on:
                extra_args['dr_vp_state'] = self.abs_dr_vpstate
                extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
            return self.macro_file_manager.expression(n, self.do_rule('rule_NotOp', n, **extra_args), passthrough=not self.full_statement)
        elif n.op in ('&',):
            extra_args = {}
            if self.dr_on:
                extra_args['dr_vp_state'] = self.abs_dr_vpstate
                extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
            return self.macro_file_manager.expression(n, self.do_rule('rule_AddrOp', n, **extra_args), passthrough=not self.full_statement)
        elif n.op in ('*',):
            extra_args = {}
            if self.dr_on:
                extra_args['dr_vp_state'] = self.abs_dr_vpstate
                extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
            return self.macro_file_manager.expression(n, self.do_rule('rule_PtrOp', n, **extra_args), passthrough=not self.full_statement)
        elif n.op in ('sizeof',):
            extra_args = {}
            if self.dr_on:
                extra_args['dr_vp_state'] = self.abs_dr_vpstate
                extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
            return self.macro_file_manager.expression(n, self.do_rule('rule_Sizeof', n, **extra_args), passthrough=not self.full_statement)
        else:
            assert(False)
            #return super().visit_UnaryOp(n)
            
        
    def visit_ID(self, n):
        ans = super().visit_ID(n) # do the lazy... part
        if n.name in ("__dr_nondet_main_data", "__dr_nondet_main_i"): # TODO needed for ldv-races where they pass around a local var pointer, making it a global variable
            self._lazyseqnewschedule__globalMemoryAccessed = True
        if n.name in self.funcNames:
            # this is a function name or NULL: return verbatim
            return n.name
        if n.name == "NULL":
            return self.macro_file_manager.expression(n, [self.visit(c_ast.Constant("void*", "NULL"))], passthrough=not self.full_statement)
        if n.name[0] == "E" and n.name in ("EPERM", "ENOENT", "ESRCH", "EINTR", "EIO", "ENXIO", "E2BIG", "ENOEXEC", "EBADF", "ECHILD", "EAGAIN", "ENOMEM", "EACCES", "EFAULT", "ENOTBLK", "EBUSY", "EEXIST", "EXDEV", "ENODEV", "ENOTDIR", "EISDIR", "EINVAL", "ENFILE", "EMFILE", "ENOTTY", "ETXTBSY", "EFBIG", "ENOSPC", "ESPIPE", "EROFS", "EMLINK", "EPIPE", "EDOM", "ERANGE", "EDEADLK", "ENAMETOOLONG", "ENOLCK", "ENOSYS", "ENOTEMPTY", "ELOOP", "ENOMSG", "EIDRM", "ECHRNG", "EL2NSYNC", "EL3HLT", "EL3RST", "ELNRNG", "EUNATCH", "ENOCSI", "EL2HLT", "EBADE", "EBADR", "EXFULL", "ENOANO", "EBADRQC", "EBADSLT", "EBFONT", "ENOSTR", "ENODATA", "ETIME", "ENOSR", "ENONET", "ENOPKG", "EREMOTE", "ENOLINK", "EADV", "ESRMNT", "ECOMM", "EPROTO", "EMULTIHOP", "EDOTDOT", "EBADMSG", "EOVERFLOW", "ENOTUNIQ", "EBADFD", "EREMCHG", "ELIBACC", "ELIBBAD", "ELIBSCN", "ELIBMAX", "ELIBEXEC", "EILSEQ", "ERESTART", "ESTRPIPE", "EUSERS", "ENOTSOCK", "EDESTADDRREQ", "EMSGSIZE", "EPROTOTYPE", "ENOPROTOOPT", "EPROTONOSUPPORT", "ESOCKTNOSUPPORT", "EOPNOTSUPP", "EPFNOSUPPORT", "EAFNOSUPPORT", "EADDRINUSE", "EADDRNOTAVAIL", "ENETDOWN", "ENETUNREACH", "ENETRESET", "ECONNABORTED", "ECONNRESET", "ENOBUFS", "EISCONN", "ENOTCONN", "ESHUTDOWN", "ETOOMANYREFS", "ETIMEDOUT", "ECONNREFUSED", "EHOSTDOWN", "EHOSTUNREACH", "EALREADY", "EINPROGRESS", "ESTALE", "EUCLEAN", "ENOTNAM", "ENAVAIL", "EISNAM", "EREMOTEIO", "EDQUOT", "ENOMEDIUM", "EMEDIUMTYPE", "ECANCELED", "ENOKEY", "EKEYEXPIRED", "EKEYREVOKED", "EKEYREJECTED", "EOWNERDEAD", "ENOTRECOVERABLE"):
            return self.macro_file_manager.expression(n, [self.visit(c_ast.Constant("int", n.name))], passthrough=not self.full_statement)
        extra_args = {}
        if self.dr_on:
            extra_args['dr_vp_state'] = self.abs_dr_vpstate
            extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
        if n.name in self.program_arrays:
            myans = self.do_rule('rule_ArrayID', n, **extra_args)
        else:
            myans = self.do_rule('rule_ID', n, **extra_args)
        return self.macro_file_manager.expression(n, myans, passthrough=not self.full_statement)
        
    def visit_Constant(self, n):
        extra_args = {}
        if self.dr_on:
            extra_args['dr_vp_state'] = self.abs_dr_vpstate
            extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
        return self.macro_file_manager.expression(n, self.do_rule('rule_Constant', n, **extra_args), passthrough=not self.full_statement)
        
    def visit_Cast(self, n):
        extra_args = {}
        if self.dr_on:
            extra_args['dr_vp_state'] = self.abs_dr_vpstate
            extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
        return self.macro_file_manager.expression(n, self.do_rule('rule_Cast', n, **extra_args), passthrough=not self.full_statement)
        
    def visit_ExprList(self, n):
        extra_args = {}
        if self.dr_on:
            extra_args['dr_vp_state'] = self.abs_dr_vpstate
            extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
        visit_ans = self.macro_file_manager.expression_comma(n, self.do_rule('rule_Comma', n, **extra_args), passthrough=not self.full_statement)
        self.expList = None if visit_ans[1] is None else visit_ans[1].copy()
        return visit_ans[0]
        
    def DRvisit_FuncCall(self, n):
        fref = n.name.name #self.frefVisit(n)
        
        
        # dr test if fref is a function pointer
        fptrVisit = None
        if fref in self.program_pointers:
            with self.dr_mode_set("ACCESS"):
                fptrVisit = self.visit_ID(n.name)
        
        # Visiting arguments
        visited_subexprs = []
        visited_subexprs_WSE = []
        #bak_dr_mode = self.abs_dr_mode['dr_mode']
        if n.args is not None:
            argsIdx = 0
            for expr in n.args.exprs:
                with self.abs_dr_mode_set("GET_VAL","TOP_ACCESS"):
                    expr_TOP_ACCESS = self._visit_expr(expr)
                
                    expr_InnerAccess = None
                    if self.dr_on and fref in ("scanf",) and argsIdx >= 1: # those functions will touch the second argument
                        expr_InnerAccess = self._visit_expr(c_ast.UnaryOp("*",expr))
                
                with self.abs_dr_mode_set("VALUE","WSE"):
                    expr_WSE = self._visit_expr(expr)
                
                expr_TA_W = expr_WSE if expr_TOP_ACCESS == "" else "("+expr_TOP_ACCESS+" ,"+expr_WSE+")"
                visited_subexprs.append(expr_TA_W)
                if expr_InnerAccess is not None:
                    visited_subexprs.append(expr_InnerAccess)
                visited_subexprs_WSE.append(expr_WSE)
                argsIdx += 1
        self.expList = visited_subexprs_WSE.copy()
        args =  ', '.join(visited_subexprs)
        
        
        #print("FREF: " + fref)
        #if fref == '__cs_safe_malloc': 
        #    print("ARGS: " + args)
        #    n.show()
        if fref == '__CSEQ_atomic_begin':
            if not self._lazyseqnewschedule__visit_funcReference:
                self._lazyseqnewschedule__atomic = True
            return ''
        elif fref == '__CSEQ_atomic_end':
            if not self._lazyseqnewschedule__visit_funcReference:
                self._lazyseqnewschedule__atomic = False
            return ''
        elif fref.startswith('__CSEQ_atomic_'):
            self._lazyseqnewschedule__globalMemoryAccessed = True
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
#            fName = args[:args.rfind(',')]
#            fName = fName[fName.rfind(',')+2:]
#            fName = fName.replace('&', '')
            fName = self.expList[2]
            fName = fName.strip()
            fName = fName.strip('()&')
            args = args + ', %s' % (self.Parser.threadOccurenceIndex[fName])

            self._lazyseqnewschedule__firstThreadCreate = True

        if fref == core.common.changeID['pthread_exit']:
            # 17 March 2021
            #threadIndex = self.Parser.threadIndex[self.__currentThread] if self.__currentThread in self.Parser.threadIndex else 0
            threadIndex = self.Parser.threadOccurenceIndex[self._lazyseqnewschedule__currentThread] if self._lazyseqnewschedule__currentThread in self.Parser.threadOccurenceIndex else 0
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
            threadIndex= self.Parser.threadOccurenceIndex[self._lazyseqnewschedule__currentThread] if self._lazyseqnewschedule__currentThread in self.Parser.threadOccurenceIndex else 0 # 17 March 2021
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

#        if fref == core.common.changeID['pthread_create']: # TODO re-write AST-based (see other modules)
#            self.addRetFuncCall(fref,args, self.Parser.threadOccurenceIndex[fName])
#        else:
        self.addRetFuncCall(fref,args)
        #ret = fref + '(' + args + ')'
        #print("GMT: " + str(self.getGlobalMemoryTest() ))
        #print(ret)
        if fptrVisit is None:
            return fref + '(' + args + ')'
        else:
            return "("+fptrVisit+","+fref + "(" + args + "))"
        
    def visit_FuncCall(self, n):
        fref = self.cGen_original._parenthesize_unless_simple(n.name)
        
        extra_args = {}
        if self.dr_on:
            extra_args['dr_vp_state'] = self.abs_dr_vpstate
            extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
            
        if fref in ('__CSEQ_assert', '__CSEQ_assume', 'assert', 'assume_abort_if_not'):
            if fref in ("__CSEQ_assume",):
                n.name.name = "__CPROVER_assume"
            if fref in ("__CSEQ_assert",):
                n.name.name = "assert"
            return self.macro_file_manager.expression(n, self.do_rule('rule_Assert_Assume', n, **extra_args), passthrough=not self.full_statement)
        elif fref == 'sizeof':
            return self.macro_file_manager.expression(n, self.do_rule('rule_Sizeof', n, **extra_args), passthrough=not self.full_statement)
        elif fref == '__cs_safe_malloc':
            return self.macro_file_manager.expression(n, self.do_rule('rule_Malloc', n, **extra_args), passthrough=not self.full_statement)
        elif fref == '__CSEQ_nondet_int':
            return self.macro_file_manager.expression(n, self.do_rule('rule_Nondet', n, **extra_args), passthrough=not self.full_statement)
            
        ## all functions are either instrumentation ones or thread functions. Anyways, don't instrument
        parts = []
        #with BakAndRestore(self, 'full_statement', False): ???
        adr_abs_on_bak = {adr:adr.abs_on for adr in self.conf_adr}
        abs_dr_mode_bak = self.abs_dr_mode
        new_abs_dr_mode = [{'abs_mode':None, 'dr_mode':"ACCESS" if adr.dr_on else None} for adr in self.conf_adr]
        for adr in self.conf_adr:
            adr.abs_on = False
        with BakAndRestore(self, 'abs_dr_mode', new_abs_dr_mode):
            #if adr.dr_on:
            ans = self.DRvisit_FuncCall(n) #visit_with_absdr_args(state, n, abs_mode if self.abs_on else None, dr_mode if self.dr_on else None, full_statement=False, **kwargs)
            #else:
            #    ans = super().visit_FuncCall(n)
        for (adr,abs_on) in adr_abs_on_bak.items():
            adr.abs_on = abs_on
        return ans
        #return self.macro_file_manager.expression(n, parts, passthrough=not self.full_statement)
        

    def visit_ArrayRef(self, n):
        extra_args = {}
        if self.dr_on:
            extra_args['dr_vp_state'] = self.abs_dr_vpstate
            extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
        return self.macro_file_manager.expression(n, [k.replace("__cs_thread_index",self.fixArrayIndex("__cs_thread_index")) for k in self.do_rule('rule_ArrayRef', n, **extra_args)], passthrough=not self.full_statement) #TODO not for plain!


    def visit_TernaryOp(self, n):
        extra_args = {}
        if self.dr_on:
            extra_args['dr_vp_state'] = self.abs_dr_vpstate
            extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
        return self.macro_file_manager.expression(n, self.do_rule('rule_TernaryOp', n, **extra_args), passthrough=not self.full_statement)
                        
    def visit_StructRef(self, n):
        extra_args = {}
        #if n.type == "." and type(n.name) is c_ast.UnaryOp and n.name.op == '*' :
        #    n = c_ast.StructRef(n.name.expr, '->', n.field)
        if self.dr_on:
            extra_args['dr_vp_state'] = self.abs_dr_vpstate
            extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
        if n.type == "->":
            return self.macro_file_manager.expression(n, self.do_rule('rule_StructRefPtr', n, **extra_args), passthrough=not self.full_statement)
        else:
            return self.macro_file_manager.expression(n, self.do_rule('rule_StructRefVar', n, **extra_args), passthrough=not self.full_statement)
            
    def visit_Typedef(self, n):
        ans = super().visit_Typedef(n)
        for adr in self.conf_adr:
            adr.addTypedef(ans)
        return ans
        
    def visit_Goto(self, n):
        parts = []
        for adr in self.conf_adr:
            parts.append(("__CPROVER_assume(!"+adr.bap+")" if adr.underapprox else ";"))
        return self.macro_file_manager.expression(n, parts, passthrough=not self.full_statement, typlbl="GotoUnder") + ";" + super().visit_Goto(n)
        
    def getval_and_nodr(self, n):
        adr_dr_on_bak = {adr: adr.dr_on for adr in self.conf_adr}
        for adr in self.conf_adr:
            adr.dr_on = False
        new_abs_dr_mode = [{'abs_mode':"GET_VAL" if adr.abs_on else None, 'dr_mode':None} for adr in self.conf_adr]
        with BakAndRestore(self, 'abs_dr_mode', new_abs_dr_mode):
            with self.clean_cp_state():
                tr = self.visit(n)
        for (adr, dr_on) in adr_dr_on_bak.items():
            adr.dr_on = dr_on
        return tr
        
    def visit_Decl(self, n, no_type=False):
        if no_type:
            return n.name
        else:
            type_of_n = getType(n.type)
            assert(type_of_n == 'TypeDecl' or type_of_n == 'FuncDecl' or type_of_n == 'PtrDecl' or type_of_n == 'ArrayDecl' or type_of_n == 'Struct', 'Invalid type: '+type_of_n)
            
            if hasattr(n,'name') and n.name != None:
                self.saveDeclarationIntoTypeGeneration(type_of_n, n)
                
            if type_of_n == 'FuncDecl':
                assert(n.name != None, "Function declaration does not have a name")
                # store it as function name
                if n.name in ("pthread_create", "pthread_join", "malloc"):
                    return ""
                self.funcNames.append(n.name)
                self.visit(n.type)
                if hasattr(n.type.type.type, 'names'):
                    function_type = ' '.join(n.type.type.type.names)
                elif hasattr(n.type.type.type.type, 'names'):
                    function_type = ' '.join(n.type.type.type.type.names)
                else:
                    assert(False, "Invalid function type: "+n.name)
                assert(('void' in function_type) or n.name.startswith('__cs_'), "At this point in the chain, all functions are expected to be void or __cs...: "+n.name)
                if n.name.startswith('__CSEQ_atomic'):
                    self.visit(n.type.args)
                # Do not instrument func declarations (func declarations != func bodies)
                with self.no_any_instrument():
                    with BakAndRestore(self, 'full_statement', False):
                        #print("NOINSTR4", n)
                        ans = super().visit_Decl(n)
                    
            elif type_of_n == 'Struct':
                ans = self.visit_Struct(n.type)
                    
            elif type_of_n == 'Union':
                with self.no_any_instrument():
                    with BakAndRestore(self, 'full_statement', False):
                        #print("NOINSTR4", n)
                        ans = super().visit_Decl(n)
                
            elif type_of_n == 'TypeDecl': # Variable/Constant
                if hasattr(n, 'quals') and len(getattr(n, 'quals')) >= 1 and getattr(n, 'quals')[0] == 'const':
                    # constants
                    for i in range(len(self.conf_adr)):
                        self.conf_adr[i].store_DeclConst(self.abs_dr_state[i], n)
                    with self.no_any_instrument():
                        with BakAndRestore(self, 'full_statement', False):
                            #print("NOINSTR5", n)
                            ans = super().visit_Decl(n)
                        return ans #do not do anything else (they are ready now). This to avoid setting global consts in main
                else:
                    # Antonio's comment: struct when no typedef is specified
                    type_st = getType(n.type.type) if n.type.type else None
                    if type_st == 'Struct':
                        if n.type.type.name in self.integral_type_list:
                            #known struct type, don't declare content
                            n.type.type.decls = None
                        else:
                            self.integral_type_list.append(n.type.type.name)
                    elif (hasattr(n.type.type, 'names')): # Antonio's comment: variable case
                        qualifier = []
                        if hasattr(n, 'quals'):
                            qualifier = n.quals
                        type_of_var = n.type.type.names[0]
                        if n.name != None:
                            if len(qualifier) >= 1:
                                self.interest_variables_list[n.name] = qualifier[0] + ' ' + type_of_var
                            else:
                                self.interest_variables_list[n.name] = type_of_var
                        else:
                            assert(False, "Variable without name "+str(n)) #return original_exp
                    else:
                        assert(False, "This type condition is not expected in a TypeDecl: "+str(n)) #TODO it might be possible
                    with BakAndRestore(n,"init", None):
                        ans = super().visit_Decl(n)
            elif type_of_n in ('PtrDecl', 'ArrayDecl') :
                type_st = getType(n.type.type.type) if n.type.type.type else None
                #print(n, getType(n.type), getType(n.type.type), getType(n.type.type.type), getType(n.type.type.type.type))
                if type_st == 'Struct':
                    if n.type.type.type.name in self.integral_type_list:
                        #known struct type, don't declare content
                        n.type.type.type.decls = None
                    else:
                        self.integral_type_list.append(n.type.type.type.name)
                    type_of_arrptr = None
                elif getType(n.type) == "ArrayDecl" and getType(n.type.type) == "PtrDecl" and getType(n.type.type.type) == "TypeDecl" and getType(n.type.type.type.type) == "Struct":
                    if n.type.type.type.type.name in self.integral_type_list:
                        #known struct type, don't declare content
                        n.type.type.type.type.decls = None
                    else:
                        self.integral_type_list.append(n.type.type.type.type.name)
                    type_of_arrptr = n.type.type.type.type.name
                elif hasattr(n.type.type.type, 'names'): #array
                    type_of_arrptr = n.type.type.type.names[0]
                elif hasattr(n.type.type.type, 'name'): #This condition capture the following case: 'static struct device *__local_csmy_callback_dev'
                    type_of_arrptr = n.type.type.type.name 
                elif hasattr(n.type.type.type.type, 'names'): #pointer to array
                    type_of_arrptr = n.type.type.type.type.names[0]
                elif hasattr(n.type.type, 'names'): #variable case
                    assert(False, "This type condition represents a variable in a PtrDecl/ArrayDecl, and it is not expected: "+str(n))
                else:
                    with self.no_any_instrument():     
                        with BakAndRestore(self, 'full_statement', False):   
                            #print("NOINSTR6", n)
                            return super().visit_Decl(n)
                    #assert(False, "This type condition is not expected: "+str(n))
                
                if type_of_n == 'ArrayDecl' and type_st == 'Struct' and n.name != 'main' and n.type != 'FuncDecl':
                    self.interest_variables_list[n.name] = type_st
                    self.program_arrays.append(n.name)
                if type_of_n == 'ArrayDecl' and type_of_arrptr != None and n.name != 'main' and n.type != 'FuncDecl':
                    self.interest_variables_list[n.name] = type_of_arrptr
                    self.program_arrays.append(n.name)


                elif type_of_n == 'PtrDecl' and n.name != None:
                    self.interest_variables_list[n.name] = type_of_arrptr
                    self.program_pointers.append(n.name)
                
                if self.scope == 'global':
                    with self.no_any_instrument(): 
                        with BakAndRestore(self, 'full_statement', False):       
                            #print("NOINSTR6", n)
                            ans = super().visit_Decl(n)
                else:
                    with self.no_any_instrument(): 
                        with BakAndRestore(self, 'full_statement', False):  
                            #print("NOINSTR7", n)
                            n_copy = copy.copy(n)
                            n_copy.init = None
                            ans = super().visit_Decl(n_copy)
            else:
                assert(False, "Unknown declaration type: "+type_of_n)
            
            if n.bitsize: 
                #TODO Do I need to treat this?
                pass
            if n.init:
                #TODO
                init = ""
                if type_of_n == 'ArrayDecl':
                    init += ";"
                    for index, ass_exp in enumerate(n.init):
                        unary_exp = c_ast.ArrayRef(c_ast.ID(n.name), c_ast.Constant('int', str(index)))
                        assignment = c_ast.Assignment("=", unary_exp, ass_exp)
                        tr = self.getval_and_nodr(assignment)
                        init += tr + ';' + '\n'
                elif type_of_n in ('PtrDecl','TypeDecl'):
                    if type(n.init) is c_ast.InitList:
                        for exp in n.init.exprs:
                            str_ref = c_ast.ID(n.name)
                            for field in exp.name:
                                str_ref = c_ast.StructRef(str_ref,'.', field)
                            ass_exp = exp.expr
                            assignment = c_ast.Assignment("=", str_ref, ass_exp)
                            tr = self.getval_and_nodr(assignment)
                            init += tr + ';' + '\n'
                    else:
                        unary_exp = c_ast.ID(n.name)
                        ass_exp = n.init
                        assignment = c_ast.Assignment("=", unary_exp, ass_exp)
                        tr = self.getval_and_nodr(assignment)
                        if self.scope == 'global':
                            init += tr + ';' + '\n'
                        else:
                            init += "; " + tr + ';' + '\n'
                else:
                    assert(False, "Unexpected initializer for variable "+n.name+" with type_of_n = "+type_of_n)
                    
                if self.scope == 'global' and n.name != 'main':
                    self.global_var_initializations += init
                elif self.scope == 'local':
                    ans = ans + init
                    
            return ans
         
    # TODO integrate into lazy...    #self.macro_file_manager.expression(n, [], passthrough=not self.full_statement)
    def visit_If(self, n):
        assert(self.full_statement)
        #if not self.any_instrument or not (self.dr_on or self.abs_on):
        #    return super().visit_If(n)
        ifStart = self._lazyseqnewschedule__maxInCompound   # label where the if stmt begins

        s = 'if ('

        if n.cond:
            extra_args = {}
            if self.dr_on:
                extra_args['dr_vp_state'] = self.abs_dr_vpstate
                extra_args['atomic'] = self._lazyseqnewschedule__atomic or self.atomicLvl > 0
            #with BakAndRestore(self, 'full_statement', False):
            condition = self.macro_file_manager.expression(n.cond, self.do_rule('rule_IfCond', n, **extra_args), passthrough=not self.full_statement, typlbl="IfCond") #TODO: for plain we did rule_IfCond
            s += condition

        s += ')\n'
        assert(self.full_statement)
        stateThen = [ads.copy() for ads in self.abs_dr_state]
        stateElse = [ads.copy() for ads in self.abs_dr_state]
        self.abs_dr_state = stateThen
        thenblock = self._generate_stmt(n.iftrue, add_indent=True)
        assert(self.full_statement)
        elseLbl = "else_lbl_"+str(self.elseLblProgr)
        self.elseLblProgr += 1
        
        if n.iffalse: #there is else
            jmpElse = self.macro_file_manager.expression(n.cond, ["if("+adr.getBav1(n)+") {goto "+elseLbl+";}" if adr.underapprox else ";" for adr in self.conf_adr], passthrough=not self.full_statement, typlbl="JmpElse")
            thenblock = "{\n"+thenblock+"\n"+jmpElse+";}\n"
        else:
            resetBap = self.macro_file_manager.expression(n.cond, [adr.bap+" = "+adr.getBap1(n) if adr.underapprox else "(void) 0" for adr in self.conf_adr], passthrough=not self.full_statement, typlbl="ResetBap")
            thenblock = "{\n"+thenblock+"\n"+resetBap+";}\n"
            
        s += thenblock

        ifEnd = self._lazyseqnewschedule__maxInCompound   # label for the last stmt in the if block:  if () { block; }
        nextLabelID = ifEnd+1

        if n.iffalse:
            self.abs_dr_state = stateElse
            assert(self.full_statement)
            elseBlock = self._generate_stmt(n.iffalse, add_indent=True)
            assert(self.full_statement)
            resetBap = self.macro_file_manager.expression(n.cond, [adr.bap+" = "+adr.getBap1(n) if adr.underapprox else "(void) 0" for adr in self.conf_adr], passthrough=not self.full_statement, typlbl="ResetBap")
            elseBlock = "{\n"+elseLbl+":;"+"\n"+elseBlock+"\n"+resetBap+";}\n"

            elseEnd = self._lazyseqnewschedule__maxInCompound   # label for the last stmt in the if_false block if () {...} else { block; }

            if ifStart < ifEnd:
                #threadIndex = self.Parser.threadIndex[self.__currentThread] if self.__currentThread in self.Parser.threadIndex else 0
                # GUARD(%s,%s)
                if not self._lazyseqnewschedule__visit_funcReference:
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

            nextLabelID = elseEnd+1
            s += self._make_indent() + 'else\n'

            elseBlock = elseBlock.replace('{', '{ '+elseHeader, 1)
            s += elseBlock
            
            self.abs_dr_state = [stateThen[i].doMerge(stateThen[i], stateElse[i]) for i in range(len(stateThen))]

        header = ''

        if ifStart+1 < nextLabelID:
            #threadIndex = self.Parser.threadIndex[self.__currentThread] if self.__currentThread in self.Parser.threadIndex else 0
            # GUARD(%s,%s)
            if not self._lazyseqnewschedule__visit_funcReference:
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
        assert(self.full_statement)
        return header + s + self._make_indent() + footer
