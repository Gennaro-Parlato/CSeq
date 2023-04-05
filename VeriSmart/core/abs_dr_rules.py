from pycparser import c_ast
from pycparser.c_generator import CGenerator
from core.support_file import SupportFileManager
from pycparser.c_ast import BinaryOp
from core.var_simplifier import Cleaner
from collections import defaultdict, deque
import string
import os

class CPState:
    def __init__(self):
        # Constant propagation: <value> = it is already known without reading it; None = must read it
        self.cp_bav = None 
        self.cp_bav_lhs = None 
        self.cp_bav_tmp = None 
        self.cp_bav1 = defaultdict(lambda: None)
        self.cp_bap1 = defaultdict(lambda: None)
        self.cp_bal = None 
        self.cp_bap = None 
        self.cp_dr = None 
        self.cp_wam = None 
        self.cp_wkm = None 
        
    def copy(self):
        # return a copy of this state
        newst = CPState()
        newst.cp_bav = self.cp_bav 
        newst.cp_bav_lhs = self.cp_bav_lhs 
        newst.cp_bav_tmp = self.cp_bav_tmp 
        newst.cp_bav1 = defaultdict(lambda: None)
        for k in self.cp_bav1:
            newst.cp_bav1[k] = self.cp_bav1[k]
        newst.cp_bap1 = defaultdict(lambda: None)
        for k in self.cp_bap1:
            newst.cp_bap1[k] = self.cp_bap1[k]
        newst.cp_bal = self.cp_bal 
        newst.cp_bap = self.cp_bap 
        newst.cp_dr = self.cp_dr 
        newst.cp_wam = self.cp_wam 
        newst.cp_wkm = self.cp_wkm 
        return newst
        
    def doMerge(self, stateThen, stateEls):
        #stores in this state the intersection of stateThen and stateEls, i.e., for each cp var keep them only if they constant propagated the same value, otherwise None
        self.cp_bav = self.__mergeVar(stateThen.cp_bav, stateEls.cp_bav)
        self.cp_bav_lhs = self.__mergeVar(stateThen.cp_bav_lhs, stateEls.cp_bav_lhs) 
        self.cp_bav_tmp = self.__mergeVar(stateThen.cp_bav_tmp, stateEls.cp_bav_tmp) 
        self.cp_bav1 = defaultdict(lambda: None)
        for k in stateThen.cp_bav1:
            self.cp_bav1[k] = self.__mergeVar(stateThen.cp_bav1[k], stateEls.cp_bav1[k])
        self.cp_bap1 = defaultdict(lambda: None)
        for k in stateThen.cp_bap1:
            self.cp_bap1[k] = self.__mergeVar(stateThen.cp_bap1[k], stateEls.cp_bap1[k])
        self.cp_bal = self.__mergeVar(stateThen.cp_bal, stateEls.cp_bal) 
        self.cp_bap = self.__mergeVar(stateThen.cp_bap, stateEls.cp_bap) 
        self.cp_dr = self.__mergeVar(stateThen.cp_dr, stateEls.cp_dr) 
        self.cp_wam = self.__mergeVar(stateThen.cp_wam, stateEls.cp_wam) 
        self.cp_wkm = self.__mergeVar(stateThen.cp_wkm, stateEls.cp_wkm) 
        
    def __mergeVar(self, v1, v2):
        return v1 if v1==v2 else None
        
        
class VPState:
    def __init__(self):
        self.VP1required = False
        self.VP2required = False
        
    def __str__(self):
        return " ".join(("VP1r:",str(self.VP1required), "VP2r:",str(self.VP2required)))
        
    def __repr__(self):
        rpold = super().__repr__()
        return "["+rpold+"; "+self.__str__()+"]"
        
class AuxVars:
    def __init__(self):
        self.value_var_nodes = dict()
        self.all_vv = []
        self.concrete_vars = TypedHelperVars("__cs_typedvar_")
        
    def create(self, ast_node, typ, with_side_effect=False):
        assert(typ != "other")
        aux = AuxVars.AuxVar("__cs_valuevar_"+str(len(self.all_vv)), self.concrete_vars, typ=typ, with_side_effect=with_side_effect)
        self.all_vv.append(aux)
        self.value_var_nodes[ast_node] = aux
        
    def create_fake(self, ast_node, value):
        aux = AuxVars.AuxVar("__cs_valuevar_"+str(len(self.all_vv)), self.concrete_vars, fake=True, value=value)
        self.all_vv.append(aux)
        self.value_var_nodes[ast_node] = aux
        
    def write(self, ast_node, value, set_if_read=None, set_if_not_read=None):
        assert(ast_node in self.value_var_nodes)
        nd = self.value_var_nodes[ast_node]
        if set_if_read is None:
            set_if_read = lambda name, x: name+" = ("+x+")"
        if set_if_not_read is None:
            if nd.with_side_effect:
                set_if_not_read = lambda x: x
            else:
                set_if_not_read = lambda x: "((void) 0)"
        return nd.write(value, set_if_read, set_if_not_read)
        
    def read(self, ast_node):
        assert(ast_node in self.value_var_nodes)
        return self.value_var_nodes[ast_node].read()
        
    def get_var_decls(self):
        return [typ + " " + ", ".join(vrs)+";" for typ, vrs in self.concrete_vars.list_all().items()]
        
    def get_var_list(self):
        return [v for vrs in self.concrete_vars.list_all().values() for v in vrs]
        
    def get_macro_decls(self):
        return [l for v in self.all_vv for l in v.get_macro_decls()]
        
    def end_of_statement(self):
        self.concrete_vars.release_all_vars()
        
    class AuxVar:
        def __init__(self, name, concrete_vars, typ=None, fake=False, value=None, with_side_effect=False):
            self.name = name
            self.typ = typ
            self.fake = fake
            self.value = value
            self.is_written = value is not None
            self.reads = 0
            self.with_side_effect = with_side_effect
            self.concrete_vars = concrete_vars
            
        def write(self, val, set_if_read, set_if_not_read):
            #print(val, "previously", self.value)
            assert(not self.fake)
            assert(not self.is_written)
            self.value = val
            self.is_written = True
            self.did_replace_set_if_read = False
            self.macrovname = "xxxxxxxxxx"
            self.set_if_read = set_if_read("@@@@",self.macrovname)
            self.set_if_not_read = set_if_not_read(self.macrovname)
            return "SET_"+self.name+"("+val+")"
            
        def read(self):
            if self.fake:
                return self.value
            else:
                self.reads += 1
                if not self.did_replace_set_if_read and ((self.is_written and self.reads >= 2) or (self.with_side_effect and self.reads >= 1)):
                    self.this_var = self.concrete_vars.acquire(self.typ)
                    self.set_if_read = self.set_if_read.replace("@@@@", self.this_var)
                    self.did_replace_set_if_read = True
                return self.name
            
        def get_var_decls(self):
            if not self.fake and ((self.is_written and self.reads >= 2) or (self.with_side_effect and self.reads >= 1)):
                print(self.name, self.fake, self.is_written, self.reads, self.with_side_effect)
                return [self.typ+" "+self.this_var+";"]
            else: 
                return []
                
        def get_var_list(self):
            if not self.fake and ((self.is_written and self.reads >= 2) or (self.with_side_effect and self.reads >= 1)):
                return [self.this_var]
            else: 
                return []
                
        def get_macro_decls(self):
            if self.fake:
                return []
            elif self.is_written:
                if self.reads == 0:
                    return ["#define SET_"+self.name+"("+self.macrovname+") "+self.set_if_not_read]
                elif self.reads == 1 and not self.with_side_effect:
                    return ["#define SET_"+self.name+"("+self.macrovname+") "+self.set_if_not_read, "#define "+self.name+" ("+self.value+")"]
                else:   
                    return ["#define SET_"+self.name+"("+self.macrovname+") "+self.set_if_read, "#define "+self.name+" ("+self.this_var+")"]
            else: 
                assert(self.reads == 0)
                return []
        
class MacroFile:
    def __init__(self, fname, adr, debug):
        self.fname = os.path.abspath(fname)
        self.adr = adr
        self.conversions = dict() # macro_content -> (rule_progr, [conversion params... only if debug])
        self.list_conversions = [] # conversion of EXPR_0, EXPR_1, ...
        self.macroProgr = 0
        self.dbg_visitor = CGenerator() if debug else None
        
    def store_macro(self, macro_content, node, abs_mode, dr_mode):
        if len(macro_content) < 15:
            # short content, won't generate a macro
            return macro_content
        if "__cs_thread_index" in macro_content:
            # don't generate macro, otherwise __cs_thread_index won't be replaced correctly
            return macro_content
        if macro_content.startswith("EXPR_") and macro_content.endswith("()") and macro_content[5:-2].isdigit():
            # this is a known expression, just return it and save into conversions
            index = int(macro_content[5:-2])
            assert(not macro_content[4].isdigit())
            assert(not macro_content[-2].isdigit())
            expanded_macro_content = self.list_conversions[index]
            conv = self.conversions[expanded_macro_content]
            if self.dbg_visitor:
                conv_params = (self.dbg_visitor.visit(node), str(abs_mode), str(dr_mode))
                if conv_params not in conv[1]:
                    conv[1].append(conv_params)
            return macro_content
        
        if macro_content in self.conversions:
            conv = self.conversions[macro_content]
            if self.dbg_visitor:
                conv_params = (self.dbg_visitor.visit(node), str(abs_mode), str(dr_mode))
                if conv_params not in conv[1]:
                    conv[1].append(conv_params)
            return conv[0]
        else:
            rule_prog = "EXPR_"+str(self.macroProgr)+"()"
            self.macroProgr += 1
            if self.dbg_visitor:
                conv_params = (self.dbg_visitor.visit(node), str(abs_mode), str(dr_mode))
                self.conversions[macro_content] = (rule_prog, [conv_params])
            else:
                self.conversions[macro_content] = (rule_prog, )
            self.list_conversions += [macro_content]
            return rule_prog
        
    def save_get_path(self):
        for code in self.conversions:
            key = self.conversions[code][0]
            self.adr.cleaner.add_code_to_clean(key[:-2], code)
        self.adr.cleaner.do_clean_codes()
        clean_codes = self.adr.cleaner.get_clean_codes()
        output = self.adr.getAbstractionMacros()
        output = "#ifndef NULL\n#define NULL 0\n#endif\n#ifndef bool\n#define bool _Bool\n#endif\n"+output.strip()+"\n"
        for macro_content in self.list_conversions:
            conv = self.conversions[macro_content]
            output += "\n"
            if self.dbg_visitor:
                output += "/*"+" ; ".join("("+c[0]+","+c[1]+","+c[2]+")" for c in conv[1])+"*/"
            trans = clean_codes[conv[0][:-2]]
            trans = trans.replace("(;)","((void)0)")
            if trans == ";":
                output += "\n#define "+conv[0]+" "+trans
            else:
                output += "\n#define "+conv[0]+" ("+trans+")"
        if len(output) > 0:
            with open(self.fname, "w") as f:
                f.write(output)
            return self.fname
        else:
            return None
            
class HelperVars:
    class Inner:
        def __init__(self, hv):
            self.hv = hv
            
        def __enter__(self):
            self.vname = self.hv.acquire()
            return self.vname
            
        def __exit__(self, *args):
            self.hv.release(self.vname)
            
    def __init__(self, prefix):
        self.prefix = prefix
        self.firstUnused = 0
        self.free = deque()
        
    def acquire(self):
        if len(self.free) > 0:
            return self.free.pop()
        else:
            name = self.prefix + str(self.firstUnused)
            self.firstUnused += 1
            return name
            
    def release(self, name):
        self.free.append(name)
            
    def __call__(self):
        return HelperVars.Inner(self)
        
    def list_all(self):
        return [self.prefix + str(i) for i in range(self.firstUnused)]
        
class TypedHelperVars: #TODO unire queste due classi
    class Inner:
        def __init__(self, hv, typ):
            self.hv = hv
            self.typ = typ
            
        def __enter__(self):
            self.vname = self.hv.acquire(typ)
            return self.vname
            
        def __exit__(self, *args):
            self.hv.release(self.vname, self.typ)
            
    def __init__(self, prefix):
        self.prefix = prefix
        self.firstUnused = {}
        self.firstUnusedAbsolute = {}
        self.free = {}
        
    def acquire(self, typ):
        if typ not in self.free:
            self.free[typ] = deque()
            self.firstUnused[typ] = 0
            self.firstUnusedAbsolute[typ] = 0
        if len(self.free[typ]) > 0:
            return self.free[typ].pop()
        else:
            name = self.prefix + typ.replace(" ","_") + "_" + str(self.firstUnused[typ])
            self.firstUnused[typ] += 1
            self.firstUnusedAbsolute[typ] = max(self.firstUnusedAbsolute[typ], self.firstUnused[typ])
            return name
            
    def release(self, name, typ):
        self.free[typ].append(name)
            
    def __call__(self, typ):
        return TypedHelperVars.Inner(self, typ)
        
    def list_all(self):
        return {typ:[self.prefix + typ.replace(" ","_") + "_" + str(i) for i in range(self.firstUnusedAbsolute[typ])] for typ in self.firstUnusedAbsolute}
        
    def release_all_vars(self):
        self.free = {typ: deque() for typ in self.free}
        self.firstUnused = {typ: 0 for typ in self.firstUnused}
        
        
class AbsDrRules:            
    def __init__(self, visitor, abs_on, dr_possible, code_contains_atomic, abstr_bits, supportFile, macroFileName, underapprox, debug=False):
        # visitor module
        self.visitor = visitor
        # abstraction active
        self.abs_on = abs_on
        # data race is possible
        self.dr_possible = dr_possible
        # underapproximation is active
        self.underapprox = underapprox
        # data race is on by default (if possible)
        self.dr_on = dr_possible
        self.code_contains_atomic = code_contains_atomic
        
        # abstraction: bit abstraction Value/Lvalue
        self.bav = "__cs_baV" if abs_on else None
        self.bal = "__cs_baL" if abs_on else None
        self.bav_lhs = "__cs_baV_lhs" if abs_on else None
        self.bav_tmp = "__cs_baV_tmp" if abs_on else None
        # underapprox: bit abstraction Path
        self.bap = "__cs_baP" if self.underapprox else None
        self.bap_passaround = "__cs_baP_passaround" if self.underapprox else None
        
        # abstraction: signed types for which abstraction is enabled
        self.abstrTypesSigned = ['int','signed','signed int','char','signed char','short','short int','signed short','signed short int',
            'long int','long','long long','long long int','signed long int','signed long','signed long long','signed long long int'] if abs_on else []
        
        
        # abstraction: unsigned types for which abstraction is enabled
        self.abstrTypesUnsigned = ['unsigned','unsigned int','unsigned char','unsigned short','unsigned short int','unsigned long', 
            'unsigned long int','unsigned long long int','size_t'] if abs_on else []
        
        # abstraction: sizeof of each abstractable type. TODO: use auxiliary file to get such values
        self.abstrTypesSizeof = {'int': 4,
                                   'signed': 4,
                                   'signed int': 4,
                                   'unsigned': 4,
                                   'unsigned int': 4,
                                   'char': 1,
                                   'signed char': 1,
                                   'unsigned char': 1,
                                   'short': 2,
                                   'short int': 2,
                                   'signed short': 2,
                                   'signed short int': 2,
                                   'unsigned short': 2,
                                   'unsigned short int': 2,
                                   'long int': 4,
                                   'long': 4,
                                   'long long': 8,
                                   'long long int': 8,
                                   'signed long int': 4,
                                   'signed long': 4,
                                   'signed long long': 8,
                                   'signed long long int': 8,
                                   'unsigned long': 4,
                                   'unsigned long int': 4,
                                   'unsigned long long int': 8,
                                   'size_t':2}
        # abstraction: nr of bits for abstracted vars
        self.abstr_bits = abstr_bits

        # bitvector types for multiplication
        self.unsigned_mul = dict() if abstr_bits is None else {k:"eint"+str(k*8-abstr_bits) for k in [1,2,4,8] if 8*k < 2*abstr_bits and abstr_bits < 8*k}
        self.unsigned_mul_1 = dict() if abstr_bits is None else {k:"eint"+str(k*8-abstr_bits+1) for k in [1,2,4,8] if 8*k < 2*abstr_bits and abstr_bits < 8*k}

        # abstraction: name field for abstraction
        self.sm_abs = "abstr" if abs_on else None
        
        # data race: data race detected
        self.dr = "__cs_dr" if dr_possible else None
        # data race: wrote all memory, i.e. if we wrote to an abstracted location
        self.wam = "__cs_wam" if dr_possible else None
        # data race: wrote known memory, i.e. if we wrote to a concrete location
        self.wkm = "__cs_wkm" if dr_possible else None
        
        # condition expressions, used in ifs and ternary ops
        self.conditions = {}
        self.conds_max = 0
        # for nondet expressions
        self.nondetvars = {}
        # bav1 expressions
        self.bav1s = {}
        self.bav1s_max = 0
        
        # bav helpers TODO try to use those as much as possible
        self.bavH = HelperVars("__cs_bavH_")
        # bap helpers TODO try to use those as much as possible
        self.bapH = HelperVars("__cs_bapH_")
        
        # bap1 expressions
        self.bap1s = {}
        self.bap1s_max = 0
        # bap1s for if
        self.bap1s_if = {} 
        self.bap1s_if_free = deque()
        self.bap1s_if_max = 0
        
        # abstraction: name field for dr
        self.sm_dr_all = "dr" if dr_possible else None
        self.sm_dr_noatomic = "dr_noatomic" if code_contains_atomic else None
        
        self.getsm_dr = lambda kwargs: self.sm_dr_noatomic if kwargs['atomic'] else self.sm_dr_all
        
        # support file to compute types
        self.supportFile = supportFile
        
        # macro file with instrumented code
        #self.macroFile = MacroFile(macroFileName, self, debug)
        
        # removes redundant assignments into instrumented code 
        self.cleaner = Cleaner()
        
        # SM setup for const declarations
        self.abs_const_decl = []

        # types for abstraction
        self.unsigned_bits = "uintb"
        self.signed_bits = "intb"
        self.unsigned_bits_1 = "uintb1" # + 1 bit
        self.signed_bits_1 = "intb1" # + 1 bit
        self.unsigned_bits_2x = "uint2b" # 2x bit
        self.signed_bits_2x = "int2b" # 2x bit
        self.unsigned_1 = "uint1"
        
        # extra vars for storing operation values
        self.auxvars = AuxVars()
        
        # helpvars for operations, eg + - *, to check if there's overflow
        self.helpvar_cnt = {}
        self.helpvar_max = {}
        
        self.any_size_t = False # true if size_t appears somewhere
        
    def end_of_statement(self):
        self.helpvar_cnt = {}
        self.bav1s = {} #TODO beware that without inlining there might be a sharing of bavs between different expressions!
        #self.bap1s_if = {} bap1s for ifs are kept between statements, can't reset automatically
        self.bap1s = {}
        self.conditions = {}
        self.auxvars.end_of_statement()
        
    def end_of_thread_function(self):
        self.bap1s_if = {} 
        self.bap1s_if_free = deque()
        self.bap1s_if_max = 0

    def get_help_var(self, typ):
        if typ not in self.helpvar_cnt:
            self.helpvar_cnt[typ] = 0
            if typ not in self.helpvar_max:
                self.helpvar_max[typ] = 0
        ans = "__cs_"+typ.replace(" ","_")+"_tmp_"+str(self.helpvar_cnt[typ])
        self.helpvar_cnt[typ] += 1
        self.helpvar_max[typ] = max(self.helpvar_max[typ], self.helpvar_cnt[typ])
        return ans
        
    def release_help_var(self, hv):
        pass #TODO

    def cast(self, expr, typ):
        return expr
        if typ is None:
            return expr
        else:
            return "(("+typ+")("+expr+"))"

    def cast_type(self, typ):
        if typ in self.abstrTypesSizeof and self.abstrTypesSizeof[typ]*8 > self.abstr_bits:
            return "intb" if typ in self.abstrTypesSigned else "uintb"
        else:
            return None
        
    def get_type_bounds(self, tp):
        sz = min(self.abstrTypesSizeof[tp], self.abstr_bits)
        signed = tp in self.abstrTypesSigned
        if signed:
            return (-2**(sz-1), 2**(sz-1)-1)
        else:
            return (0, 2**sz-1)
        
    # Test whether we can assign a assExpType to an unExprType according to abstraction
    def can_assign_unchecked(self, unExprType, assExpType):
        if not self.abs_on:
            return True
        if unExprType == 'other' or assExpType == 'other':
            return True
            
        signed_unExprType = unExprType in self.abstrTypesSigned
        signed_assExpType = assExpType in self.abstrTypesSigned
        sz_unExprType = self.abstrTypesSizeof[unExprType]*8
        sz_assExpType = self.abstrTypesSizeof[assExpType]*8
        
        #if signed:=unsigned and bitwidth reduced for abstraction, mandate a check
        if signed_unExprType and not signed_assExpType and (sz_unExprType > self.abstr_bits or sz_assExpType > self.abstr_bits):
            return False
        return True
        
    # Needed by Cleaner to parse the expressions
    def addTypedef(self, txt):
        self.cleaner.addTypedef(txt)
        
        # data race: p1, i.e., we need to discover writes
    def p1code(self, vpstate):
        assert(self.dr_on)
        vpstate.VP1required = True
        return "(__cs_dataraceDetectionStarted && !__cs_dataraceSecondThread && __cs_dataraceActiveVP1)"
        
        # data race: p2, i.e., we need to discover reads and writes
    def p2code(self, vpstate):
        assert(self.dr_on)
        vpstate.VP2required = True
        return "(__cs_dataraceSecondThread && __cs_dataraceActiveVP2)"
        
    def getVpstate(self, **kwargs):
        return kwargs['dr_vp_state']
        
    def aux_vars_decl(self):
        return self.compound_expr("\n",*([
            self.if_abs(lambda: "unsigned __CPROVER_bitvector[1] "+self.bav+" = 0;"),
            self.if_abs(lambda: "unsigned __CPROVER_bitvector[1] "+self.bal+" = 0;"),
            self.if_abs(lambda: "unsigned __CPROVER_bitvector[1] "+self.bav_lhs+" = 0;"),
            self.if_abs(lambda: "unsigned __CPROVER_bitvector[1] "+self.bav_tmp+" = 0;"),
            self.if_abs(lambda: "typedef unsigned __CPROVER_bitvector[1] "+self.unsigned_1+";"),
            self.if_abs(lambda: "typedef unsigned __CPROVER_bitvector["+str(self.abstr_bits)+"] "+self.unsigned_bits+";"),
            self.if_abs(lambda: "typedef __CPROVER_bitvector["+str(self.abstr_bits)+"] "+self.signed_bits+";"),
            self.if_abs(lambda: "typedef unsigned __CPROVER_bitvector["+str(self.abstr_bits+1)+"] "+self.unsigned_bits_1+";"),
            self.if_abs(lambda: "typedef __CPROVER_bitvector["+str(self.abstr_bits+1)+"] "+self.signed_bits_1+";"),
            self.if_abs(lambda: "typedef unsigned __CPROVER_bitvector["+str(self.abstr_bits*2)+"] "+self.unsigned_bits_2x+";"),
            self.if_abs(lambda: "typedef __CPROVER_bitvector["+str(self.abstr_bits*2)+"] "+self.signed_bits_2x+";"),
            #self.if_abs(lambda: self.unsigned_bits_1+" "+self.get_uintb1_var()+" = 0;"),
            self.if_ua(lambda: "unsigned __CPROVER_bitvector[1] "+self.bap_passaround+" = 0;"),
            self.if_dr_possible(lambda: "unsigned __CPROVER_bitvector[1] "+self.dr+" = 0;"),
            self.if_dr_possible(lambda: "unsigned __CPROVER_bitvector[1] "+self.wam+" = 0;"),
            self.if_dr_possible(lambda: "unsigned __CPROVER_bitvector[1] "+self.wkm+" = 0;"),
            self.if_dr_possible(lambda: 'unsigned __CPROVER_bitvector[1] __cs_dataraceDetectionStarted = 0;'),
            self.if_dr_possible(lambda: 'unsigned __CPROVER_bitvector[1] __cs_dataraceSecondThread = 0;'),
            self.if_dr_possible(lambda: 'unsigned __CPROVER_bitvector[1] __cs_dataraceNotDetected = 1;'),
            self.if_dr_possible(lambda: 'unsigned __CPROVER_bitvector[1] __cs_dataraceContinue = 1;'),
            self.if_dr_possible(lambda: 'unsigned __CPROVER_bitvector[1] __cs_dataraceActiveVP1 = 0;'),
            self.if_dr_possible(lambda: 'unsigned __CPROVER_bitvector[1] __cs_dataraceActiveVP2 = 0;'),
        #+[
        #    self.if_abs(lambda: t+" __cs_bf_"+t.replace(" ","_")+" = ("+t+") 0;") for t in self.abstrTypesSigned
        #] + 
        #[
        #    "typedef unsigned __CPROVER_bitvector["+self.unsigned_mul[k][4:]+"] "+self.unsigned_mul[k]+";" for k in self.unsigned_mul
        #] + [
        #    "typedef unsigned __CPROVER_bitvector["+self.unsigned_mul_1[k][4:]+"] "+self.unsigned_mul_1[k]+";" for k in self.unsigned_mul_1
        #] + [
        #    "typedef union {intb v; "+t+" o;} abstr_"+t.replace(" ","_")+";" for t in self.abstrTypesSigned if self.abstrTypesSizeof[t] * 8 > self.abstr_bits
        #] + [
        #    "typedef union {uintb v; "+t+" o;} abstr_"+t.replace(" ","_")+";" for t in self.abstrTypesUnsigned if self.abstrTypesSizeof[t] * 8 > self.abstr_bits and (t != "size_t" or self.any_size_t)
        ]))[0]
            
    '''def get_value_var_node_fake(self, node):
        # That's a fake variable (because we statically know that bav=1 at creation time): return "1"
        if node not in self.value_var_nodes:
            self.value_var_nodes[node] = ("1", None)
            
    def get_value_var_node(self, node, typ):
        if node in self.value_var_nodes:
            return self.value_var_nodes[node][0]
        else:
            assert(typ is not None)
            self.value_var_nodes[node] = ("__cs_valuevar_"+str(len(self.value_var_nodes)), typ)
            return self.value_var_nodes[node][0]'''

    def cond_vars_decl(self):
        return self.compound_expr("\n",*(['unsigned __CPROVER_bitvector[1] __cs_cond_'+str(v)+';' for v in range(self.conds_max)]))[0]
        
    def nondet_vars_decl(self):
        return self.compound_expr("\n",*([v[0]+' '+v[1]+';' for v in self.nondetvars.values()]))[0]
        
    def bav1_vars_decl(self):
        return self.compound_expr("\n",*(['unsigned __CPROVER_bitvector[1] __cs_bav1_'+str(v)+';' for v in range(self.bav1s_max)]+['unsigned __CPROVER_bitvector[1] '+x+';' for x in self.bavH.list_all()]))[0]
        
    def bap1_vars_decl(self):
        return self.compound_expr("\n",*(['unsigned __CPROVER_bitvector[1] __cs_bap1_'+str(v)+';' for v in range(self.bap1s_max)]+['unsigned __CPROVER_bitvector[1] '+x+';' for x in self.bapH.list_all()]
            ))[0]

    def extra_vars_decl(self):
        return self.compound_expr("\n",*(
            self.auxvars.get_var_decls()+
            [typ+" __cs_"+typ.replace(" ","_")+"_tmp_"+str(k)+";" for (typ, mx) in self.helpvar_max.items() for k in range(mx)]))[0]
            
    def reset_vars_stmt(self):
        return " = ".join(
            ["__cs_bap1_"+str(v) for v in range(self.bap1s_max)]+
            ["__cs_cond_"+str(v) for v in range(self.conds_max)]+
            ["__cs_bav1_"+str(v) for v in range(self.bav1s_max)]+
            ([self.bav, self.bal, self.bav_lhs, self.bav_tmp] if self.abs_on else [])+
            self.bavH.list_all()+
            self.bapH.list_all()+
            self.auxvars.get_var_list()+
            ["__cs_"+typ.replace(" ","_")+"_tmp_"+str(k) for (typ, mx) in self.helpvar_max.items() for k in range(mx)]+
            [" z 0"])+";"
        
            
        #[vvn[1]+" "+vvn[0]+" = 0;" for vvn in self.value_var_nodes.values() if vvn[1] is not None]))[0]
        
        
    def sm_field_decl(self):
        return "#define FIELD_DECLS() "+self.compound_expr(" ",*([
            self.if_abs(lambda: '__CPROVER_field_decl_global("'+self.sm_abs+'", (unsigned __CPROVER_bitvector[1])0);'),
            self.if_abs(lambda: '__CPROVER_field_decl_local("'+self.sm_abs+'", (unsigned __CPROVER_bitvector[1])0);'),
            self.if_dr_possible(lambda: '__CPROVER_field_decl_global("'+self.sm_dr_noatomic+'", (_Bool)0);' if self.code_contains_atomic else ""),
            self.if_dr_possible(lambda: '__CPROVER_field_decl_global("'+self.sm_dr_all+'", (_Bool)0);'),
            self.if_dr_possible(lambda: '__CPROVER_field_decl_local("'+self.sm_dr_noatomic+'", (_Bool)0);' if self.code_contains_atomic else ""),
            self.if_dr_possible(lambda: '__CPROVER_field_decl_local("'+self.sm_dr_all+'", (_Bool)0);'),
        ]+self.abs_const_decl))[0]
        
    def getAbstractionMacros(self):
        if self.abs_on:
            bitstr = str(self.abstr_bits)
            bitstr_1 = str(self.abstr_bits-1)
            power_t = 2**self.abstr_bits-1
            mask_t = hex(power_t)
            power_t_1 = 2**(self.abstr_bits-1)-1
            mask_t_1 = hex(power_t_1)
            return self.compound_expr("\n",*([
                self.sm_field_decl(),
            ] 
             +["#define MASK_"+t.replace(" ","_")+"_"+bitstr+" (("+t+") "+mask_t+")" for t in self.abstrTypesSigned]+
              ["#define MASK_"+t.replace(" ","_")+"_"+bitstr_1+" (("+t+") "+mask_t_1+")" for t in self.abstrTypesSigned]+
              ["#define invMASK_"+t.replace(" ","_")+"_"+bitstr_1+" (("+t+") "+hex((2**(8*self.abstrTypesSizeof[t])-1) - power_t_1)+")" for t in self.abstrTypesSigned]+
              #["#define BOUNDS_FAILURE_"+t.replace(" ","_")+"(exp) (((__cs_bf_"+t.replace(" ","_")+"=((exp)&~MASK_"+t.replace(" ","_")+"_"+bitstr_1+"))!=(~MASK_"+t.replace(" ","_")+"_"+bitstr_1+")) && __cs_bf_"+t.replace(" ","_")+")" for t in self.abstrTypesSigned]+
              ["#define BOUNDS_FAILURE_"+t.replace(" ","_")+"(exp) (((((exp)&invMASK_"+t.replace(" ","_")+"_"+bitstr_1+"))!=(invMASK_"+t.replace(" ","_")+"_"+bitstr_1+")) && ((exp)&invMASK_"+t.replace(" ","_")+"_"+bitstr_1+"))" for t in self.abstrTypesSigned]+
            #  ["#define ENCODE_"+t.replace(" ","_")+"(exp) ((exp)&MASK_"+t.replace(" ","_")+"_"+bitstr+")" for t in self.abstrTypesSigned]+
            #  #["#define ENCODE_"+t.replace(" ","_")+"(exp) (("+t+")((signed __CPROVER_bitvector["+bitstr+"]) (exp)))" for t in self.abstrTypesSigned]+
            #  ["#define DECODE_"+t.replace(" ","_")+"(exp) (("+t+")((signed __CPROVER_bitvector["+bitstr+"]) (exp)))" for t in self.abstrTypesSigned]+
            #  #["#define DECODE_"+t.replace(" ","_")+"(exp) (exp)" for t in self.abstrTypesSigned]+
            #  ["#define MIN_"+t.replace(" ","_")+" "+("((~(("+t+")0)) << "+bitstr_1+")" if self.abstr_bits < self.abstrTypesSizeof[t]*8 else "((~(("+t+")0)) << "+str(self.abstrTypesSizeof[t]*8-1)+")") for t in self.abstrTypesSigned]+
            #  ["#define MAX_"+t.replace(" ","_")+" "+"(~(MIN_"+t.replace(" ","_")+"))" for t in self.abstrTypesSigned]+
            #  ["#define ISMIN_"+t.replace(" ","_")+"(exp) "+"((exp) == MIN_"+t.replace(" ","_")+")" for t in self.abstrTypesSigned]+
            #  ["#define ISMAX_"+t.replace(" ","_")+"(exp) "+"((exp) == MAX_"+t.replace(" ","_")+")" for t in self.abstrTypesSigned]+
            #  
            #  
            # 
              ["#define MASK_"+t.replace(" ","_")+"_"+bitstr+" (("+t+") "+mask_t+")" for t in self.abstrTypesUnsigned]+
              ["#define invMASK_"+t.replace(" ","_")+"_"+bitstr+" (("+t+") "+hex((2**(8*self.abstrTypesSizeof[t])-1) - power_t)+")" for t in self.abstrTypesUnsigned]+
              ["#define BOUNDS_FAILURE_"+t.replace(" ","_")+"(exp) ((exp)&invMASK_"+t.replace(" ","_")+"_"+bitstr+")" for t in self.abstrTypesUnsigned]+
            #  ["#define ENCODE_"+t.replace(" ","_")+"(exp) ((exp)&MASK_"+t.replace(" ","_")+"_"+bitstr+")" for t in self.abstrTypesUnsigned]+
            #  #["#define ENCODE_"+t.replace(" ","_")+"(exp) (("+t+")((unsigned __CPROVER_bitvector["+bitstr+"]) (exp)))" for t in self.abstrTypesUnsigned]+
            #  ["#define DECODE_"+t.replace(" ","_")+"(exp) (("+t+")((unsigned __CPROVER_bitvector["+bitstr+"]) (exp)))" for t in self.abstrTypesUnsigned]+
            #  #["#define DECODE_"+t.replace(" ","_")+"(exp) (exp)" for t in self.abstrTypesUnsigned]+
            #  ["#define MIN_"+t.replace(" ","_")+" (("+t+")0)" for t in self.abstrTypesUnsigned]+
            #  ["#define MAX_"+t.replace(" ","_")+" "+("(~((~(("+t+")0)) << "+bitstr+"))" if self.abstr_bits < self.abstrTypesSizeof[t]*8 else "(~(("+t+")0))") for t in self.abstrTypesUnsigned]+
            #  ["#define ISMIN_"+t.replace(" ","_")+"(exp) "+"((exp) == MIN_"+t.replace(" ","_")+")" for t in self.abstrTypesUnsigned]+
            #  ["#define ISMAX_"+t.replace(" ","_")+"(exp) "+"((exp) == MAX_"+t.replace(" ","_")+")" for t in self.abstrTypesUnsigned]
                self.auxvars.get_macro_decls()
              ))[0]
        else:
            return self.compound_expr("\n",*([self.sm_field_decl()]+self.auxvars.get_macro_decls()))[0]
        
    def get_first_state(self):
        s = CPState()
        return s
        
    def enableDr(self):
        self.dr_on = True
        
    def disableDr(self):
        self.dr_on = False
        
    def store_content(self, full_statement, macro_content, node, abs_mode, dr_mode):
        # if full_statement -> compact macro, store it and return its code.
        # else -> return macro_content verbatim
        return macro_content
        if full_statement:
            return self.macroFile.store_macro(macro_content, node, abs_mode, dr_mode)
        else:
            return macro_content #.replace("___fakeifvar___ = ","")
        
    def void0(self):
        return "(void) 0"
        
    # apply constant propagation: if it is 0 or 1 => ifZero()/ifOne(), else ifNone()
    # default values: ifZero/ifOne -> lambda: "0"/"1", ifNone -> self.field
    def cp(self, state, field, ifZero=None, ifOne=None, ifNone=None):
        cpval = getattr(state, "cp_"+field)
        if cpval == 0:
            return "0" if ifZero is None else ifZero()
        elif cpval == 1:
            return "1" if ifOne is None else ifOne()
        else:
            return getattr(self, field) if ifNone is None else ifNone()
            
    def not_cp(self, state, field):
        cpval = getattr(state, "cp_"+field)
        if cpval == 0:
            return "1"
        elif cpval == 1:
            return "0"
        else:
            return "(!"+getattr(self, field)+")"
        
    # join parts to form a compound expression
    def compound_expr(self, jn, *items):
        clean_items = [x.strip() for x in items if x is not None and x.strip() != ""]
        joined = jn.join(clean_items)
        return joined, len(clean_items)
        
    # join parts to form a compound expression with lambda functions
    def compound_expr_lambda(self, jn, *items):
        allParts = [x() for x in items]
        parts = [x.strip() for x in allParts if x is not None and x.strip() != ""]
        return self.compound_expr(jn, *parts)
            
    # join parts to form a comma expression
    def comma_expr(self, *items):
        commas, parts = self.compound_expr(", ", items)
        if parts >=1 :
            return "(" + commas + ")"
        else:
            return commas
            
    # join parts to form a comma expression, with lambda functions
    def comma_expr_lambda(self, *items):
        commas, parts = self.compound_expr_lambda(", ", *items)
        if parts >=1 :
            return "(" + commas + ")"
        else:
            return commas
            
    # bracketed expression
    def brackets(self, item):
        return "("+item+")"
        
    # join parts to form an or expression
    def or_expr(self, *items):
        ors, parts = self.compound_expr(" || ", *items)
        if parts == 0:
            return "0"
        elif parts == 1:
            return ors
        else:
            return "(" + ors + ")"
    
    # apply cp to or expression, i.e., if any item is "1" return "1", remove "0"s
    def or_expr_prop(self, *items):
        if "1" in items:
            return "1"
        else:
            nonzero_items = tuple(x for x in items if x != "0")
            return self.or_expr(*nonzero_items)
            
    # apply cp to and expression, i.e., if any item is "0" return "0", remove "1"s
    def and_expr_prop(self, *items):
        if "0" in items:
            return "0"
        else:
            nonzero_items = tuple(x for x in items if x != "1")
            return self.and_expr(*nonzero_items)
        
    # join parts to form an and expression
    def and_expr(self, *items):
        ands, parts = self.compound_expr(" && ", *items)
        if parts == 0:
            return "1"
        elif parts == 1:
            return ands
        else:
            return "(" + ands + ")"
            
    # join parts to form a comma expression
    def comma_expr(self, *items):
        clean_items = [x for x in items if x != "" and x is not None]
        commas = ", ".join(clean_items)
        if len(clean_items) >=2 :
            return "(" + commas + ")"
        else:
            return commas
    
    # apply constant propagation in assignment, i.e., if val = "0"/"1" set state.cp_target = 0/1, else set state.cp_target = None
    def assign_with_prop(self, state, target, val):
        if val == str(getattr(state, "cp_"+target)) and val != "None":
            # value is the same as in cp: I don't even need to assign
            return ""
        if val == "0":
            setattr(state, "cp_"+target, 0)    
        elif val == "1":
            setattr(state, "cp_"+target, 1)   
        else:
            setattr(state, "cp_"+target, None)   
        return getattr(self, target) + " = " + val
        
    # apply constant propagation in assignment, i.e., if val = "0"/"1" set state.cp_target = 0/1, else set state.cp_target = None
    def assign_bav1_with_prop(self, state, target, val):
        if val == str(state.cp_bav1[target]) and val != "None":
            # value is the same as in cp: I don't even need to assign
            return ""
        if val == "0":
            state.cp_bav1[target] = 0
        elif val == "1":
            state.cp_bav1[target] = 1
        else:
            state.cp_bav1[target] = None
        return target + " = " + val
        
    # assignment disabling self propagation
    def assign(self, state, target, val):
        assert(hasattr(state, "cp_"+target))
        setattr(state, "cp_"+target, None)   
        return getattr(self, target) + " = " + val
        
    def assign_var(self, target, val):
        return target + " = " + val
        
    def nondet(self):
        #return "__VERIFIER_nondet_bool()"
        return "nondet_bool()" # TODO workaround for cbmc because the instrumenter does not operate on macro file
        
    def getsm(self, addr, field):
        return "__CPROVER_get_field("+addr+", \""+field+"\")"
        
    def setsm(self, addr, field, value):
        return "__CPROVER_set_field("+addr+", \""+field+"\", "+value+")"
    
    # return expr() if dr is on else ""        
    def if_dr(self, expr):
        return expr() if self.dr_on else ""
        
    # return expr() if dr is possible else ""        
    def if_dr_possible(self, expr):
        return expr() if self.dr_possible else ""
    
    # return expr() if abs is on else ""        
    def if_abs(self, expr):
        return expr() if self.abs_on else ""
    
    # return expr() if underapprox is on else ""        
    def if_ua(self, expr):
        return expr() if self.underapprox else ""
        
    # return expr() if underapprox is ff else ""        
    def if_no_ua(self, expr):
        return expr() if self.underapprox else ""
        
    # return expr() if abs is off else ""        
    def if_no_abs(self, expr):
        return "" if self.abs_on else expr()
        
    # return expr() if either abs or dr is off else ""     
    def if_abs_or_dr(self, expr):
        return expr() if self.abs_on or self.dr_on else ""
        
    def is_abstractable(self, xtype):
        ans = xtype in ('int',
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
                                   'unsigned short',
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
                                   'size_t') #TODO fill it properly
        return ans
        
    '''def decode(self, x, xtype):
        assert(self.abs_on)
        if self.is_abstractable(xtype):
            xtype_nospaces = xtype.replace(" ","_")
            return "DECODE_"+xtype_nospaces+"(("+xtype+")("+x+"))"
            #return "DECODE_"+xtype_nospaces+"(("+x+"))"
        else:
            return x
        
    def encode(self, x, xtype):
        assert(self.abs_on)
        if self.is_abstractable(xtype):
            xtype_nospaces = xtype.replace(" ","_")
            return "ENCODE_"+xtype_nospaces+"(("+xtype+")("+x+"))"
            #return "ENCODE_"+xtype_nospaces+"(("+x+"))"
        else:
            return "("+x+")"'''
        
    def ismin_type(self, x, xtype):
        # returns "ISMIN_xtype(x)"
        assert(self.abs_on and self.is_abstractable(xtype))
        xtype_nospaces = xtype.replace(" ","_")
        return "ISMIN_"+xtype_nospaces+"("+x+")"
        
    def ismax_type(self, x, xtype):
        # returns "ISMAX_xtype(x)"
        assert(self.abs_on and self.is_abstractable(xtype))
        xtype_nospaces = xtype.replace(" ","_")
        return "ISMAX_"+xtype_nospaces+"("+x+")"
        
    def bounds_failure(self, x, xtype):
        assert(self.abs_on and self.is_abstractable(xtype))
        xtype_nospaces = xtype.replace(" ","_")
        return "BOUNDS_FAILURE_"+xtype_nospaces+"(("+x+"))"
        
    def ternary_expr(self, state, cond, then, els):
        if cond == "0":
            return els(state)
        elif cond == "1":
            return then(state)
        else:
            stateThen = state.copy()
            stateEls = state.copy()
            expr_then = then(stateThen)
            expr_els = els(stateEls)
            if expr_then in ("()",""):
                expr_then = "((void)0)"
            if expr_els in ("()",""):
                expr_els = "((void)0)"
            ans = "((" + cond + ")?(" + expr_then + "):(" + expr_els + "))"
            state.doMerge(stateThen, stateEls)
            return ans
        
    def assert_expr(self, val):
        #return "__CSEQ_assert("+val+")"
        return "assert("+val+")"
        
    def assume_expr(self, val):
        return "__CPROVER_assume("+val+")"
        
    def fail_expr(self):
        return self.assert_expr("0")
        
    def cast_sign_check(self, v):
        return self.cast("("+v + " >> " + str(self.abstr_bits-1)+") & 1", self.unsigned_1)
        
    def assertDisabledIIFModesAreNone(self, abs_mode, dr_mode, **kwargs):
        impl = lambda a,b : not a or b
        iif = lambda a,b : (not a) == (not b)
        assert(impl(self.abs_on, abs_mode in ("SET_VAL", "GET_ADDR", "GET_VAL", "UPD_VAL")), "Invalid abstraction mode: "+str(abs_mode))
        assert(impl(not self.abs_on, abs_mode is None), "Abstraction is disabled but mode is not None: "+str(abs_mode))
        assert(impl(self.dr_on, dr_mode in ("ACCESS", "NO_ACCESS", "WSE")), "Invalid dr mode: "+str(dr_mode)) #LVALUE needed only to get the label. This is needed to keep both abstraction ad dr together without None values
        assert(impl(not self.dr_on, dr_mode is None), "Dr is disabled but mode is not None: "+str(dr_mode))
        assert(iif(self.dr_on, 'dr_vp_state' in kwargs), "IIF in dr mode, you need to pass a dr_vp_state")
    
    # Perform a visit using the visitor module, according to the enabled modes
    def visitor_visit(self, state, n, abs_mode, dr_mode, **kwargs):
        if type(n) is c_ast.FuncCall and self.dr_on and dr_mode != "WSE": #TODO check if abs & dr
            return ""
        ans = self.visitor.visit_with_absdr_args(state, n, self, abs_mode if self.abs_on else None, dr_mode if self.dr_on else None, full_statement=False, **kwargs)
        if isinstance(ans, list): ans = ans[0] # TODO this should always happen!
        ans = ans.strip()
        if ans == "()":
            return ""
        else:
            return ans
        
    # Perform a visit using the visitor module without any instrumentation
    def visitor_visit_noinstr(self, n):
        ans = self.visitor.visit_noinstr(n, full_statement=False)
        if isinstance(ans, list): ans = ans[0]
        return ans
        
    # check if is a cond var expression
    def is_cond_var(self, unExp):
        return type(unExp) is c_ast.ID and any(["__cz_tmp_"+x+"_cond_" in unExp.name for x in ["while","for","if"]])
        
        
    # reduced bitwidth operations
         
    def binary_op_of(self, a, op, b, dest, of):
        binary_ops = {'+':'add', '-':'sub', '*':'mul', '/':'div', '<<':'shl'}
        return "__CPROVER_"+binary_ops[op]+"_bits_overflow("+a+", "+b+", "+dest+", "+of+", "+str(self.abstr_bits)+")"
        
    def binary_op_only_of(self,a, op, b, of):
        binary_ops = {'+':'add', '-':'sub', '*':'mul', '/':'div', '<<':'shl'}
        return "__CPROVER_"+binary_ops[op]+"_bits_overflow_only("+a+", "+b+", "+of+", "+str(self.abstr_bits)+")"
        
    def binary_op_no_of(self, a, op, b, dest):
        binary_ops = {'+':'add', '-':'sub', '*':'mul', '/':'div', '<<':'shl', '|':'or', '^':'xor', '&':'and', '==':'eq', '!=':'neq', '<':'lt', '<=':'le', '>':'gt', '>=':'ge', '>>':'shr', '%':'mod'}
        return "__CPROVER_"+binary_ops[op]+"_bits("+a+", "+b+", "+dest+", "+str(self.abstr_bits)+")"
        
        
    def unary_op_of(self, op, a, dest, of):
        unary_ops = {'-':'unary_minus'}
        return "__CPROVER_"+unary_ops[op]+"_bits_overflow("+a+", "+dest+", "+of+", "+str(self.abstr_bits)+")"
        
    def unary_op_retval(self, op, a):
        unary_ops = {'-':'unary_minus'}
        return "__CPROVER_"+unary_ops[op]+"_bits_retval("+a+", "+str(self.abstr_bits)+")"
        
    def unary_op_only_of(self, op, a, of):
        unary_ops = {'-':'unary_minus'}
        return "__CPROVER_"+unary_ops[op]+"_bits_overflow_only("+a+", "+of+", "+str(self.abstr_bits)+")"
        
    def assign_abstr(self, name, val):
        return "__CPROVER_assign_bits("+val+", &("+name+"), "+str(self.abstr_bits)+")"
        
    def assign_abstr_1(self, name, val):
        return "__CPROVER_assign_bits("+val+", &("+name+"), 1)"
        
    def cut(self, expr):
        return "__CPROVER_cut_bits("+expr+", "+str(self.abstr_bits)+")"
        
    def visit_cut(self, state, expr, abs_mode, dr_mode, **kwargs):
        typ = self.supportFile.get_type(expr)
        val = self.visitor_visit(state, expr, abs_mode, dr_mode, **kwargs)
        if self.is_abstractable(typ):
            return self.cut(val)
        else:
            return val
        
    def nz(self, expr):
        return "__CPROVER_nz_bits("+expr+", "+str(self.abstr_bits)+")"
        
    def visit_nz(self, state, expr, abs_mode, dr_mode, **kwargs):
        if "negate" in kwargs and kwargs["negate"]:
            kwargs = kwargs.copy()
            del kwargs["negate"]
            isNeg = True
        else:
            isNeg = False
        typ = self.supportFile.get_type(expr)
        val = self.visitor_visit(state, expr, abs_mode, dr_mode, **kwargs)
        if self.is_abstractable(typ):
            if isNeg:
                return "!("+self.nz(val)+")"
            else:
                return self.nz(val)
        else:
            if isNeg:
                return "!("+val+")"
            else:
                return val
        
    def visit_nz_cond(self, state, expr, abs_mode, dr_mode, **kwargs):
        if self.is_cond_var(expr) and self.abs_on:
            return "__CPROVER_nz_bits("+expr.name+", 1)"
        else:
            return self.visit_nz(state, expr, abs_mode, dr_mode, **kwargs)
                
    def rule_preOp(self, state, preop, abs_mode, dr_mode, full_statement, **kwargs): # --x, ++x
        is_func_arg = kwargs.pop("func_arg", False)
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, preop, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, preop, abs_mode, "WSE", **kwargs)
                )), preop, abs_mode, dr_mode)
        unExp = preop.expr
        op = preop.op
        assert(op in ("--","++"))
        unExprType = self.supportFile.get_type(unExp) if self.abs_on else None
        assignee = c_ast.BinaryOp(op[-1], unExp, c_ast.Constant("int", "1"))
        if abs_mode in ("GET_VAL", None) and dr_mode in ("ACCESS", "PREFIX", "NO_ACCESS", None):
            fullOp = lambda: self.cast(self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs)+" "+op[-1]+" 1", self.cast_type(unExprType))
            intop = op[-1]
            
            ans1 = [
                self.if_abs_or_dr(lambda: self.visitor_visit(state, unExp, "UPD_VAL", "NO_ACCESS", **kwargs)),
                self.if_abs(lambda: self.__assignment_manual_bal_fail(state)),
                self.if_dr(lambda: self.__assignment_manual_cp_p1(state, unExp,unExprType, **kwargs)),
                self.if_dr(lambda: self.__assignment_manual_cp_p2(state, unExp,unExprType, **kwargs))
            ]
            if self.abs_on:
                if self.is_abstractable(unExprType):
                    with self.bavH() as bav1:
                        operation = self.binary_op_of(self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs), intop, "1", "&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", "&"+bav1)
                        bavSetParts = [self.cp(state, "bav"), self.if_ua(lambda: self.cp(state, "bap")), bav1]
                    ans2 = [
                        operation,
                        self.assign(state, "bav", self.or_expr_prop(*bavSetParts)),
                        self.setsm("&(("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+"))", self.sm_abs, self.cp(state, "bav"))
                    ]
                else:
                    ans2 = [
                        intop+intop+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs),
                        self.if_ua(lambda: self.setsm("&(("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+"))", self.sm_abs, self.or_expr_prop(self.cp(state, "bav"), self.cp(state, "bap"))))
                    ]
            else:
                ans2 = [self.visitor_visit(state, unExp, None, "WSE", **kwargs)+" = "+fullOp()]
            ans = self.comma_expr(*(ans1 + ans2))
            return self.store_content(full_statement,ans, preop, abs_mode, dr_mode)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE", None) and (abs_mode is not None or dr_mode is not None):
            return self.store_content(full_statement,self.visitor_visit(state, unExp, "VALUE", "WSE", func_arg = is_func_arg, **kwargs), preop, abs_mode, dr_mode)
        else:
            assert(False, "Invalid mode for preOp: abs_mode = "+str(abs_mode)+"; dr_mode = "+str(dr_mode))
            
    def rule_postOp(self, state, preop, abs_mode, dr_mode, full_statement, **kwargs): # --x, ++x
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, postop, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, postop, abs_mode, "WSE", **kwargs)
                )), postop, abs_mode, dr_mode)
        
        unExp = preop.expr
        op = preop.op
        assert(op in ("p--","p++"))
        assignee = c_ast.BinaryOp(op[-1], unExp, c_ast.Constant("int", "1"))
        unExprType = self.supportFile.get_type(unExp) if self.abs_on else None 
        fullOp = lambda: self.cast(self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs)+" "+op[-1]+" 1", self.cast_type(unExprType))
        if abs_mode in ("GET_VAL", None) and dr_mode in ("ACCESS", "PREFIX", "NO_ACCESS", None):
            intop = op[-1]
            if self.abs_on:
                if (not self.is_abstractable(unExprType)) or self.abstr_bits >= 8 * self.abstrTypesSizeof[unExprType]:
                    self.auxvars.create(preop, unExprType, True)
                else:
                    self.auxvars.create(preop, self.cast_type(unExprType), True)
            
            ans1 = [
                self.if_abs_or_dr(lambda: self.visitor_visit(state, unExp, "UPD_VAL", "NO_ACCESS", **kwargs)),
                self.if_abs(lambda: self.__assignment_manual_bal_fail(state)),
                self.if_dr(lambda: self.__assignment_manual_cp_p1(state, unExp,unExprType, **kwargs)),
                self.if_dr(lambda: self.__assignment_manual_cp_p2(state, unExp,unExprType, **kwargs))
            ]
            if self.abs_on:
                if self.is_abstractable(unExprType): 
                    save_old_val = self.auxvars.write(preop, self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs), self.assign_abstr)
                    with self.bavH() as bav1:
                        operation = self.binary_op_of(self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs), intop, "1", "&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", "&"+bav1)
                        bavSetParts = [self.cp(state, "bav"), self.if_ua(lambda: self.cp(state, "bap")), bav1]
                    ans2 = [
                        save_old_val,
                        operation,
                        self.assign(state, "bav", self.or_expr_prop(*bavSetParts)),
                        self.setsm("&(("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+"))", self.sm_abs, self.cp(state, "bav"))
                    ]
                else:
                    ans2 = [
                        self.auxvars.write(preop, self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs)),
                        self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+intop+intop,
                        self.if_ua(lambda: self.setsm("&(("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+"))", self.sm_abs, self.or_expr_prop(self.cp(state, "bav"), self.cp(state, "bap"))))
                    ]
            else:
                ans2 = [self.if_no_abs(lambda: self.visitor_visit(state, unExp, None, "WSE", **kwargs)+" = "+fullOp())] 
            ans = self.comma_expr(*(ans1+ans2))
            return self.store_content(full_statement,ans, preop, abs_mode, dr_mode)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE", None) and (abs_mode is not None or dr_mode is not None):
            if self.abs_on:
                ans = self.auxvars.read(preop)
            else:
                intop = op[-1]
                invertOp = "+" if intop == "-" else "-" #invert the operator to get access to the value before op
                ans = self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs)+" "+invertOp+" 1"
            return self.store_content(full_statement, ans, preop, abs_mode, dr_mode)
        else:
            assert(False, "Invalid mode for postOp: abs_mode = "+str(abs_mode)+"; dr_mode = "+str(dr_mode))
            
    def __arrayref_bavtmp_dr(self, state, dr_mode, postExp, exp, bav_tmp, **kwargs):
        # if dr_mode is NO_ACCESS/PREFIX: remove
        # if abstraction:
        # return (bav_tmp || bav)?(p2&&dr=(dr||wam||wkm)):(p2&&dr=(dr||wam||get_sm_dr(&[[postExp,VALUE,WSE]][ [[exp,VALUE,WSE]] ])))
        # else:
        # return p2&&dr=(dr||wam||get_sm_dr(&[[postExp,WSE]][ [[exp,WSE]] ]))
        assert(self.dr_on)
        ok = lambda state: self.and_expr(self.p2code(self.getVpstate(**kwargs)), self.brackets(self.assign_with_prop(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), 
            self.getsm("&("+self.brackets(self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs))+"["+self.visit_cut(state, exp, "VALUE", "WSE", **kwargs)+"])", self.getsm_dr(kwargs))))))
        err = lambda state: self.and_expr(self.p2code(self.getVpstate(**kwargs)), self.brackets(self.assign_with_prop(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), self.cp(state, "wkm")))))
        if dr_mode in ("NO_ACCESS", "PREFIX"):
            return ""
        elif self.abs_on:
            tmp_bav_cp = (bav_tmp, state.cp_bav)
            if tmp_bav_cp[0] == "1" or tmp_bav_cp[1] == 1: # True || x, x || True
                return ok(state)
            elif tmp_bav_cp[0] == "0" and tmp_bav_cp[1] == 0: # False || False
                return err(state)
            elif tmp_bav_cp[1] == 0: # ? || False
                return self.ternary_expr(state, self.cp(state, "bav"), err, ok)
            elif tmp_bav_cp[0] == "0": # False || ?
                return self.ternary_expr(state, bav_tmp, err, ok)
            else: # ? || ?
                return self.ternary_expr(state, self.or_expr(self.cp(state, "bav"),bav_tmp), err, ok)
        else:
            return ok(state)
            
    def __arrayref_bavtmp_abs(self, state, postExp, exp, bav_tmp, **kwargs):
        # return bav = ((bal = (bav_tmp || bav)) || get_sm_abs(&[[postExp,VALUE,WSE]] [ [[exp,VALUE,WSE]] ]))
        assert(self.abs_on)
        getsm = lambda: self.getsm("&("+self.brackets(self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs))+"["+self.visit_cut(state, exp, "VALUE", "WSE", **kwargs)+"])", self.sm_abs)
        tmp_bav_cp = (bav_tmp, state.cp_bav) #(bav_tmp || bav) as const propagation
        if tmp_bav_cp[1] == 1: # x || True
            return self.assign_with_prop(state, "bal", "1") 
        elif tmp_bav_cp[0] == "1": # True || (False/?)
            return self.comma_expr(self.assign_with_prop(state, "bal", "1"), self.assign_with_prop(state, "bav", "1")) 
        elif tmp_bav_cp[0] == "0" and tmp_bav_cp[1] == 0: #(False || False)
            return self.comma_expr(self.assign_with_prop(state, "bal", "0"), self.assign(state, "bav", getsm()))
        else: # (? || ?) (False || ?) (? || False)
            return self.assign(state, "bav", self.or_expr(self.assign(state,"bal",self.or_expr_prop(bav_tmp,self.cp(state,"bav"))),getsm())) 
        
            
    def rule_ArrayRef(self, state, arrexp, abs_mode, dr_mode, full_statement, **kwargs): # postExp[exp]
        is_func_arg = kwargs.pop("func_arg", False)
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, arrexp, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, arrexp, abs_mode, "WSE", **kwargs)
                )), arrexp, abs_mode, dr_mode)
        postExp = arrexp.name
        exp = arrexp.subscript
        if abs_mode in ("LVALUE", "VALUE", None) and dr_mode in ("WSE", None):
            return self.store_content(full_statement,self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs)+"["+self.visit_cut(state, exp, "VALUE", "WSE", **kwargs)+"]", arrexp, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL", "UPD_VAL", None) and dr_mode in ("ACCESS", "PREFIX", "NO_ACCESS", None):
            stmts = [self.if_abs_or_dr(lambda: self.visitor_visit(state, postExp, "GET_VAL", "PREFIX", **kwargs))]
            with self.bavH() as bav_tmp:
                stmts.append(self.if_abs(lambda: self.assign_var(bav_tmp, self.cp(state, "bav"))))
                cp_bav_tmp = self.cp(state, "bav", ifNone=lambda: bav_tmp)
                stmts.append(self.if_abs_or_dr(lambda: self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs)))
                stmts.append(self.if_dr(lambda: self.__arrayref_bavtmp_dr(state, dr_mode, postExp, exp, cp_bav_tmp, **kwargs)))
                stmts.append(self.if_abs(lambda: self.__arrayref_bavtmp_abs(state, postExp, exp, cp_bav_tmp, **kwargs)))
            return self.store_content(full_statement,self.comma_expr(*stmts), arrexp, abs_mode, dr_mode)
        elif abs_mode in ("SET_VAL", "GET_ADDR",) and dr_mode in ("PREFIX", "NO_ACCESS", None):
            stmts = [self.if_abs_or_dr(lambda: self.visitor_visit(state, postExp, "GET_VAL", "PREFIX", **kwargs))]
            with self.bavH() as bav_tmp:
                stmts.append(self.if_abs(lambda: self.assign_var(bav_tmp, self.cp(state, "bav"))))
                cp_bav_tmp = self.cp(state, "bav", ifNone=lambda: bav_tmp)
                stmts.append(self.if_abs_or_dr(lambda: self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs)))
                stmts.append(self.if_abs(lambda: self.assign_with_prop(state,"bal",self.or_expr_prop(cp_bav_tmp,self.cp(state,"bav")))))
            return self.store_content(full_statement, self.comma_expr(*stmts), arrexp, abs_mode, dr_mode)
        else:
            assert(False, "Invalid mode for ArrayRef: abs_mode = "+str(abs_mode)+"; dr_mode = "+str(dr_mode))
    
    def __structrefptr_bavtmp_dr(self, state, dr_mode, postExp, exp, **kwargs):
        # if dr_mode is NO_ACCESS/PREFIX: remove
        # if abstraction:
        # return (bav)?(p2&&dr=(dr||wam||wkm)):(p2&&dr=(dr||wam||get_sm_dr(&[[postExp,VALUE,WSE]][ [[exp,VALUE,WSE]] ])))
        # else:
        # return p2&&dr=(dr||wam||get_sm_dr(&([[postExp,WSE]]->exp)]))
        assert(self.dr_on)
        ok = lambda state: self.and_expr(self.p2code(self.getVpstate(**kwargs)), self.brackets(self.assign_with_prop(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), 
            self.getsm("&("+self.brackets(self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs))+"->"+exp.name+")", self.getsm_dr(kwargs))))))
        err = lambda state: self.and_expr(self.p2code(self.getVpstate(**kwargs)), self.brackets(self.assign_with_prop(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), self.cp(state, "wkm")))))
        if dr_mode in ("NO_ACCESS", "PREFIX"):
            return ""
        elif self.abs_on:
            if state.cp_bav == 1:
                return err(state)
            elif state.cp_bav == 0:
                return ok(state)
            else:
                return self.ternary_expr(state, self.cp(state, "bav"), err, ok)
        else:
            return ok(state)        
    
    def __structrefptr_bavtmp_abs(self, state, postExp, exp, **kwargs):
        # return  ((bal = bav), bav = bav || get_sm_abs(&([[postExp,VALUE,WSE]]->exp)))
        assert(self.abs_on)
        getsm = lambda: self.getsm("&("+self.brackets(self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs))+"->"+exp.name+")", self.sm_abs)
        cp = (state.cp_bal, state.cp_bav) #(bal, bav) as const propagation
        if cp[0] == 0 and cp[1] == 0: #bal = False, bav = False
            return self.assign_with_prop(state, "bav", getsm())
        elif cp[0] in (1, None) and cp[1] == 0: #bal = True/?, bav = False
            return self.comma_expr(self.assign_with_prop(state, "bal", self.cp(state, "bav")), self.assign_with_prop(state, "bav",  getsm()))
        elif cp[0] == 1 and cp[1] == 1: #bal = True, bav = True
            return ""
        elif cp[0] in (0, None) and cp[1] == 1: #bal = False/?, bav = True
            return self.assign_with_prop(state, "bal", self.cp(state, "bav"))
        elif cp[1] is None: #bal = False/True/?, bav = ?
            return self.comma_expr(self.assign_with_prop(state, "bal", self.cp(state, "bav")), self.assign_with_prop(state, "bav",  getsm()))
        else:
            assert(False)
            
    def rule_StructRefPtr(self, state, srexp, abs_mode, dr_mode, full_statement, **kwargs): # postExp->exp
        is_func_arg = kwargs.pop("func_arg", False)
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, srexp, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, srexp, abs_mode, "WSE", **kwargs)
                )), srexp, abs_mode, dr_mode)
        assert(srexp.type == "->")
        postExp = srexp.name
        fid = srexp.field
        if abs_mode in ("LVALUE", "VALUE", None) and dr_mode in ("WSE", None):
            return self.store_content(full_statement,self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs)+"->"+fid.name, srexp, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL", "UPD_VAL", None) and dr_mode in ("ACCESS", "PREFIX", "NO_ACCESS", None):
            return self.store_content(full_statement,self.comma_expr(
                self.if_abs_or_dr(lambda: self.visitor_visit(state, postExp, "GET_VAL", "ACCESS", **kwargs)),
                self.if_dr(lambda: self.__structrefptr_bavtmp_dr(state, dr_mode, postExp, fid, **kwargs)), 
                self.if_abs(lambda: self.__structrefptr_bavtmp_abs(state, postExp, fid, **kwargs))
            ), srexp, abs_mode, dr_mode)
        elif abs_mode in ("SET_VAL", "GET_ADDR",) and dr_mode in ("PREFIX", "NO_ACCESS", None):
            ans = self.comma_expr(
                self.if_abs_or_dr(lambda: self.visitor_visit(state, postExp, "GET_VAL", "ACCESS", **kwargs)),
                self.if_abs(lambda: self.assign_with_prop(state, "bal", self.cp(state, "bav")))
            )
            return self.store_content(full_statement,ans, srexp, abs_mode, dr_mode)
        else:
            assert(False, "Invalid mode for StructRefPtr: abs_mode = "+str(abs_mode)+"; dr_mode = "+str(dr_mode))
            
    def __structrefvar_bal_dr(self, state, dr_mode, postExp, exp, srexprType, **kwargs):
        # if dr_mode is NO_ACCESS/PREFIX: remove
        # if abstraction:
        # return (bal)?(p2&&dr=(dr||wam||wkm)):(p2&&dr=(dr||wam||get_sm_dr(&([[postExp,WSE]].exp)))
        # else:
        # return p2&&dr=(dr||wam||get_sm_dr(&([[postExp,WSE]].exp)))
        assert(self.dr_on)
        ok = lambda state: self.and_expr(self.p2code(self.getVpstate(**kwargs)), self.brackets(self.assign_with_prop(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), 
            self.getsm("&("+self.brackets(self.visitor_visit(state, postExp, "LVALUE", "WSE", **kwargs))+"."+exp.name+")", self.getsm_dr(kwargs))))))
        err = lambda state: self.and_expr(self.p2code(self.getVpstate(**kwargs)), self.brackets(self.assign_with_prop(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), self.cp(state, "wkm")))))
        if dr_mode in ("NO_ACCESS", "PREFIX"):
            return ""
        elif self.abs_on:
            if state.cp_bal == 1:
                return err(state)
            elif state.cp_bal == 0:
                return ok(state)
            else:
                return self.ternary_expr(state, self.cp(state, "bal"), err, ok)
        else:
            return ok(state)        
            
    def __structrefvar_bav_abs(self, state, postExp, exp, srexprType, **kwargs):
        # return (bal || bav = get_sm_abs(&([[postExp,VALUE,WSE]]->exp))) && (bav=1)
        assert(self.abs_on)
        getsm = lambda: self.getsm("&("+self.brackets(self.visitor_visit(state, postExp, "LVALUE", "WSE", **kwargs))+"."+exp.name+")", self.sm_abs)
        if state.cp_bal == 1:
            return self.assign_with_prop(state, "bav", "1")
        elif state.cp_bal == 0:
            return self.assign(state, "bav", getsm())
        elif state.cp_bal is None:
            return self.assign(state, "bav", self.or_expr(self.cp(state,"bal"),getsm()))
        else:
            assert(False)
            
    def rule_StructRefVar(self, state, srexp, abs_mode, dr_mode, full_statement, **kwargs): # postExp->exp
        is_func_arg = kwargs.pop("func_arg", False)
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, srexp, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, srexp, abs_mode, "WSE", **kwargs)
                )), srexp, abs_mode, dr_mode)
        assert(srexp.type == ".")
        postExp = srexp.name
        fid = srexp.field
        if abs_mode in ("LVALUE", "VALUE", None) and dr_mode in ("WSE", None):
            return self.store_content(full_statement,self.brackets(self.visitor_visit(state, postExp, "LVALUE", "WSE", **kwargs))+"."+fid.name, srexp, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL", "UPD_VAL", None) and dr_mode in ("ACCESS", "PREFIX", "NO_ACCESS", None):
            srexpType = self.supportFile.get_type(srexp) #"int" #TODO get type from expression
            return self.store_content(full_statement,self.comma_expr(
                self.if_abs_or_dr(lambda: self.visitor_visit(state, postExp, "GET_ADDR", "NO_ACCESS", **kwargs)),
                self.if_dr(lambda: self.__structrefvar_bal_dr(state, dr_mode, postExp, fid,srexpType, **kwargs)), 
                self.if_abs(lambda: self.__structrefvar_bav_abs(state, postExp, fid,srexpType, **kwargs))
            ), srexp, abs_mode, dr_mode)
        elif abs_mode in ("SET_VAL", "GET_ADDR",) and dr_mode in ("PREFIX", "NO_ACCESS", None):
            ans = self.if_abs_or_dr(lambda: self.visitor_visit(state, postExp, "GET_ADDR", "NO_ACCESS", **kwargs))
            return self.store_content(full_statement,ans, srexp, abs_mode, dr_mode)
        else:
            assert(False, "Invalid mode for StructRefVar: abs_mode = "+str(abs_mode)+"; dr_mode = "+str(dr_mode))
            
    def getCondition(self, cond):
        if cond not in self.conditions:
            self.conditions[cond] = "__cs_cond_"+str(len(self.conditions))
            self.conds_max = max(self.conds_max, len(self.conditions))
        return self.conditions[cond]
        
    def getNondetvar(self, ndfnc, typ="int"):
        if ndfnc not in self.nondetvars:
            self.nondetvars[ndfnc] = [typ, "__cs_nondet_v__"+str(len(self.nondetvars))]
        return self.nondetvars[ndfnc][1]
        
    def getNondetvarBv(self, ndfnc, nbits):
        # nondeterministic bitvector. If nbits = uXX -> unsigned bv[XX], else bv[XX]. This will be replaced in instrumenter to avoid cparser issues
        if ndfnc not in self.nondetvars:
            self.nondetvars[ndfnc] = ["char", "__cs_nondet_v_bv"+nbits+"_"+str(len(self.nondetvars))]
        return self.nondetvars[ndfnc][1]
        
    def getBav1(self, bop):
        if bop not in self.bav1s:
            self.bav1s[bop] = "__cs_bav1_"+str(len(self.bav1s))
            self.bav1s_max = max(self.bav1s_max, len(self.bav1s))
        return self.bav1s[bop]
        
        
    def getBap1(self, bop):
        if bop not in self.bap1s:
            self.bap1s[bop] = "__cs_bap1_"+str(len(self.bap1s))
            self.bap1s_max = max(self.bap1s_max, len(self.bap1s))
        return self.bap1s[bop]
        
    def getBap1If(self, bop):
        if bop not in self.bap1s_if:
            if len(self.bap1s_if_free) == 0:
                vname = "__cs_bap1_if_"+str(self.bap1s_if_max)
                self.bap1s_if_max += 1
            else:
                vname = self.bap1s_if_free.pop()
            self.bap1s_if[bop] = vname
        return self.bap1s_if[bop]
        
    def releaseBap1If(self, bop):
        self.bap1s_if_free.append(self.bap1s_if[bop])
        del self.bap1s_if[bop]
        
    def __ternary_underapprox(self, state, top, **kwargs):
        # returns (bap1 = bap, [lorExpr, GETVAL], bav1 = bav, bap = bap || bav, ((condchoice && then) || else)
        # where
        #   condchoice = (cond = bav||[lorExpr, VALUE]) {so that you do both then and else if lorExpr was not ok}
        #   then = ([expr, GETVAL], !bav1) {so that you fall though to else if lorExpr was not ok}
        #   else = ([condExpr, GETVAL], bap=bap1, bav=bav||bav1)
        #assert(self.underapprox and not self.dr) # dr still not ready
        lorExp = top.cond
        exp = top.iftrue
        condExp = top.iffalse
        condvar = self.getCondition(top)
        
        with self.bavH() as bav1: # TODO maybe optimize the scopes?
            with self.bapH() as bap1:
                then = lambda state: self.comma_expr(self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs), "!"+bav1)
                els = lambda state: self.comma_expr(self.visitor_visit(state, condExp, "GET_VAL", "ACCESS", **kwargs), 
                    self.assign_var(self.bap, bap1),
                    self.assign_with_prop(state, "bav", self.or_expr_prop(self.cp(state, "bav"), bav1))
                    )
                    
                parts = [
                    self.assign_var(bap1, self.cp(state, "bap")),
                    self.visitor_visit(state, lorExp, "GET_VAL", "ACCESS", **kwargs),
                    self.assign_var(bav1, self.cp(state, "bav")),
                    self.assign_with_prop(state, "bap", self.or_expr_prop(self.cp(state, "bap"), self.cp(state, "bav"))),
                    self.assign_var(condvar, self.or_expr_prop(self.cp(state, "bav"), self.visit_nz(state, lorExp, "VALUE", "WSE", **kwargs)))
                ]
                condChoice = parts[-1]
                stateThen = state.copy()
                stateEls = state.copy()
                expr_then = then(stateThen)
                expr_els = els(stateEls)
                if expr_then in ("()",""):
                    expr_then = "((void)0)"
                if expr_els in ("()",""):
                    expr_els = "((void)0)"
                state.doMerge(stateThen, stateEls)
                parts.append(self.or_expr(self.and_expr(condChoice,expr_then),expr_els))
        
        return self.comma_expr(*parts)
        
    def rule_TernaryOp(self, state, top, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, top, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, top, abs_mode, "WSE", **kwargs)
                )), top, abs_mode, dr_mode)
        lorExp = top.cond
        exp = top.iftrue
        condExp = top.iffalse
        if abs_mode is None and dr_mode is None:
            return self.store_content(full_statement,self.ternary_expr(state, self.visitor_visit(state, lorExp, None, None, **kwargs), \
                lambda state: self.visitor_visit(state, exp, None, None, **kwargs), \
                lambda state: self.visitor_visit(state, condExp, None, None, **kwargs)), top, abs_mode, dr_mode)
        elif abs_mode in ("VALUE",None) and dr_mode in ("WSE", None):
            return self.store_content(full_statement,self.ternary_expr(state, self.getCondition(top), 
                lambda state: (self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)), 
                lambda state: (self.visitor_visit(state, condExp, "VALUE", "WSE", **kwargs))), top, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","PREFIX","NO_ACCESS", None):
            if self.underapprox:
                trans = self.__ternary_underapprox(state, top, **kwargs)
            else:
                condvar = self.getCondition(top)
                trans = self.comma_expr(
                    self.visitor_visit(state, lorExp, "GET_VAL", "ACCESS", **kwargs),
                    self.if_abs(lambda: self.assign_var(condvar, self.ternary_expr(state, self.cp(state, "bav"), lambda state: self.getNondetvarBv(top, "u1"), lambda state: self.visit_nz(state, lorExp, "VALUE", "WSE", **kwargs)))),
                    self.if_no_abs(lambda: self.assign_var(condvar, self.visitor_visit(state, lorExp, "VALUE", "WSE", **kwargs))),
                    self.ternary_expr(state, condvar, 
                        lambda state: self.brackets(self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs)), 
                        lambda state: self.brackets(self.visitor_visit(state, condExp, "GET_VAL", "ACCESS", **kwargs)))
                )
            return self.store_content(full_statement, trans, top, abs_mode, dr_mode)
        else:
            assert(False)
    
    def __ptrop_dr(self, state, dr_mode, castExp, castExprType, **kwargs):
        # if dr_mode is NO_ACCESS/PREFIX: remove
        # if abstraction:
        # return (bav)?(p2&&dr=(dr||wam||wkm)):(p2&&dr=(dr||wam||get_sm_dr(*[[castExp,VALUE,WSE]]))
        # else:
        # return p2&&dr=(dr||wam||get_sm_dr(*[[castExp,VALUE,WSE]])
        assert(self.dr_on)
        ok = lambda state: self.and_expr(self.p2code(self.getVpstate(**kwargs)), self.brackets(self.assign_with_prop(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), 
            self.getsm("&("+self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs)+")", self.getsm_dr(kwargs))))))
        err = lambda state: self.and_expr(self.p2code(self.getVpstate(**kwargs)), self.brackets(self.assign_with_prop(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), self.cp(state, "wkm")))))
        if dr_mode in ("NO_ACCESS", "PREFIX"):
            return ""
        elif self.abs_on:
            if state.cp_bav == 1:
                return err(state)
            elif state.cp_bav == 0:
                return ok(state)
            else:
                return self.ternary_expr(state, self.cp(state, "bav"), err, ok)
        else:
            return ok(state)   
            
    def __ptrop_abs(self, state, castExp, **kwargs):
        # return bal = bav, bav = bav || get_sm_abs([[castExp,VALUE,WSE]])
        assert(self.abs_on)
        visit_val = lambda: self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs)
        getsm = lambda: self.assign(state, "bav", self.getsm(visit_val(), self.sm_abs))
        cp = (state.cp_bal, state.cp_bav) #(bal, bav) as const propagation
        if cp[0] == 0 and cp[1] == 0: #bal = False, bav = False
            return self.assign(state, "bal", getsm())
        elif cp[0] in (1, None) and cp[1] == 0: #bal = True/?, bav = False
            return self.comma_expr(self.assign_with_prop(state, "bal", self.cp(state, "bav")), self.assign(state, "bal", getsm()))
        elif cp[0] == 1 and cp[1] == 1: #bal = True, bav = True
            return ""
        elif cp[0] in (0, None) and cp[1] == 1: #bal = False/?, bav = True
            return self.assign_with_prop(state, "bal", self.cp(state, "bav"))
        elif cp[1] is None: #bal = False/True/?, bav = ?
            return self.comma_expr(self.assign_with_prop(state, "bal", self.cp(state, "bav")), self.assign(state, "bal", getsm()))
        else:
            assert(False)     
                    
    def rule_PtrOp(self, state, ptrop, abs_mode, dr_mode, full_statement, **kwargs):
        is_func_arg = kwargs.pop("func_arg", False)
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, ptrop, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, ptrop, abs_mode, "WSE", **kwargs)
                )), ptrop, abs_mode, dr_mode)
        assert(ptrop.op == '*')
        castExp = ptrop.expr
        if abs_mode is None and dr_mode is None:
            return self.store_content(full_statement,"*("+self.visitor_visit(state, castExp, None, None, **kwargs)+")", ptrop, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL","UPD_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS","PREFIX",None):
            castExpType = self.supportFile.get_type(castExp)
            return self.store_content(full_statement,self.brackets(self.comma_expr(
                self.visitor_visit(state, castExp, "GET_VAL", "ACCESS", **kwargs),
                self.if_dr(lambda:self.__ptrop_dr(state, dr_mode, castExp, castExpType, **kwargs)),
                self.if_abs(lambda:self.__ptrop_abs(state, castExp, **kwargs))
            )), ptrop, abs_mode, dr_mode)
        elif abs_mode in ("SET_VAL","GET_ADDR") and dr_mode in ("ACCESS","NO_ACCESS","PREFIX",None):
            return self.store_content(full_statement,self.comma_expr(
                self.visitor_visit(state, castExp, "GET_VAL", "ACCESS", **kwargs),
                self.assign_with_prop(state, "bal", self.cp(state, "bav"))
            ), ptrop, abs_mode, dr_mode)
        elif abs_mode in ("LVALUE", "VALUE", None) and dr_mode in ("WSE",None):
            return self.store_content(full_statement,"(*("+self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs)+"))", ptrop, abs_mode, dr_mode)
        else:
            assert(False)
            
    def rule_AddrOp(self, state, addrop, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, addrop, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, addrop, abs_mode, "WSE", **kwargs)
                )), addrop, abs_mode, dr_mode)
        assert(addrop.op == '&')
        castExp = addrop.expr
        if abs_mode is None and dr_mode is None:
            return self.store_content(full_statement,"&("+self.visitor_visit(state, castExp, None, None, **kwargs)+")", addrop, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS","PREFIX", None):
            return self.store_content(full_statement,self.comma_expr(
                self.visitor_visit(state, castExp, "GET_ADDR", "NO_ACCESS", **kwargs),
                self.if_abs(lambda: self.assign_with_prop(state, "bav", self.cp(state, "bal")))
            ), addrop, abs_mode, dr_mode)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            return self.store_content(full_statement,"&("+self.visitor_visit(state, castExp, "LVALUE", "WSE", **kwargs)+")", addrop, abs_mode, dr_mode)
        else:
            assert(False)
            
    def _not_getval(self, state, notop, **kwargs):
        # returns value = (([[castExp, GET_VAL, ACCESS]], bav) ? nondetbool(), :![[castexp, VALUE, WSE]]), bav = 0
        # and applies constant propagation
        castExp = notop.expr
        kw2 = kwargs.copy()
        kw2["negate"] = True
        ok = lambda state: self.visit_nz(state, castExp, "VALUE", "WSE", **kw2) 
        err = lambda state: self.getNondetvarBv(notop, "u1") # self.nondet()
        value = self.getCondition(notop)
        castexp_getval = self.visitor_visit(state, castExp, "GET_VAL", "ACCESS", **kwargs)
        if not self.abs_on:
        	return self.comma_expr(castexp_getval,self.assign_var(value, ok(state)))
        if state.cp_bav == 0:
            return self.comma_expr(
                castexp_getval, 
                self.assign_var(value, ok(state)))
        elif state.cp_bav == 1:
            return self.comma_expr(
                castexp_getval, 
                self.assign_var(value, err(state)),
                self.assign_with_prop(state,"bav","0"))
        elif state.cp_bav is None:
            return self.comma_expr_lambda(
                lambda: self.assign_var(value, self.ternary_expr(state, self.comma_expr(castexp_getval,self.bav), err, ok)),
                lambda: self.assign_with_prop(state,"bav","0")
            )
        else:
            assert(False)
            
            
    def rule_NotOp(self, state, notop, abs_mode, dr_mode, full_statement, **kwargs):
        is_func_arg = kwargs.pop("func_arg", False)
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, notop, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, notop, abs_mode, "WSE", **kwargs)
                )), notop, abs_mode, dr_mode)
        assert(notop.op == '!')
        castExp = notop.expr
        if abs_mode is None and dr_mode is None:
            return self.store_content(full_statement,"!("+self.visitor_visit(state, castExp, None, None, **kwargs)+")", notop, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","PREFIX","NO_ACCESS",None):
            if self.underapprox:
                value = self.getCondition(notop)
                kw2 = kwargs.copy()
                kw2["negate"] = True
                trans = self.assign_var(value, self.comma_expr(
                    self.visitor_visit(state, castExp, "GET_VAL", "ACCESS", **kwargs),
                    self.visit_nz(state, castExp, "VALUE", "WSE", **kw2) 
                ))
            else:
                trans = self._not_getval(state, notop, **kwargs)
            return self.store_content(full_statement, trans, notop, abs_mode, dr_mode)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            return self.getCondition(notop)
        else:
            assert(False)

    def rule_UnOp(self, state, unop, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, unop, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, unop, abs_mode, "WSE", **kwargs)
                )), unop, abs_mode, dr_mode)
        assert(unop.op in ('+','-','~'))
        castExp = unop.expr
        unOp = unop.op
        if abs_mode is None and dr_mode is None:
            return self.store_content(full_statement,unOp+"("+self.visitor_visit(state, castExp, None, None, **kwargs)+")", unop, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL", None) and dr_mode in ("ACCESS","PREFIX","NO_ACCESS",None):
            ans = [self.visitor_visit(state, castExp, "GET_VAL", "ACCESS", **kwargs)]
            castExprType = self.supportFile.get_type(castExp)
            if self.abs_on and self.is_abstractable(castExprType) and unOp == "-":
                castexp_visit = self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs)
                if self.cp(state,"bav") == "1":
                    #broken
                    self.auxvars.create_fake(unop, "0")
                elif self.cp(state,"bav") == "0":
                    #always ok
                    self.auxvars.create(unop, self.cast_type(castExprType), True)
                    state.cp_bav = None
                    ans.append(self.auxvars.write(unop, self.bav, lambda valuevar, of: self.unary_op_of(unOp, castexp_visit, "&"+valuevar, "&"+of), lambda of: self.unary_op_only_of(unOp, castexp_visit, "&"+of)))
                else:
                    with self.bavH() as bav1:
                        self.auxvars.create(unop, self.cast_type(castExprType), True)
                        ans.append(self.auxvars.write(unop, bav1, lambda valuevar, of: self.unary_op_of(unOp, castexp_visit, "&"+valuevar, "&"+of), lambda of: self.unary_op_only_of(unOp, castexp_visit, "&"+of)))
                        ans.append(self.assign(state, "bav", self.or_expr_prop(self.cp(state,"bav"), bav1)))
            return self.store_content(full_statement,self.comma_expr(*ans), unop, abs_mode, dr_mode)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            castExprType = self.supportFile.get_type(castExp)
            if self.abs_on and self.is_abstractable(castExprType):
                if unOp == "-":
                    ans = self.auxvars.read(unop)
                elif unOp == "~":
                    ans = self.unary_op_retval(unOp, self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs))
                elif unOp == "+":
                    ans = self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs)
                else:
                    assert(False)
            else:
                ans = unOp+"("+self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs)+")"
            return self.store_content(full_statement, ans, unop, abs_mode, dr_mode)
        else:
            assert(False)
            
    def rule_Sizeof(self, state, sizeof, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, sizeof, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, sizeof, abs_mode, "WSE", **kwargs)
                )), sizeof, abs_mode, dr_mode)
        assert(sizeof.op in ('sizeof',))
        unexp_type = sizeof.expr
        if abs_mode is None and dr_mode is None:
            return self.store_content(full_statement,"sizeof("+self.visitor_visit(state, unexp_type, None, None, **kwargs)+")", sizeof, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS",None):
            return self.store_content(full_statement,self.if_abs(lambda: self.assign_with_prop(state, "bav", "0")), sizeof, abs_mode, dr_mode)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            ans = "sizeof("+self.visitor_visit_noinstr(unexp_type)+")"
            return self.store_content(full_statement,ans, sizeof, abs_mode, dr_mode)
        else:
            assert(False)
            
    def rule_Comma(self, state, comma, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs) 
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, comma, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, comma, abs_mode, "WSE", **kwargs)
                )), comma, abs_mode, dr_mode)
        exps = comma.exprs
        if abs_mode is None and dr_mode is None:
            parts = [self.visitor_visit(state, x, None, None, **kwargs) for x in exps]
            return (self.store_content(full_statement,'('+', '.join([p if p != "" else "(void)0" for p in parts])+')', comma, abs_mode, dr_mode), parts) #This should be the only place where you need the second argument
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS",'PREFIX',None):
            parts = [self.visitor_visit(state, x, "GET_VAL", "NO_ACCESS", **kwargs) for x in exps[:-1]] + \
                [self.visitor_visit(state, exps[-1], "GET_VAL", ("NO_ACCESS" if dr_mode == "NO_ACCESS" else "ACCESS"), **kwargs)]
            return (self.store_content(full_statement,'('+', '.join([p if p != "" else "(void)0" for p in parts])+')', comma, abs_mode, dr_mode), None)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            return (self.store_content(full_statement,self.visitor_visit(state, exps[-1], "VALUE", "WSE", **kwargs), comma, abs_mode, dr_mode), None)
        else:
            assert(False)
            
    def __assert_assume_inner(self, state, exp, assexp, **kwargs):
        if not self.abs_on or state.cp_bav == 0:
            return self.visit_nz(state, exp, "VALUE", "WSE", **kwargs)
        elif state.cp_bav == 1:
            return self.getNondetvarBv(assexp, "u1")
        elif state.cp_bav is None:
            return self.ternary_expr(state, self.cp(state, "bav"),
                lambda state: self.getNondetvarBv(assexp, "u1"), 
                lambda state: self.visit_nz(state, exp, "VALUE", "WSE", **kwargs))
        else:
            assert(False)
            
    def __malloc_inner(self, state, **kwargs):
        # bav && fail()
        if not self.abs_on or state.cp_bav == 0:
            return ""
        elif state.cp_bav == 1:
            if self.underapprox:
                return self.assume_expr("0")
            else:
                return self.fail_expr()
        elif state.cp_bav is None:
            if self.underapprox:
                return self.assume_expr("!"+self.bav)
            else:
                return self.assert_expr("!"+self.bav)
        else:
            assert(False)
            
    def rule_Malloc(self, state, fullExpr, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs) 
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, fullExpr, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, fullExpr, abs_mode, "WSE", **kwargs)
                )), fullExpr, abs_mode, dr_mode)
        exp = fullExpr.args
        fncName = fullExpr.name.name
        if abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            malloc_type = "char *"
            #ans = self.get_value_var_node(fullExpr, malloc_type)
            ans = self.auxvars.read(fullExpr)
            return self.store_content(full_statement,ans, \
                fullExpr, abs_mode, dr_mode)
        
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("NO_ACCESS","ACCESS","PREFIX",None):
            malloc_type = "char *"
            #malloc_value = self.get_value_var_node(fullExpr, malloc_type)
            self.auxvars.create(fullExpr, malloc_type)
            return self.store_content(full_statement, \
                self.comma_expr(
                    self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs),
                    self.__malloc_inner(state, **kwargs),
                    self.auxvars.write(fullExpr, fncName+"("+self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)+")")
                    #self.assign_var(malloc_value, fncName+"("+self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)+")")
                ) \
            , fullExpr, abs_mode, dr_mode)
        else:
            assert(False)
            
    def rule_Return(self, state, fullExpr, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs) 
        assert(not self.dr_on, "Not implemented, see abstr_dr_common")
        if abs_mode in ("GET_VAL",None) and dr_mode in ("TOP_ACCESS", "ACCESS", None):
            if fullExpr.expr:
                getval = self.visitor_visit(state, fullExpr.expr, "GET_VAL", "ACCESS", **kwargs)
                
                ret_tp = self.supportFile.get_type(fullExpr.expr)
                if type(fullExpr.expr) in (c_ast.ArrayRef, c_ast.StructRef, c_ast.Constant, c_ast.ID, c_ast.Assignment) or (type(fullExpr.expr) is c_ast.UnaryOp and fullExpr.expr.op in ('*', '--','++')):
                    val = self.visitor_visit(state, fullExpr.expr, "VALUE", "WSE", func_arg=True, **kwargs)
                else:
                    val = self.visitor_visit(state, fullExpr.expr, "VALUE", "WSE", **kwargs)
                return "return "+self.comma_expr(getval, val)
            else:
                return "return"
        else:
            assert(False)
            
    def rule_FuncCall(self, state, fullExpr, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs) 
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, fullExpr, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, fullExpr, abs_mode, "WSE", **kwargs)
                )), fullExpr, abs_mode, dr_mode)
        exp = fullExpr.args
        fncName = fullExpr.name.name
        if abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            ans = self.auxvars.read(fullExpr)
            return self.store_content(full_statement,ans, fullExpr, abs_mode, dr_mode)
        
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("NO_ACCESS","ACCESS","PREFIX",None):
            ret_type = self.supportFile.get_type(fullExpr)
            auxvar_type = None
            if self.is_abstractable(ret_type) and ret_type in self.abstrTypesSizeof and self.abstrTypesSizeof[ret_type]*8 > self.abstr_bits:
                auxvar_type = "intb" if ret_type in self.abstrTypesSigned else "uintb"
            elif ret_type == "other":
                ret_type = kwargs['func_types'][fncName] if fncName in kwargs['func_types'] else "void"
                if ret_type != "void":
                    auxvar_type = ret_type
            if auxvar_type is not None:
                self.auxvars.create(fullExpr, auxvar_type, with_side_effect=True)
            
            #this allows to setup a different argument calling scheme (e.g, the extra arg of _cs_create), if argMap[i] is int, the i-th argument will be [[exp.exprs[i],VALUE]], else the i-th argument will be argMap[i].
            argMap = kwargs['argMap'] if 'argMap' in kwargs and kwargs['argMap'] is not None else ([i for i in range(len(exp.exprs))] if exp is not None else [])
            bav1 = self.getBav1(full_statement) if not fncName.startswith("__CSEQ_atomic") else None
            statements = []
            if not fncName.startswith("__CSEQ_atomic"): 
                statements.append(self.assign_var(bav1, "0"))
            for (arg_idx, aid) in enumerate(argMap):
                if isinstance(aid, int):
                    statements.append(self.visitor_visit(state, exp.exprs[aid], "GET_VAL", "ACCESS", **kwargs)) #TODO is ACCESS ok?
                    '''if 'pass_sm' in kwargs and kwargs['pass_sm'] and (self.abs_on or self.dr_on):
                        isstr = self.supportFile.is_struct(exp.exprs[aid])
                        if self.abs_on:
                            pa_varname = self.smpass_getPassaroundNameVar(fncName, arg_idx, self.sm_abs, isstr)
                            if isstr:
                                statements.append(pa_varname + " = " + self.visitor_visit(state, exp.exprs[aid], "VALUE", "WSE", **kwargs))
                            else:
                                statements.append(pa_varname + " = " + self.cp(state, "bav"))
                        if self.dr_on:
                            assert(False, "Not implemented") # TODO è un assegnamento fuori atomic (a meno di essere già in atomic)
                    '''
                    if not fncName.startswith("__CSEQ_atomic") and self.cp(state, "bav") != "0": 
                        statements.append(self.assign_var(bav1, self.or_expr_prop(bav1, self.cp(state, "bav"))))
                else:
                    pass
                    '''if 'pass_sm' in kwargs and kwargs['pass_sm'] and (self.abs_on or self.dr_on):
                        if self.abs_on:
                            pa_varname = self.smpass_getPassaroundNameVar(fncName, arg_idx, self.sm_abs, False)
                            statements.append(pa_varname + " = 0")
                        if self.dr_on:
                            assert(False, "Not implemented") # TODO è un assegnamento fuori atomic (a meno di essere già in atomic)
                    '''
            if not fncName.startswith("__CSEQ_atomic"): 
                statements.append(self.assign_with_prop(state,"bav", bav1))
                statements.append(self.__malloc_inner(state, **kwargs))
                if self.underapprox:
                    statements.append(self.assume_expr("!"+self.bap))
            '''if 'pass_sm' in kwargs and kwargs['pass_sm'] and (self.abs_on or self.dr_on):
                args = []
                for aid in argMap:
                    if isinstance(aid, int):
                        isstr = self.supportFile.is_struct(exp.exprs[aid])
                        arg_tp = self.supportFile.get_type(exp.exprs[aid])
                        if isstr:
                            args.append(self.smpass_getPassaroundNameVar(fncName, arg_idx, self.sm_abs, True))
                        elif not self.is_abstractable(arg_tp) or self.abstrTypesSizeof[arg_tp] * 8 <= self.abstr_bits:
                            args.append(self.visitor_visit(state, exp.exprs[aid], "VALUE", "WSE", **kwargs))
                        elif type(exp.exprs[aid]) in (c_ast.ArrayRef, c_ast.StructRef, c_ast.ID, c_ast.Assignment) or (type(exp.exprs[aid]) is c_ast.UnaryOp and exp.exprs[aid].op in ('*', '--','++')):
                            argtr = self.visitor_visit(state, exp.exprs[aid], "VALUE", "WSE", func_arg=True, **kwargs)
                            args.append(argtr)
                        else:
                            helpvar_tp = self.rule_Type(None, None, None, None, None, typ_txt = arg_tp)
                            helpvar = self.get_help_var(helpvar_tp)
                            statements.append(helpvar+" = "+self.visitor_visit(state, exp.exprs[aid], "VALUE", "WSE", **kwargs))
                            args.append(helpvar)
                    else:
                        args.append(aid)
            else:'''
            args = [self.visit_cut(state, exp.exprs[aid], "VALUE", "WSE", **kwargs) if isinstance(aid, int) else aid for aid in argMap]
            fncCallCode = fncName+"("+",".join(args)+")"
            if auxvar_type is None:
                statements.append(fncCallCode)
            elif (not self.is_abstractable(ret_type)) or self.abstr_bits >= 8 * self.abstrTypesSizeof[ret_type]:
                statements.append(self.auxvars.write(fullExpr, fncCallCode))
            else:
                statements.append(self.auxvars.write(fullExpr, fncCallCode, self.assign_abstr))
            
            return self.store_content(full_statement, \
                self.comma_expr(*statements) \
            , fullExpr, abs_mode, dr_mode)
        else:
            assert(False)
            
    def smpass_getPassaroundNameVar(self, funcname, idx, field,with_sm):
        assert(False)
        return "__"+("cz" if with_sm else "cs")+"_smpass__"+funcname+"__" + str(idx) + "__" + field

    def rule_SMpassDef(self, state, funcdef, abs_mode, dr_mode, full_statement, **kwargs):
        if self.abs_on or self.dr_on:
            out = ["main(void);"]
            if funcdef.type.args is not None:
                for (i, param) in enumerate(funcdef.type.args.params):
                    pname = param.name
                    isstr = self.supportFile.is_struct(c_ast.ID(pname))
                    passaround_type = self.supportFile.get_type(c_ast.ID(pname)) if isstr else self.unsigned_1
                    if self.abs_on:
                        out.append(passaround_type+" "+self.smpass_getPassaroundNameVar(funcdef.name, i, self.sm_abs,isstr)+";")
                    #if self.dr_on: # TODO: pensarci bene
                    #    out.append(passaround_type+" "+self.smpass_getPassaroundNameVar(funcdef.name.name, i, self.sm_dr_all)+";")
                    #    out.append(passaround_type+" "+self.smpass_getPassaroundNameVar(funcdef.name.name, i, self.sm_dr_noatomic)+";")
            return " ".join(out)[:-1]
        else:
            return "main(void)"
    def rule_SMpassAssignInFunc(self, state, funcdef, abs_mode, dr_mode, full_statement, **kwargs):
        assert(False)
        if self.abs_on or self.dr_on:
            out = []
            if funcdef.type.args is not None:
                for (i, param) in enumerate(funcdef.type.args.params):
                    pname = param.name
                    isstr = self.supportFile.is_struct(c_ast.ID(pname))
                    passaround_type = self.supportFile.get_type(c_ast.ID(pname)) if isstr else "char" #TODO will become unsigned bv[1]
                    orig_varname = self.visitor_visit(state, c_ast.ID(pname), "LVALUE", "WSE")
                    if self.abs_on:
                        pa_varname = self.smpass_getPassaroundNameVar(funcdef.name, i, self.sm_abs,isstr)
                        if isstr:
                            out.append(orig_varname + " = " + pa_varname + ";")
                        else:
                            out.append(self.setsm("&("+orig_varname+")", self.sm_abs, pa_varname)+";")
                    if self.dr_on:
                        assert(False, "Not implemented") # TODO è un assegnamento fuori atomic (a meno di essere già in atomic)
            return " ".join(out)
        else:
            return ""
            
    '''
    def rule_FuncCall(self, state, fullExpr, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs) 
        exp = fullExpr.args
        fncName = fullExpr.name.name
        print(fullExpr.args)
        if abs_mode in ("GET_VAL", None) and dr_mode in ("NO_ACCESS", "ACCESS", None):
            ans = fncName+"("+ \
                ", ".join(
                    self.comma_expr(self.visitor_visit(state, exp, abs_mode, "ACCESS", **kwargs), self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)) for exp in fullExpr.args
                ) \
            +")"
            return ans
            #return self.store_content(full_statement, ans, fullExpr, abs_mode, dr_mode)
        else:
            assert(False)'''
            
    def __assume_underapprox(self, state, exp, **kwargs):
        #assert(self.underapprox and not  self.dr_on)
        assert(self.underapprox)
        '''return self.assume_expr(self.and_expr_prop(self.not_cp(state, "bap"), 
            self.comma_expr(self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs),
                self.and_expr_prop(self.not_cp(state, "bav"), 
                    self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)))))'''
        return self.comma_expr(
            self.assume_expr(self.not_cp(state, "bap")), 
            self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs),
            self.assume_expr(self.and_expr_prop(self.not_cp(state, "bav"), 
                    self.visit_nz(state, exp, "VALUE", "WSE", **kwargs))))
                    
    def __assert_underapprox(self, state, exp, **kwargs):
        assert(self.underapprox and not self.dr_on)
        '''ans = self.comma_expr(self.assume_expr(self.and_expr_prop(self.not_cp(state, "bap"), 
            self.comma_expr(self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs),
                self.not_cp(state, "bav")))),
            self.assert_expr(self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)))
        return ans'''
        return self.comma_expr(
            self.assume_expr(self.not_cp(state, "bap")), 
            self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs),
            self.assume_expr(self.not_cp(state, "bav")),
            self.assert_expr(self.visit_nz(state, exp, "VALUE", "WSE", **kwargs)))
            
    def rule_Assert_Assume(self, state, fullExpr, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs) 
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, fullExpr, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, fullExpr, abs_mode, "WSE", **kwargs)
                )), fullExpr, abs_mode, dr_mode)
        exp = fullExpr.args
        fncName = fullExpr.name.name
        # TODO this is already done by the backend's instrumenter on the c file, but it does not act on the macro file. Therefore I'll do it now here
        if fncName in ("__CSEQ_assert", "assert", "__CPROVER_assert"):
            if  self.dr_possible:
                fncName = "__CPROVER_assume"
            else:
                fncName = "assert"
        elif fncName == "__CSEQ_assume":
            fncName = "__CPROVER_assume"
        if abs_mode in ("GET_VAL",None) and dr_mode in ("NO_ACCESS",None):
            if self.underapprox:
                if fncName in ("__CPROVER_assume", "assume_abort_if_not"):
                    trans = self.__assume_underapprox(state, exp, **kwargs)
                else:
                    trans = self.__assert_underapprox(state, exp, **kwargs)
            else:
                ce = self.comma_expr(
                        self.if_abs(lambda: self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs)),
                        self.__assert_assume_inner(state, exp, fullExpr, **kwargs)
                    )
                trans = fncName+"("+ ce +")"
            return self.store_content(full_statement, trans, fullExpr, abs_mode, dr_mode)
        else:
            assert(False)
            
    def rule_Fail(self, state, fullExpr, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs) 
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, fullExpr, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, fullExpr, abs_mode, "WSE", **kwargs)
                )), fullExpr, abs_mode, dr_mode)
        exp = fullExpr.args
        fncName = "assert"
        if abs_mode in ("GET_VAL",None) and dr_mode in ("NO_ACCESS",None):
            if self.underapprox:
                trans = self.comma_expr(
                    self.assume_expr(self.not_cp(state, "bap")),
                    self.assume_expr(self.not_cp(state, "bav")),
                    self.assert_expr("0"))
            else:
                trans = self.assert_expr("0")
            return self.store_content(full_statement, trans, fullExpr, abs_mode, dr_mode)
        else:
            assert(False)
            
    def fakeIfAssignment(self, n):
        return self.assign_var("___fakeifvar___", n)
        
    def __ifcond_underapprox(self, state, n, **kwargs):
        #assert(self.underapprox and not self.dr_on)
        exp = n.cond
        #bav1 = self.getBav1(n)
        bap1 = self.getBap1If(n)
        return self.comma_expr(
            self.assign_var(bap1, self.bap),
            self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs),
            #self.assign_var(bav1, self.bav),
            self.assign_with_prop(state,"bap",self.or_expr_prop(self.cp(state,"bap"), self.cp(state,"bav"))),
            self.or_expr_prop(self.cp(state,"bav"), self.visit_nz(state, exp, "VALUE", "WSE", **kwargs))
        )
            
    def rule_IfCond(self, state, n, abs_mode, dr_mode, full_statement, **kwargs):
        exp = n.cond
        if self.underapprox:
            trans = self.__ifcond_underapprox(state, n, **kwargs)
        elif not self.abs_on and not self.dr_on:
            trans = self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)
        else:
            exp_getval = self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs)
            exp_val = lambda state: self.visit_nz_cond(state, exp, "VALUE", "WSE", **kwargs)
            
            if state.cp_bav == 0:
                trans = self.comma_expr(exp_getval, exp_val(state))
            elif state.cp_bav == 1:
                trans = self.comma_expr(exp_getval, self.getNondetvarBv(n, "u1"))
            elif state.cp_bav is None:
                texp = self.ternary_expr(state, self.cp(state, "bav"),lambda state: self.getNondetvarBv(n, "u1"), exp_val)
                trans = self.comma_expr(exp_getval, texp)
            else:
                assert(False)
        return self.store_content(full_statement, self.fakeIfAssignment(trans), exp, abs_mode, dr_mode)
        
    def rule_ElseCond(self, state, n, abs_mode, dr_mode, full_statement, **kwargs):
        if self.underapprox:
            #that's ok doing GET_VAL once more because if conditions are stored in auxiliary vars (hence no side effects, see conditionextractor module)
            ans = "if("+self.comma_expr(self.visitor_visit(state, n, "GET_VAL", "NO_ACCESS", **kwargs), self.or_expr_prop(self.cp(state, "bav"), "!"+self.visitor_visit(state, n, "VALUE", "WSE", **kwargs)))+")" # TODO for dr do something else
            return self.store_content(full_statement, ans, n, abs_mode, dr_mode)
        else:
            return self.store_content(full_statement, "else", n, abs_mode, dr_mode)
    
    def rule_Cast(self, state, cast, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, cast, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, cast, abs_mode, "WSE", **kwargs)
                )), cast, abs_mode, dr_mode)
        unExpr = cast.expr
        toType = cast.to_type
        if abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            dest_tp = self.visitor_visit_noinstr(toType)
            sfType = self.supportFile.get_type(toType)
            
            if sfType in self.abstrTypesSizeof and self.abstrTypesSizeof[sfType]*8 > self.abstr_bits:
                dest_tp = "intb" if sfType in self.abstrTypesSigned else "uintb"

            ans = "("+dest_tp+") "+ self.visitor_visit(state, unExpr, "VALUE", "WSE", **kwargs)
            return self.store_content(full_statement, ans, cast, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS",'PREFIX',None):
            return self.store_content(full_statement,self.visitor_visit(state, unExpr, "GET_VAL", "NO_ACCESS" if dr_mode == "NO_ACCESS" else "ACCESS", **kwargs), cast, abs_mode, dr_mode)
        else:
            assert(False)

    def __binaryop_testbf(self, exp1, exp2, op):
        # returns 1 if (exp1 op exp2) overflows
        #op in '|','^','&','==','!=','<','<=','>','>=','<<','>>','+','-','*','/','%'
        # remaining '<<','>>','+','-','*'
        e1_op_e2_type = self.supportFile.get_type(fullOp)
        e1_type = self.supportFile.get_type(exp1)
        e2_type = self.supportFile.get_type(exp2)
        assume(self.is_abstractable(e1_op_e2_type))
        if op in ('|','^','&','==','!=','<','<=','>','>=','/','%'):
            return ""
        if op == "+":
            return "()" #str(self.abstr_bits)
        return ""
        
    def __binaryop_checks_and_val_new(self, state, node, exp1, exp2, op, e1_op_e2_type, e1_type, e2_type, of, **kwargs):
        # assign to value_var the value, and set of accordingly
        assert(op in ('|','^','&','==','!=','<','<=','>','>=','<<','>>','+','-','*','/','%'))
        if op in ('==','!=','<','<=','>','>='):
            visit1 = self.visit_cut(state, exp1, "VALUE", "WSE", **kwargs)
            visit2 = self.visit_cut(state, exp2, "VALUE", "WSE", **kwargs)
            self.auxvars.create(node, self.unsigned_1, with_side_effect=True)
            return (self.auxvars.write(node, "0", lambda valuevar, ofv: self.binary_op_no_of(visit1, op, visit2, "&"+valuevar)))
        elif self.__binaryop_op_can_overflow(op):
            visit1 = self.visit_cut(state, exp1, "VALUE", "WSE", **kwargs)
            visit2 = self.visit_cut(state, exp2, "VALUE", "WSE", **kwargs)
            self.auxvars.create(node, self.cast_type(e1_op_e2_type), with_side_effect=True)
            if of == self.bav:
                state.cp_bav = None
            return (self.auxvars.write(node, of, lambda valuevar, ofv: self.binary_op_of(visit1, op, visit2, "&"+valuevar, "&"+ofv), lambda ofv: self.binary_op_only_of(visit1, op, visit2, "&"+ofv)))
        else:
            visit1 = self.visit_cut(state, exp1, "VALUE", "WSE", **kwargs)
            visit2 = self.visit_cut(state, exp2, "VALUE", "WSE", **kwargs)
            self.auxvars.create(node, self.cast_type(e1_op_e2_type), with_side_effect=True)
            return (self.auxvars.write(node, "0", lambda valuevar, ofv: self.binary_op_no_of(visit1, op, visit2, "&"+valuevar)))
             

    def __binaryop_checks_and_val(self, state, node, exp1, exp2, op, e1_op_e2_type, e1_type, e2_type, **kwargs):
        # return two expressions: {'checks': (0 iif you can do the operation), 'val': (assign to value_var the value)} assuming that exp1 and exp2 are ok (i.e., their bav is 0)
        #value_var = self.get_value_var_node(node, e1_op_e2_type)
        
        if op in ("+", "-"):
            if not self.is_abstractable(e1_op_e2_type):
                return {'checks':'0', 'val':''}
            elif self.abstr_bits >= 8 * self.abstrTypesSizeof[e1_op_e2_type]:
                #value_var = self.get_value_var_node(node, e1_op_e2_type)
                self.auxvars.create(node, e1_op_e2_type)
                #return self.comma_expr(self.assign_var(value_var, "("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+")"), "0")
                val = "("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+")"
                return {'checks': '0', 'val': self.auxvars.write(node, val)}
            elif type(exp1) is c_ast.Constant and exp1.value == "1":
                vl_e2 = self.cast(self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs), self.signed_bits)
                if e1_op_e2_type in self.abstrTypesSigned:
                    vl_tot = self.cast("(1 "+op+" "+vl_e2+")", self.signed_bits)
                    #value_var = self.get_value_var_node(node, self.signed_bits)
                    self.auxvars.create(node, self.signed_bits)
                    extremeval = str(2**(self.abstr_bits-1)-1) if op == "+" else str(-2**(self.abstr_bits-1))
                    testValueOk = self.cast("("+vl_e2+"=="+self.cast(extremeval, self.signed_bits)+")", self.unsigned_1)
                    return {'checks': testValueOk, 'val': self.auxvars.write(node, vl_tot)}
                else:
                    vl_tot = self.cast("(1 "+op+" "+vl_e2+")", self.unsigned_bits)
                    #value_var = self.get_value_var_node(node, self.unsigned_bits)
                    self.auxvars.create(node, self.unsigned_bits)
                    extremeval = str(2**(self.abstr_bits)-1) if op == "+" else "0"
                    testValueOk = self.cast("("+vl_e2+"=="+self.cast(extremeval, self.unsigned_bits)+")", self.unsigned_1)
                    return {'checks': testValueOk, 'val': self.auxvars.write(node, vl_tot)}
            elif type(exp2) is c_ast.Constant and exp2.value == "1":
                vl_e1 = self.cast(self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs), self.signed_bits)
                if e1_op_e2_type in self.abstrTypesSigned:
                    vl_tot = self.cast("("+vl_e1+" "+op+" 1)", self.signed_bits)
                    #value_var = self.get_value_var_node(node, self.signed_bits)
                    self.auxvars.create(node, self.signed_bits)
                    extremeval = str(2**(self.abstr_bits-1)-1) if op == "+" else str(-2**(self.abstr_bits-1))
                    testValueOk = self.cast("("+vl_e1+"=="+self.cast(extremeval, self.signed_bits)+")", self.unsigned_1)
                    return {'checks': testValueOk, 'val': self.auxvars.write(node, vl_tot)}
                else:
                    vl_tot = self.cast("("+vl_e1+" "+op+" 1)", self.unsigned_bits)
                    #value_var = self.get_value_var_node(node, self.unsigned_bits)
                    self.auxvars.create(node, self.unsigned_bits)
                    extremeval = str(2**(self.abstr_bits)-1) if op == "+" else "0"
                    testValueOk = self.cast("("+vl_e1+"=="+self.cast(extremeval, self.unsigned_bits)+")", self.unsigned_1)
                    return {'checks': testValueOk, 'val': self.auxvars.write(node, vl_tot)}
            else:
                typ1 = self.signed_bits_1 if e1_op_e2_type in self.abstrTypesSigned else self.unsigned_bits_1
                typ = self.signed_bits if e1_op_e2_type in self.abstrTypesSigned else self.unsigned_bits
                sm = self.get_help_var("intb1") if e1_op_e2_type in self.abstrTypesSigned else self.get_help_var("uintb1")
                vl_tot_1 = self.cast("("+self.cast(self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs),typ1)+" "+op+" "+
                        self.cast(self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs),typ1)+")", typ1)
                #value_var = self.get_value_var_node(node, typ)
                self.auxvars.create(node, typ)
                testValueOk = self.cast("(("+sm+" >> ("+str(self.abstr_bits)+")) ^ ("+sm+" >> ("+str(self.abstr_bits-1)+")))", self.unsigned_1)
                return {'checks': testValueOk, 'val': self.comma_expr(
                    self.assign_var(sm, vl_tot_1),
                    self.auxvars.write(node, self.cast(sm, typ))
                )}
        elif op == "/":
            if not self.is_abstractable(e1_op_e2_type):
                return {'checks': '0', 'val': ''}
            if self.abstr_bits >= 8 * self.abstrTypesSizeof[e1_op_e2_type]:
                #value_var = self.get_value_var_node(node, e1_op_e2_type)
                self.auxvars.create(node, e1_op_e2_type)
                #return self.comma_expr(self.assign_var(value_var, "("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+")"), "0")
                val = "("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+")"
                return {'checks': '0', 'val': self.auxvars.write(node, val)}
            elif e1_op_e2_type not in self.abstrTypesSigned:
                #value_var = self.get_value_var_node(node, self.unsigned_bits)
                self.auxvars.create(node, self.unsigned_bits)
                vl_tot = self.cast(self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs), self.unsigned_bits)
                #return self.comma_expr(self.assign_var(value_var, vl_tot), "0")
                return {'checks': '0', 'val': self.auxvars.write(node, vl_tot)}
            #value_var = self.get_value_var_node(node, self.signed_bits)
            self.auxvars.create(node, self.signed_bits)
            vl_e1 = self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)
            vl_e2 = self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)
            vl_tot = self.cast(vl_e1+" "+op+" "+vl_e2, self.signed_bits)
            minval_1 = str(-2**(self.abstr_bits-1))
            runtime_check_1 = lambda: "("+vl_e1+" == " + self.cast(minval_1, self.signed_bits)+")"
            check_1 = None # None: do check runtime; True: is not minval_1 static; False: is minval_1 static
            if type(exp1) is c_ast.Constant and self.is_numeric_constant(exp1.value):
                check_1 = exp1.value != minval_1
            check_2 = None # None: do check runtime; True: is not -1 static; False: is -1 static
            runtime_check_2 = lambda: "("+vl_e2+" == " + self.cast("-1", self.signed_bits)+")"
            if type(exp2) is c_ast.Constant and self.is_numeric_constant(exp2.value):
                check_2 = exp2.value != "-1"

            #assign_vl_tot = self.assign_var(value_var, vl_tot)
            #assign_vl_tot = self.auxvars.write(node, vl_tot)
            if check_1 is None and check_2 is None:
                testValueOk = self.cast(runtime_check_1()+" && "+runtime_check_2(), self.unsigned_1)
                return {'checks': testValueOk, 'val': self.auxvars.write(node, vl_tot)}
            elif check_1 is True or check_2 is True:
                return {'checks': '0', 'val': self.auxvars.write(node, vl_tot)}
                #return self.comma_expr(assign_vl_tot, self.cast("0", self.unsigned_1))
            elif check_1 is False and check_2 is False:
                return {'checks': '1', 'val': self.auxvars.write(node, vl_tot)}
                #return self.comma_expr(assign_vl_tot, self.cast("1", self.unsigned_1))
            elif check_1 is None:
                #assign_vl_tot = self.auxvars.write(node, vl_tot)
                testValueOk = self.cast(runtime_check_1(), self.unsigned_1)
                return {'checks': testValueOk, 'val': self.auxvars.write(node, vl_tot)}
            else:
                #assign_vl_tot = self.auxvars.write(node, vl_tot)
                testValueOk = self.cast(runtime_check_2(), self.unsigned_1)
                return {'checks': testValueOk, 'val': self.auxvars.write(node, vl_tot)}
        elif op == "*":
            if not self.is_abstractable(e1_op_e2_type):
                return {'checks': '0', 'val': ''}
            if (not self.is_abstractable(e1_op_e2_type)) or self.abstr_bits >= 8 * self.abstrTypesSizeof[e1_op_e2_type]:
                #value_var = self.get_value_var_node(node, e1_op_e2_type)
                self.auxvars.create(node, e1_op_e2_type)
                #return self.comma_expr(self.assign_var(value_var, "("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+")"), "0")
                val = "("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+")"
                return {'checks': '0', 'val': self.auxvars.write(node, val)}
            if e1_op_e2_type in self.abstrTypesSigned:
                if 2 * self.abstr_bits > 8 * self.abstrTypesSizeof[e1_op_e2_type]:
                    # do it using (8*self.abstrTypesSizeof[e1_op_e2_type]) bits
                    mul = self.get_help_var(e1_op_e2_type)
                    #value_var = self.get_value_var_node(node, self.signed_bits)
                    self.auxvars.create(node, self.signed_bits)
                    vl_e1 = self.cast(self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs), e1_op_e2_type)
                    vl_e2 = self.cast(self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs), e1_op_e2_type)
                    vl_tot = self.cast(vl_e1+" "+op+" "+vl_e2, e1_op_e2_type)
                    bv_extra = self.unsigned_mul_1[self.abstrTypesSizeof[e1_op_e2_type]]
                    mul_shr = self.cast(mul + " >> " + str(self.abstr_bits-1), bv_extra)
                    testValueOk = self.cast("(("+mul_shr+") && " + self.cast("~("+mul_shr+")", bv_extra) + ")" ,self.unsigned_1)
                    return {'checks': testValueOk, 'val': self.comma_expr(
                        self.assign_var(mul, vl_tot),
                        self.auxvars.write(node, self.cast(mul, self.signed_bits)),
                    )}
                else:
                    # do it using (2 * self.abstr_bits) bits
                    mul = self.get_help_var("int2b")
                    #value_var = self.get_value_var_node(node, self.signed_bits)
                    self.auxvars.create(node, self.signed_bits)
                    
                    vl_e1 = self.cast(self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs), self.signed_bits_2x)
                    vl_e2 = self.cast(self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs), self.signed_bits_2x)
                    vl_tot_2x = self.cast(vl_e1+" "+op+" "+vl_e2, self.signed_bits_2x)
                    bv_extra = self.unsigned_bits_1
                    
                    mul_shr = self.cast(mul + " >> " + str(self.abstr_bits-1), bv_extra)
                    testValueOk = self.cast("(("+mul_shr+") && " + self.cast("~("+mul_shr+")", bv_extra)+")", self.unsigned_1)
                    return {'checks': testValueOk, 'val': self.comma_expr(
                        self.assign_var(mul, vl_tot_2x),
                        self.auxvars.write(node, self.cast(mul, self.signed_bits))
                    )}
            else:
                if 2 * self.abstr_bits > 8 * self.abstrTypesSizeof[e1_op_e2_type]:
                    # do it using (8*self.abstrTypesSizeof[e1_op_e2_type]) bits
                    mul = self.get_help_var(e1_op_e2_type)
                    #value_var = self.get_value_var_node(node, self.unsigned_bits)
                    self.auxvars.create(node, self.unsigned_bits)
                    vl_e1 = self.cast(self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs), e1_op_e2_type)
                    vl_e2 = self.cast(self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs), e1_op_e2_type)
                    vl_tot = self.cast(vl_e1+" "+op+" "+vl_e2, e1_op_e2_type)
                    
                    bv_extra = self.unsigned_mul[self.abstrTypesSizeof[e1_op_e2_type]]
                    testValueOk = self.cast("("+self.cast(mul + " >> " + str(self.abstr_bits), bv_extra)+")!=0", self.unsigned_1)
                    return {'checks': testValueOk, 'val': self.comma_expr(
                        self.assign_var(mul, vl_tot),
                        self.auxvars.write(node, self.cast(mul, self.unsigned_bits))
                    )}
                else:
                    # do it using (2 * self.abstr_bits) bits
                    mul = self.get_help_var("uint2b")
                    #value_var = self.get_value_var_node(node, self.unsigned_bits)
                    self.auxvars.create(node, self.unsigned_bits)
                    
                    vl_e1 = self.cast(self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs), self.unsigned_bits_2x)
                    vl_e2 = self.cast(self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs), self.unsigned_bits_2x)
                    vl_tot_2x = self.cast(vl_e1+" "+op+" "+vl_e2, self.unsigned_bits_2x)
                    
                    testValueOk = self.cast("("+mul + " >> " + str(self.abstr_bits)+")!=0", self.unsigned_1)
                    return {'checks': testValueOk, 'val': self.comma_expr(
                        self.assign_var(mul, vl_tot_2x),
                        self.auxvars.write(node, self.cast(mul, self.unsigned_bits))
                    )}
        elif op == "<<":
            if (not self.is_abstractable(e1_op_e2_type)) or self.abstr_bits >= 8 * self.abstrTypesSizeof[e1_op_e2_type]:
                #value_var = self.get_value_var_node(node, e1_op_e2_type)
                self.auxvars.create(node, self.e1_op_e2_type)
                #return self.comma_expr(self.assign_var(value_var, "("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+")"), "0")
                val = "("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+")"
                return {'checks': '0', 'val': self.auxvars.write(node, val)}
            if e1_op_e2_type in self.abstrTypesSigned:
                a = self.cast(self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs), e1_op_e2_type)
                b = self.cast(self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs), e1_op_e2_type)
                #value_var = self.get_value_var_node(node, self.signed_bits)
                self.auxvars.create(node, self.signed_bits)
                a_shl_b = "("+a+"<<"+b+")"
                sz_expr = self.abstrTypesSizeof[e1_op_e2_type] * 8
                mask1 = "((1 << ("+str(self.abstr_bits+1)+"+("+b+")))-1)" #((1 << (BITS+b+1))-1)
                mask2_bin = (("1"*sz_expr) + ("0"*(self.abstr_bits-1)))[-sz_expr:] # (~((1 << BITS-1)-1))
                mask2 = "0x%x"%int(mask2_bin,2)
                mask1_2 = "("+mask1+"&"+mask2+")" # mask1 & mask2
                part1 = a_shl_b + "&" + mask1_2
                part2 = "(~" + a_shl_b + ")&" + mask1_2
                vl_tot = self.cast(a_shl_b, self.signed_bits)
                testValueOk = self.cast("("+part1+")&&("+part2+")", self.unsigned_1)
                return {'checks': testValueOk, 'val': self.auxvars.write(node, vl_tot)}
            else:
                a = self.cast(self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs), e1_op_e2_type)
                b = self.cast(self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs), e1_op_e2_type)
                #value_var = self.get_value_var_node(node, self.unsigned_bits)
                self.auxvars.create(node, self.unsigned_bits)
                a_shl_b = "("+a+"<<"+b+")"
                asb_shr_bits = "("+a_shl_b+">>"+str(self.abstr_bits)+")"
                vl_tot = self.cast(a_shl_b, self.unsigned_bits)
                testValueOk = self.cast(asb_shr_bits+" != 0", self.unsigned_1)
                return {'checks': testValueOk, 'val': self.auxvars.write(node, vl_tot)}
        else:
            if (not self.is_abstractable(e1_op_e2_type)) or self.abstr_bits >= 8 * self.abstrTypesSizeof[e1_op_e2_type]:
                #value_var = self.get_value_var_node(node, e1_op_e2_type)
                self.auxvars.create(node, self.e1_op_e2_type)
                #return self.comma_expr(self.assign_var(value_var, "("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+")"), "0")
                val = "("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+")"
                return {'checks': '0', 'val': self.auxvars.write(node, val)}
            else:
                typ = self.signed_bits if e1_op_e2_type in self.abstrTypesSigned else self.unsigned_bits
                #a = self.cast(self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs), typ) #self.cast_sign_check(exp)
                #b = self.cast(self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs), typ)
                both_abstractable = self.is_abstractable(e1_type) and self.is_abstractable(e2_type)
                not_same_signedness = (1 if e1_type in self.abstrTypesSigned else 0) + (1 if e2_type in self.abstrTypesSigned else 0) == 1
                compare_op = op in ("<","<=",">",">=","!=","==")
                a = self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)
                b = self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)
                #value_var = self.get_value_var_node(node, typ)
                self.auxvars.create(node, typ)
                vl_tot = self.cast(a+" "+op+" "+b, typ)
                if both_abstractable and compare_op and not_same_signedness:
                    testValueOk = self.or_expr(self.cast_sign_check(a), self.cast_sign_check(b))
                    return {'checks': testValueOk, 'val': self.auxvars.write(node, vl_tot)}
                else:
                    return {'checks': '0', 'val': self.auxvars.write(node, vl_tot)} 
    
    def __binaryop_bav_and_val(self, state, exp1, exp2, op, fullOp, **kwargs):
        # returns (value_var = exp1 op exp2, bav = bav1 || bav || exp1 op exp2 fails)
        # and ensure that value_var is created in any case
        # using constant propagation     
        assert(self.abs_on)
        e1_op_e2_type = self.supportFile.get_type(fullOp) 
        e1_type = self.supportFile.get_type(fullOp.left) 
        e2_type = self.supportFile.get_type(fullOp.right) 
        bav1 = self.getBav1(fullOp)
        cp = (state.cp_bav, state.cp_bav1[bav1]) #(bav, bav_1) as const propagation
        if cp[0] == 1: #(True, x)
            #value_var = self.get_value_var_node_fake(fullOp)
            self.auxvars.create_fake(fullOp, "1")
            return ""
        if cp[1] == 1: #(x, True)
            #value_var = self.get_value_var_node_fake(fullOp)
            self.auxvars.create_fake(fullOp, "1")
            return self.assign_with_prop(state, "bav", "1")
        #e1_op_e2 = lambda: "("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+")"
        isAbs = self.is_abstractable(e1_op_e2_type)
        
        chk = self.__binaryop_checks_and_val(state, fullOp, exp1, exp2, op, e1_op_e2_type, e1_type, e2_type, **kwargs)
        if cp[0] == 0 and cp[1] == 0: #(False, False)
            return self.comma_expr(chk['val'], self.assign(state, "bav", chk['checks']))
        if cp[0] == 0: #(False, ?)
            return self.comma_expr(chk['val'], self.assign(state, "bav", self.or_expr(bav1, chk['checks'])))
        if cp[1] == 0: #(?, False)
            return self.comma_expr(chk['val'], self.assign(state, "bav", chk['checks']))
        if cp[0] is None and cp[1] is None: #(?,?)
            return self.comma_expr(chk['val'], self.assign(state, "bav",self.or_expr(bav1 ,self.cp(state,"bav"), chk['checks'])))
        assert(False)
        
    def __binaryShortCircuit_internal(self, state, expr, **kwargs):
        # return (([[expr, GET_VAL, ACCESS]], bav)? nondet : [[expr, VALUE]])
        # with cp
        expr_getval = self.visitor_visit(state, expr, "GET_VAL", "ACCESS", **kwargs)
        expr_val = lambda state: self.visit_nz(state, expr, "VALUE", "WSE", **kwargs)
        if not self.abs_on or state.cp_bav == 0:
            return self.comma_expr(expr_getval, expr_val(state))
        elif state.cp_bav == 1:
            return self.comma_expr(expr_getval, self.getNondetvarBv(expr, "u1"))#self.nondet())
        elif state.cp_bav is None:
            return self.ternary_expr(state, self.comma_expr(expr_getval,self.cp(state, "bav")), lambda state: self.getNondetvarBv(expr, "u1"), expr_val) #self.nondet(), expr_val)
        
    def __or_underapproxOld(self, state, fullOp, **kwargs):
        # returns value = part1 || part2
        # where
        #   part1 = ([exp1,GETVAL], bav1 =bav, (!bav&&[exp1,VALUE])) {so that you fall though to part2 if exp1 was not ok}
        #   part2 = (bap1=bap, bap=bap||bav, [exp2,GETVAL], bap=bap1, [exp2,VALUE] || (bav=bav||bav1,0)) {so that you don't set bav when exp2 == 1}
        #assert(self.underapprox and not self.dr) # dr still not ready
        exp1 = fullOp.left
        exp2 = fullOp.right
        value = self.getCondition(fullOp)
        bav1 = self.getBav1(fullOp)
        bap1 = self.getBap1(fullOp)
        exp1_getval = self.visitor_visit(state, exp1, "GET_VAL", "ACCESS", **kwargs)
        exp1_val = self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)
        
        part1 = self.comma_expr(exp1_getval,
            self.assign_var(bav1, self.cp(state, "bav")),
            self.and_expr_prop(self.not_cp(state, "bav"), exp1_val))
        
        statePart1 = state.copy()
        statePart2 = state.copy()
        
        part2 = self.comma_expr(
            self.assign_var(bap1, self.cp(statePart2, "bap")),
            self.assign_with_prop(statePart2, "bap", self.or_expr_prop(self.cp(statePart2, "bap"), self.cp(statePart2, "bav"))),
            self.visitor_visit(statePart2, exp2, "GET_VAL", "ACCESS", **kwargs),
            self.assign_with_prop(statePart2, "bap", bap1),
            self.or_expr_prop(
                self.visitor_visit(statePart2, exp2, "VALUE", "WSE", **kwargs),
                self.comma_expr(self.assign_with_prop(statePart2, "bav", self.or_expr_prop(self.cp(statePart2, "bav"), bav1)), "0")
            ))
        state.doMerge(statePart1, statePart2)
        
        return self.assign_var(value, self.or_expr_prop(part1, part2))
        
    def __and_underapproxNoSeRight(self, state, fullOp, **kwargs):
        # returns part1, part2, part3
        # where
        #   part1 = [exp1,GETVAL], bav1 =bav, bap1=bap, bap=bap||bav
        #   part2 = part2a && part2b
        #       part2a = (bav||[exp1,VALUE])
        #       part2b = [exp2,GETVAL]
        #   part3 = bap=bap1, bav=(bav||bav1) && (bav1||[exp1,VALUE]) && (bav||[exp2,VALUE]), value = [exp1,VALUE] && [exp2,VALUE]
        exp1 = fullOp.left
        exp2 = fullOp.right
        value = self.getCondition(fullOp)
        bav1 = self.getBav1(fullOp)
        bap1 = self.getBap1(fullOp)
        part1 = [
            self.visitor_visit(state, exp1, "GET_VAL", "ACCESS", **kwargs),
            self.assign_var(bav1, self.cp(state, "bav")),
            self.assign_var(bap1, self.cp(state, "bap")),
            self.assign_with_prop(state, "bap", self.or_expr_prop(self.cp(state, "bap"), self.cp(state, "bav")))
        ]
        part2 = [self.visitor_visit(state, exp2, "GET_VAL", "ACCESS", **kwargs)] 
        part3 = [
            self.assign_with_prop(state, "bap", bap1),
            self.assign_with_prop(state, "bav", self.and_expr_prop(self.or_expr_prop(self.cp(state, "bav"), bav1), self.or_expr_prop(bav1, self.visit_nz(state, exp1, "VALUE", "WSE", **kwargs)), self.or_expr_prop(self.cp(state, "bav"), self.visit_nz(state, exp2, "VALUE", "WSE", **kwargs)))),
            self.assign_var(value, self.and_expr_prop(self.visit_nz(state, exp1, "VALUE", "WSE", **kwargs), self.visit_nz(state, exp2, "VALUE", "WSE", **kwargs)))
        ]
        return self.comma_expr(*(part1+part2+part3))
        
    def __and_underapprox(self, state, fullOp, **kwargs):
        # returns part1, part2, part3
        # where
        #   part1 = [exp1,GETVAL], bav1 =bav, bap1=bap, bap=bap||bav
        #   part2 = part2a && part2b
        #       part2a = (bav||[exp1,VALUE])
        #       part2b = [exp2,GETVAL]
        #   part3 = bap=bap1, bav=bav||(bav1&&[exp2,VALUE]), value = [exp1,VALUE] && [exp2,VALUE]
        exp1 = fullOp.left
        exp2 = fullOp.right
        if not self.supportFile.has_side_effects[exp2]:
            return self.__and_underapproxNoSeRight(state, fullOp, **kwargs)
        value = self.getCondition(fullOp)
        with self.bavH() as bav1:
            with self.bapH() as bap1:
                part1 = [
                    self.visitor_visit(state, exp1, "GET_VAL", "ACCESS", **kwargs),
                    self.assign_var(bav1, self.cp(state, "bav")),
                    self.assign_var(bap1, self.cp(state, "bap")),
                    self.assign_with_prop(state, "bap", self.or_expr_prop(self.cp(state, "bap"), self.cp(state, "bav")))
                ]
                part2a = self.or_expr_prop(self.cp(state, "bav"), self.visit_nz(state, exp1, "VALUE", "WSE", **kwargs))
                stateTillPart2a = state.copy()
                statePart2b = state.copy()
                part2b = "("+self.visitor_visit(statePart2b, exp2, "GET_VAL", "ACCESS", **kwargs)+")"
                state.doMerge(stateTillPart2a, statePart2b)
                part2 = [self.and_expr_prop(part2a, part2b)]
                part3 = [
                    self.assign_with_prop(state, "bap", bap1),
                    self.assign_with_prop(state, "bav", self.or_expr_prop(self.cp(state, "bav"), self.and_expr_prop(bav1, self.visit_nz(state, exp2, "VALUE", "WSE", **kwargs)))),
                    self.assign_var(value, self.and_expr_prop(self.visit_nz(state, exp1, "VALUE", "WSE", **kwargs), self.visit_nz(state, exp2, "VALUE", "WSE", **kwargs)))
                ]
        return self.comma_expr(*(part1+part2+part3))
        
    def __or_underapproxNoSeRight(self, state, fullOp, **kwargs):
        # returns part1, part2, part3
        # where
        #   part1 = [exp1,GETVAL], bav1 =bav, bap1=bap, bap=bap||bav
        #   part2 = [exp2,GETVAL]
        #   part3 = bap=bap1, bav=(bav||bav1) && (bav1||![exp1,VALUE]) && (bav||![exp2,VALUE]), value = [exp1,VALUE] || [exp2,VALUE]
        exp1 = fullOp.left
        exp2 = fullOp.right
        value = self.getCondition(fullOp)
        with self.bavH() as bav1:
            with self.bapH() as bap1:
                part1 = [
                    self.visitor_visit(state, exp1, "GET_VAL", "ACCESS", **kwargs),
                    self.assign_var(bav1, self.cp(state, "bav")),
                    self.assign_var(bap1, self.cp(state, "bap")),
                    self.assign_with_prop(state, "bap", self.or_expr_prop(self.cp(state, "bap"), self.cp(state, "bav")))
                ]
                part2 = [self.visitor_visit(state, exp2, "GET_VAL", "ACCESS", **kwargs)] 
                part3 = [
                    self.assign_with_prop(state, "bap", bap1),
                    self.assign_with_prop(state, "bav", self.and_expr_prop(self.or_expr_prop(self.cp(state, "bav"), bav1), self.or_expr_prop(bav1, "!("+self.visit_nz(state, exp1, "VALUE", "WSE", **kwargs)+")"), self.or_expr_prop(self.cp(state, "bav"), "!("+self.visit_nz(state, exp2, "VALUE", "WSE", **kwargs)+")"))),
                    self.assign_var(value, self.or_expr_prop(self.visit_nz(state, exp1, "VALUE", "WSE", **kwargs), self.visit_nz(state, exp2, "VALUE", "WSE", **kwargs)))
                ]
        return self.comma_expr(*(part1+part2+part3))
        
    def __or_underapprox(self, state, fullOp, **kwargs):
        # returns part1, part2, part3
        # where
        #   part1 = [exp1,GETVAL], bav1 =bav, bap1=bap, bap=bap||bav
        #   part2 = part2a && part2b
        #       part2a = (!bav&&[exp1,VALUE])
        #       part2b = [exp2,GETVAL]
        #   part3 = bap=bap1, bav=bav||(bav1&&![exp2,VALUE]), value = [exp1,VALUE] || [exp2,VALUE]
        exp1 = fullOp.left
        exp2 = fullOp.right
        is_staticlocalinit = (type(exp1) == c_ast.ID and "staticlocalinit" in exp1.name)
        if is_staticlocalinit:
            exp2ForVal = fullOp.right.lvalue
        else:
            exp2ForVal = exp2
        #ID(name='__cz_staticlocal_writer_fn_mutex')
        if not self.supportFile.has_side_effects[exp2]:
            return self.__or_underapproxNoSeRight(state, fullOp, **kwargs)
        value = self.getCondition(fullOp)
        with self.bavH() as bav1:
            with self.bapH() as bap1:
                part1 = [
                    self.visitor_visit(state, exp1, "GET_VAL", "ACCESS", **kwargs),
                    self.assign_var(bav1, self.cp(state, "bav")),
                    self.assign_var(bap1, self.cp(state, "bap")),
                    self.assign_with_prop(state, "bap", self.or_expr_prop(self.cp(state, "bap"), self.cp(state, "bav")))
                ]
                kwneg = kwargs.copy()
                kwneg['negate'] = True
                part2a = self.and_expr_prop(self.not_cp(state, "bav"), self.visit_nz(state, exp1, "VALUE", "WSE", **kwneg))
                stateTillPart2a = state.copy()
                statePart2b = state.copy()
                part2b = "("+self.visitor_visit(statePart2b, exp2, "GET_VAL", "ACCESS", **kwargs)+")"
                state.doMerge(stateTillPart2a, statePart2b)
                part2 = [self.and_expr_prop(part2a, part2b)]
                kwneg2 = kwargs.copy()
                kwneg2['negate'] = True
                part3 = [
                    self.assign_with_prop(state, "bap", bap1),
                    self.assign_with_prop(state, "bav", self.or_expr_prop(self.cp(state, "bav"), self.and_expr_prop(bav1, self.visit_nz(state, exp2ForVal, "VALUE", "WSE", **kwneg2)))),
                    self.assign_var(value, self.or_expr_prop(self.visit_nz(state, exp1, "VALUE", "WSE", **kwargs), self.visit_nz(state, exp2ForVal, "VALUE", "WSE", **kwargs)))
                ]
        return self.comma_expr(*(part1+part2+part3))
        
    def __and_underapproxZ(self, state, fullOp, **kwargs):
        # returns value = (part1 && part2), part3
        # where
        #   part1 = ([exp1,GETVAL], bav1 =bav, bap1=bap, bap=bap||bav, bav) ? 1 : [exp1,VALUE]
        #   part2 = ([exp2,GETVAL], bav) ? 1 : [exp2,VALUE]
        #   part3 = (bap=bap1, bav = bav || (bav1 && value))
        exp1 = fullOp.left
        exp2 = fullOp.right
        value = self.getCondition(fullOp)
        bav1 = self.getBav1(fullOp)
        bap1 = self.getBap1(fullOp)
        part1cond = self.comma_expr(
            self.visitor_visit(state, exp1, "GET_VAL", "ACCESS", **kwargs),
            self.assign_var(bav1, self.cp(state, "bav")),
            self.assign_var(bap1, self.cp(state, "bap")),
            self.assign_with_prop(state, "bap", self.or_expr_prop(self.cp(state, "bap"), self.cp(state, "bav"))), 
            self.cp(state, "bav")
        )
        part1 = self.or_expr_prop(part1cond, self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs))
        part2cond = self.comma_expr(
            self.visitor_visit(state, exp2, "GET_VAL", "ACCESS", **kwargs), 
            self.cp(state, "bav")
        )
        part2 = self.or_expr_prop(part2cond, self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs))
        val_p1_and_p2 = self.assign_var(value, self.and_expr_prop(part1, part2))
        part3 = self.assign_with_prop(state, "bav", self.or_expr_prop(self.cp(state, "bav"), self.and_expr_prop(bav1, value)))
        return self.comma_expr(val_p1_and_p2, self.assign_with_prop(state, "bap", bap1), part3)
        
    def __and_underapproxOldest(self, state, fullOp, **kwargs):
        # returns value = part1 && part2
        # where
        #   part1 = ([exp1,GETVAL], bav1 =bav, (bav||[exp1,VALUE])) {so that you fall though to part2 if exp1 was not ok}
        #   part2 = (bap1=bap, bap=bap||bav, [exp2,GETVAL], bap=bap1, [exp2,VALUE] && (bav=bav||bav1,1)) {so that you don't set bav when exp2 == 1} OLD
        #   part2 = (bap1=bap, bap=bap||bav, [exp2,GETVAL], bap=bap1, bav=bav||(bav1&&[exp2,VALUE]), [exp2,VALUE]) {so that you don't set bav when exp2 == 1}
        exp1 = fullOp.left
        exp2 = fullOp.right
        value = self.getCondition(fullOp)
        bav1 = self.getBav1(fullOp)
        bap1 = self.getBap1(fullOp)
        exp1_getval = self.visitor_visit(state, exp1, "GET_VAL", "ACCESS", **kwargs)
        exp1_val = self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)
        
        part1 = self.comma_expr(exp1_getval,
            self.assign_var(bav1, self.cp(state, "bav")),
            self.or_expr_prop(self.cp(state, "bav"), exp1_val))
        
        statePart1 = state.copy()
        statePart2 = state.copy()
        
        part2 = self.comma_expr(
            self.assign_var(bap1, self.cp(statePart2, "bap")),
            self.assign_with_prop(statePart2, "bap", self.or_expr_prop(self.cp(statePart2, "bap"), self.cp(statePart2, "bav"))),
            self.visitor_visit(statePart2, exp2, "GET_VAL", "ACCESS", **kwargs),
            self.assign_with_prop(statePart2, "bap", bap1),
            
            self.assign_with_prop(statePart2, "bav", self.or_expr_prop(self.cp(statePart2, "bav"), self.and_expr_prop(bav1, self.visitor_visit(statePart2, exp2, "VALUE", "WSE", **kwargs)))),
            self.visitor_visit(statePart2, exp2, "VALUE", "WSE", **kwargs)
            
            # OLD
            #self.and_expr_prop(
            #    self.visitor_visit(statePart2, exp2, "VALUE", "WSE", **kwargs),
            #    self.comma_expr(self.assign_with_prop(statePart2, "bav", self.or_expr_prop(self.cp(statePart2, "bav"), bav1)), "1")
            #)
            )
        state.doMerge(statePart1, statePart2)
        
        return self.assign_var(value, self.and_expr_prop(part1, part2))
        
    def __and_overapproxNoSeRight(self, state, fullOp, **kwargs):
        exp1 = fullOp.left
        exp2 = fullOp.right
        value = self.getCondition(fullOp)
        bav1 = self.getBav1(fullOp)
        part1 = [
            self.visitor_visit(state, exp1, "GET_VAL", "ACCESS", **kwargs),
            self.assign_var(bav1, self.cp(state, "bav"))
        ]
        part2 = [self.visitor_visit(state, exp2, "GET_VAL", "ACCESS", **kwargs)] 
        part3 = [
            self.assign_with_prop(state, "bav", self.and_expr_prop(self.or_expr_prop(self.cp(state, "bav"), bav1), self.or_expr_prop(bav1, self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)), self.or_expr_prop(self.cp(state, "bav"), self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)))),
            self.assign_var(value, self.and_expr_prop(self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs), self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)))
        ]
        return self.comma_expr(*(part1+part2+part3))
        
        
    def rule_OrAnd(self, state, fullOp, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, fullOp, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, fullOp, abs_mode, "WSE", **kwargs)
                )), fullOp, abs_mode, dr_mode)
        exp1 = fullOp.left
        exp2 = fullOp.right
        
        assert(fullOp.op in ("||", "&&"))
        
        if abs_mode is None and dr_mode is None:
            return "(("+self.visitor_visit(state, exp1, None, None, **kwargs) + ") " + fullOp.op + " ("+self.visitor_visit(state, exp2, None, None, **kwargs) + "))"
        if abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            return self.getCondition(fullOp)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS",'PREFIX',None):
            if self.underapprox:
                if fullOp.op == "||":
                    trans = self.__or_underapprox(state, fullOp, **kwargs)
                else:
                    trans = self.__and_underapprox(state, fullOp, **kwargs)
            #elif self.abs_on and fullOp.op == "&&":
            #    trans = self.__and_overapproxNoSeRight(state, fullOp, **kwargs)
            else:
                value = self.getCondition(fullOp)
                exp1_tr = self.__binaryShortCircuit_internal(state, exp1, **kwargs)
                stateBetween = state.copy()
                exp2_tr = self.__binaryShortCircuit_internal(state, exp2, **kwargs)
                state.doMerge(state, stateBetween)
                trans = self.comma_expr(
                    self.assign_var(value, "("+exp1_tr + " " + fullOp.op + " " +exp2_tr+")"),
                    self.if_abs(lambda: self.assign_with_prop(state, "bav", "0"))
                )
            return self.store_content(full_statement, trans, fullOp, abs_mode, dr_mode)
        else:
            assert(False)
            
    def __binaryop_op_can_overflow(self, op):
        return op in ("+","-","*","/","<<")
            
    def rule_BinaryOp(self, state, fullOp, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, fullOp, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, fullOp, abs_mode, "WSE", **kwargs)
                )), fullOp, abs_mode, dr_mode)
        exp1 = fullOp.left
        exp2 = fullOp.right
        op = fullOp.op
        
        e1_op_e2_type = self.supportFile.get_type(fullOp) 
        e1_type = self.supportFile.get_type(fullOp.left) 
        e2_type = self.supportFile.get_type(fullOp.right) 
        isNotAbs_e1_op_e2_type = (not self.is_abstractable(e1_op_e2_type)) or self.abstr_bits >= 8 * self.abstrTypesSizeof[e1_op_e2_type]
        isNotAbs_e1_type = (not self.is_abstractable(e1_type)) or self.abstr_bits >= 8 * self.abstrTypesSizeof[e1_type]
        isNotAbs_e2_type = (not self.is_abstractable(e2_type)) or self.abstr_bits >= 8 * self.abstrTypesSizeof[e2_type]
        
        assert(op in ('|','^','&','==','!=','<','<=','>','>=','<<','>>','+','-','*','/','%'))
        
        if abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            if not self.abs_on or isNotAbs_e1_op_e2_type:
                ans = "(("+self.visit_cut(state, exp1, "VALUE", "WSE", **kwargs)+") "+op+" ("+ self.visit_cut(state, exp2, "VALUE", "WSE", **kwargs)+"))"
            elif isNotAbs_e2_type or isNotAbs_e1_type:
                ans = self.cut("("+self.visit_cut(state, exp1, "VALUE", "WSE", **kwargs)+") "+op+" ("+ self.visit_cut(state, exp2, "VALUE", "WSE", **kwargs)+")")
            else:
                ans = self.auxvars.read(fullOp)
            return self.store_content(full_statement, ans, fullOp, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS",'PREFIX',None):
            stmts = []
            stmts.append(self.visitor_visit(state, exp1, "GET_VAL", "ACCESS", **kwargs))
            if not self.abs_on:
                stmts.append(self.visitor_visit(state, exp2, "GET_VAL", "ACCESS", **kwargs))
            elif self.cp(state, "bav") == "1":
                # broken: the whole expression is not ok: evaluate exp2 and create a valuevar with a fake value
                stmts.append(self.visitor_visit(state, exp2, "GET_VAL", "ACCESS", **kwargs))
                if self.cp(state, "bav") != "1":
                    stmts.append(self.assign_with_prop(state,"bav","1"))
                self.auxvars.create_fake(fullOp, "1")
            elif self.cp(state, "bav") == "0":
                # first bav was always ok: compute exp2 directly using the original bav
                stmts.append(self.visitor_visit(state, exp2, "GET_VAL", "ACCESS", **kwargs))
                if isNotAbs_e1_op_e2_type or isNotAbs_e1_type or isNotAbs_e2_type:
                    # no abstraction: [VALUE] will compute the result
                    pass
                elif self.cp(state, "bav") == "1":
                    # broken
                    self.auxvars.create_fake(fullOp, "1")
                elif self.cp(state, "bav") == "0":
                    # both bav ok: compute of directly using the original bav
                    stmts.append(self.__binaryop_checks_and_val_new(state, fullOp, exp1, exp2, op, e1_op_e2_type, e1_type, e2_type, self.bav, **kwargs))
                elif self.cp(state, "bav") == self.bav:
                    if self.__binaryop_op_can_overflow(op):
                        with self.bavH() as bav1:
                            stmts.append(self.__binaryop_checks_and_val_new(state, fullOp, exp1, exp2, op, e1_op_e2_type, e1_type, e2_type, bav1, **kwargs))
                            stmts.append(self.assign_with_prop(state,"bav",self.or_expr_prop(self.cp(state, "bav"), bav1)))
                    else:
                        stmts.append(self.__binaryop_checks_and_val_new(state, fullOp, exp1, exp2, op, e1_op_e2_type, e1_type, e2_type, None, **kwargs))
                else:
                    assert(False)
            elif self.cp(state, "bav") == self.bav:
                # first bav unknown: backup bav
                with self.bavH() as bav1:
                    stmts.append(self.assign_var(bav1, self.cp(state, "bav")))
                    stmts.append(self.visitor_visit(state, exp2, "GET_VAL", "ACCESS", **kwargs))
                    if (not self.is_abstractable(e1_op_e2_type)) or self.abstr_bits >= 8 * self.abstrTypesSizeof[e1_op_e2_type]:
                        # no abstraction: [VALUE] will compute the result
                        stmts.append(self.assign_with_prop(state,"bav",self.or_expr_prop(self.cp(state, "bav"), bav1)))
                    elif self.cp(state, "bav") == "1":
                        # broken
                        self.auxvars.create_fake(fullOp, "1")
                    elif self.cp(state, "bav") == "0":
                        # second bav ok: compute of directly using the original bav
                        stmts.append(self.__binaryop_checks_and_val_new(state, fullOp, exp1, exp2, op, e1_op_e2_type, e1_type, e2_type, self.bav, **kwargs))
                        stmts.append(self.assign_with_prop(state,"bav",self.or_expr_prop(self.cp(state, "bav"), bav1)))
                    elif self.cp(state, "bav") == self.bav:
                        stmts.append(self.assign_with_prop(state,"bav",self.or_expr_prop(self.cp(state, "bav"), bav1)))
                        stmts.append(self.__binaryop_checks_and_val_new(state, fullOp, exp1, exp2, op, e1_op_e2_type, e1_type, e2_type, bav1, **kwargs))
                        if self.__binaryop_op_can_overflow(op):
                            stmts.append(self.assign_with_prop(state,"bav",self.or_expr_prop(self.cp(state, "bav"), bav1)))
                    else:
                        assert(False)
            else:
                assert(False)
            return self.store_content(full_statement,self.comma_expr(*stmts), fullOp, abs_mode, dr_mode)
        else:
            assert(False)
        
        
    def rule_ID(self, state, sid, abs_mode, dr_mode, full_statement, **kwargs):
        is_func_arg = kwargs.pop("func_arg", False)
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, sid, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, sid, abs_mode, "WSE", **kwargs)
                )), sid, abs_mode, dr_mode)
        if not self.abs_on and not self.dr_on:
            return sid.name
        elif abs_mode == "LVALUE":
            return sid.name
        elif abs_mode == "VALUE" :
            return sid.name
        elif dr_mode == "WSE": # and implicitly abs is disabled
            return sid.name
        elif sid.name == "__cs_thread_index":
            return ""
        else:
            sidType = self.supportFile.get_type(sid)
            return self.store_content(full_statement,self.comma_expr(
                self.if_dr(lambda: 
                    self.and_expr(
                        self.p2code(self.getVpstate(**kwargs)), 
                        self.brackets(self.assign_with_prop(state,"dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), self.getsm("&("+sid.name+")", self.getsm_dr(kwargs)))))
                    ) if dr_mode != "NO_ACCESS" else ""),
                self.if_abs(lambda: self.assign_with_prop(state,"bal","0")),
                self.if_abs(lambda: (self.assign_with_prop(state,"bav",self.getsm("&("+sid.name+")", self.sm_abs)) if abs_mode in ("GET_VAL", "UPD_VAL") else ""))
            ), sid, abs_mode, dr_mode)
    
    def rule_ArrayID(self, state, sid, abs_mode, dr_mode, full_statement, **kwargs):   
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, sid, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, sid, abs_mode, "WSE", **kwargs)
                )), sid, abs_mode, dr_mode)
        if not self.abs_on and not self.dr_on:
            return sid.name
        elif abs_mode == "LVALUE":
            return sid.name
        elif abs_mode == "VALUE" :
            return sid.name
        elif dr_mode == "WSE": # and implicitly abs is disabled
            return sid.name
        else:
            return self.store_content(full_statement,self.comma_expr(
                self.if_dr(lambda: 
                    self.and_expr(
                        self.p2code(self.getVpstate(**kwargs)), 
                        self.brackets(self.assign_with_prop(state,"dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), self.getsm("&("+sid.name+")", self.getsm_dr(kwargs)))))
                    ) if dr_mode not in ("NO_ACCESS", "PREFIX") else ""),
                self.if_abs(lambda: self.assign_with_prop(state,"bal","0")),
                self.if_abs(lambda: self.assign_with_prop(state,"bav","0") if abs_mode in ("GET_VAL", "UPD_VAL") else "")
            ), sid, abs_mode, dr_mode)
                    
    def rule_Constant(self, state, con, abs_mode, dr_mode, full_statement, **kwargs):      
        is_func_arg = kwargs.pop("func_arg", False)
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, con, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, con, abs_mode, "WSE", **kwargs)
                )), con, abs_mode, dr_mode)
        assert(abs_mode not in ("SET_VAL", "GET_ADDR"), "Invalid: cannot get address or set the value of constants")
        if not self.abs_on and not self.dr_on:
            return con.value
        elif abs_mode == "VALUE":
            cv_typ = self.supportFile.get_type(con)
            if self.compileTimeBoundsFailure(cv_typ, con.value) == "1":
                return self.cast("0", self.unsigned_1)
            else:
                return self.cast(con.value, self.cast_type(cv_typ))
        elif dr_mode == "WSE":
            return con.value
        else:
            cv_typ = self.supportFile.get_type(con)
            return self.if_abs(lambda:self.assign_with_prop(state,"bav", self.compileTimeBoundsFailure(cv_typ, con.value)))
            
    # nondeterministic returning function. Treat as a constant
    def rule_Nondet(self, state, fnc, abs_mode, dr_mode, full_statement, **kwargs):      
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, fnc, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, fnc, abs_mode, "WSE", **kwargs)
                )), fnc, abs_mode, dr_mode)
        assert(abs_mode not in ("SET_VAL", "GET_ADDR"), "Invalid: cannot get address or set the value of constants")
        if not self.abs_on and not self.dr_on:
            return self.getNondetvar(fnc)
        elif abs_mode == "VALUE" or dr_mode == "WSE":
            nvtyp = self.cast_type(kwargs['ndtype'])
            if (not self.is_abstractable(nvtyp)) or self.abstr_bits >= 8 * self.abstrTypesSizeof[nvtyp]:
                return self.getNondetvar(fnc)
            else:
                return self.cut(self.getNondetvar(fnc))
        else:
            typ=kwargs['ndtype']
            return self.if_abs(lambda:self.assign_with_prop(state,"bav", self.bounds_failure(self.getNondetvar(fnc), typ)))
                
    # nondeterministic returning function. Treat as a constant
    def rule_NondetBool(self, state, fnc, abs_mode, dr_mode, full_statement, **kwargs):      
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, fnc, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, fnc, abs_mode, "WSE", **kwargs)
                )), fnc, abs_mode, dr_mode)
        assert(abs_mode not in ("SET_VAL", "GET_ADDR"), "Invalid: cannot get address or set the value of constants")
        if not self.abs_on and not self.dr_on:
            return self.getNondetvarBv(fnc, "u1")
        elif abs_mode == "VALUE" or dr_mode == "WSE":
            return self.getNondetvarBv(fnc, "u1")
        else:
            return self.if_abs(lambda:self.assign_with_prop(state,"bav", "0"))
            
    # helper function: returns "p1 && (set_sm_dr(&[[unexp, LVALUE]],1), WKM=1)" and manually applies const propagation
    def __assignment_manual_cp_p1(self, state, unExpr, **kwargs):
        return self.and_expr(self.p1code(self.getVpstate(**kwargs)),
            self.comma_expr(
                self.setsm("&(("+self.visitor_visit(state, unExpr, "LVALUE", "WSE", **kwargs)+"))", self.sm_dr_all, "1"),  
                self.setsm("&(("+self.visitor_visit(state, unExpr, "LVALUE", "WSE", **kwargs)+"))", self.sm_dr_noatomic, "1") if self.code_contains_atomic and not kwargs['atomic'] else "",
                self.assign(state, "wkm", "1")))
            
    # helper function: returns "p2 && (DR = DR || WAM || get_sm_dr(&[[unexp, LVALUE]]))" and manually applies const propagation
    def __assignment_manual_cp_p2(self, state, unExpr, unExprType, **kwargs):
        return self.and_expr(self.p2code(self.getVpstate(**kwargs)),
            self.brackets(self.assign(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), 
                self.getsm("&("+self.visitor_visit(state, unExpr, "LVALUE", "WSE", **kwargs)+")", self.getsm_dr(kwargs)))))
            )
    
    # helper function: returns "bal && fail()" and manually applies const propagation    
    def __assignment_manual_bal_fail(self, state):
        if state.cp_bal == 0:
            return ""
        elif state.cp_bal == 1:
            if self.underapprox:
                return self.assume_expr("0")
            else:
                return fail_expr()
        elif state.cp_bal is None:
            if self.underapprox:
                return self.assume_expr("!"+self.bal)
            else:
                return self.assert_expr("!"+self.bal)
        else:
            assert(False)
        '''if state.cp_bal is None:
            return self.and_expr(self.bal, self.fail_expr())
        elif state.cp_bal == 0:
            return ""
        elif state.cp_bal == 1:
            return self.fail_expr()
        else:
            assert(False, "Invalid bal: "+str(state.cp_bal))'''
    # helper function: returns "bav && fail()" and manually applies const propagation    
    # if underapprox: "bav && assume(0)"
    def __assignment_manual_bav_fail(self, state):
        if state.cp_bav == 0:
            return ""
        elif state.cp_bav == 1:
            if self.underapprox:
                return self.assume_expr("0")
            else:
                return self.fail_expr()
        elif state.cp_bav is None:
            if self.underapprox:
                return self.assume_expr("!"+self.bav)
            else:
                return self.assert_expr("!"+self.bav)
        else:
            assert(False)
        '''if state.cp_bav is None:
            return self.and_expr(self.bav, self.fail_expr())
        elif state.cp_bav == 0:
            return ""
        elif state.cp_bav == 1:
            return self.fail_expr()
        else:
            assert(False, "Invalid bav: "+str(state.cp_bav))'''
            
    def evalValue(self, value):
        if value[0] == "'" and value[-1] == "'":
            if len(value) == 4:
                vesc = value[2]
                if vesc == "a": return 7
                elif vesc == "b": return 8
                elif vesc == "e": return 0x1b
                elif vesc == "f": return 0xc
                elif vesc == "n": return 0xa
                elif vesc == "r": return 0xd
                elif vesc == "t": return 9
                elif vesc == "v": return 0xb
                elif vesc == "\\": return 0x5c
                elif vesc == "'": return 0x27
                elif vesc == "\"": return 0x22
                elif vesc == "?": return 0x3f
                return ord(vesc)
            else:
                return ord(value[1])
        elif value[-1] == "u":
            return eval(value[:-1])
        else:
            return eval(value)
            
            
    def compileTimeBoundsFailure(self, typ, value):
        if value[0] == "E":
            return self.bounds_failure(value, typ)
        if value == "__cs_CREATE_JOINABLE":
            return "0"
        if typ in self.abstrTypesSigned:
            intVal = self.evalValue(value)
            mn = -2**(self.abstr_bits-1)
            mx = 2**(self.abstr_bits-1)-1
            mnU = 0
            mxU = 2**(self.abstr_bits)-1
            if mn <= intVal and intVal <= mx:
                return "0" #inside bound normally
            elif value.startswith("0") and mnU <= intVal and intVal <= mxU: 
                return "0" #octal or binary, treat them as unsigned
            else:
                return "1"
        elif typ in self.abstrTypesUnsigned:
            intVal = self.evalValue(value)
            mn = 0
            mx = 2**(self.abstr_bits)-1
            return "0" if mn <= intVal and intVal <= mx else "1"
        elif value == "NULL":
            return "0"
        elif "." in value:
            return "0"
        elif len(value) > 0 and value[0] == '"' and value[-1] == '"':
            return "0"
        else:
            assert(False)
            
    def is_numeric_constant(self, v):
        if len(v) == 3 and v[0] == "'" and v[2] == "'" and v[1] != "\\":
            return True # char
        if len(v) == 4 and v[0] == "'" and v[3] == "'" and v[1] == "\\" and v[2] in "abefnrtv\\'\"?":
            return True # escaped char
        v = v.strip().replace("'","")
        if v[-3:] in ("ULL", "ull"):
            v = v[:-3]
        elif v[-2:] in ("LL", "ll", "UL", "ul"):
            v = v[:-2]
        elif v[-1] in ("L", "l", "U", "u"):
            v = v[:-1]
        if v[0] == "0" and len(v)>=2:
            if len(v) == 1:
                return True
            elif v[1] in string.octdigits and len(v) == 2:
                return True
            elif v[1] in ("X","x") and len(v) > 2:
                return all(c in string.hexdigits for c in v[2:])
            elif v[1] in ("Oo"+string.octdigits) and len(v) > 2:
                return all(c in string.octdigits for c in v[2:])
            elif v[1] in ("B","b") and len(v) > 2:
                return all(c in "01" for c in v[2:])
            else:
                return False
        else:
            return v.isnumeric()
        
    # Test whethrer we need to check a bounds failure: otherwise, return "" or a pre-computed value
    def __assignment_bounds_failure(self, state, n, unExprType, assExpType, **kwargs):
        #if not self.is_abstractable(unExprType):
        #    return ""
        #TODO check if bitwidth is compatible if vars have different abstraction bitwidths
        if type(n) in (c_ast.Struct, c_ast.Union): 
            return "0"
        elif type(n) is c_ast.UnaryOp and n.op in ("+","-") and type(n.expr) is c_ast.Constant:
            if self.is_numeric_constant(n.expr.value):
                return self.compileTimeBoundsFailure(unExprType, n.op+n.expr.value)
            else:
                return "0"
        elif type(n) is c_ast.Constant:
            if self.is_numeric_constant(n.value):
                return self.compileTimeBoundsFailure(unExprType, n.value)
            else:
                return "0"
        elif type(n) is c_ast.BinaryOp and n.op == "-" and n.right is c_ast.Constant and n.right.value == "1":
            return self.ismin_type(self.visitor_visit(state, n.left, "VALUE", "WSE", **kwargs), unexprType)
        elif type(n) is c_ast.BinaryOp and n.op == "+" and n.right is c_ast.Constant and n.right.value == "1":
            return self.ismax_type(self.visitor_visit(state, n.left, "VALUE", "WSE", **kwargs), unexprType)
        elif type(n) in (c_ast.ArrayRef, c_ast.Assignment, c_ast.StructRef, c_ast.ID, c_ast.FuncCall): 
            if self.can_assign_unchecked(unExprType, assExpType):
                return "0" # can do the assignments without checking, types are compatible
            else:
                return self.bounds_failure(self.visitor_visit(state, n, "VALUE", "WSE", **kwargs), unExprType)
        elif type(n) in (c_ast.BinaryOp, c_ast.TernaryOp, c_ast.UnaryOp):
            return self.bounds_failure(self.visitor_visit(state, n, "VALUE", "WSE", **kwargs), unExprType)
        elif type(n) is c_ast.ExprList:
            return self.__assignment_bounds_failure(state, n.exprs[-1], unExprType, assExpType, **kwargs)
        elif type(n) is c_ast.Cast:
            return self.__assignment_bounds_failure(state, n.expr, unExprType, assExpType, **kwargs)
        else:
            print(n)
            assert(False)
            
    def assignment_encode_simpl_possible(self, n):
        if type(n) is c_ast.Cast:
            return self.assignment_encode_simpl_possible(n.expr)
        elif type(n) is c_ast.UnaryOp and n.op == "*":
            return True
        elif type(n) in (c_ast.ArrayRef, c_ast.StructRef, c_ast.ID):
            return True
        else:
            return False
    def assignment_encode(self, inner,assExp, xtype):
        return self.encode(inner, xtype)
        # return encode(inner) avoiding "ENCODE_t(DECODE_t(" constructs
        if self.is_abstractable(xtype) and self.assignment_encode_simpl_possible(assExp):
            brackets = 0
            idxLeft = 0
            foundDecode = False
            while idxLeft < len(inner):
                if inner[idxLeft] == " ":
                    idxLeft += 1
                elif inner[idxLeft] == "(":
                    brackets += 1
                    idxLeft += 1
                elif inner[idxLeft] == "D" and inner.startswith("DECODE_"+xtype, idxLeft):
                    idxLeft += len("DECODE_"+xtype)
                    foundDecode = True
                    break
                else:
                    break
            if foundDecode:
                idxRight = len(inner) - 1
                if brackets == 0:
                    return inner[idxLeft:idxRight+1]
                while idxRight >= 0:
                    if inner[idxRight] == " ":
                        idxRight -= 1
                    elif inner[idxRight] == ")":
                        brackets -= 1
                        idxRight -= 1
                        if brackets == 0:
                            return inner[idxLeft:idxRight+1]
                    else:
                        break
        return self.encode(inner, xtype)
        
        
    def rule_Assignment(self, state, assn, abs_mode, dr_mode, full_statement, **kwargs):
        is_func_arg = kwargs.pop("func_arg", False)
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, assn, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, assn, abs_mode, "WSE", **kwargs)
                )), assn, abs_mode, dr_mode)
        unExp = assn.lvalue
        assExp = assn.rvalue
        op = assn.op
        
        isCondVar = self.is_cond_var(unExp) # this assignment is used in if/loop conditions: do not consider it dirty only because baP=1
        
        if abs_mode == "VALUE" or dr_mode == "WSE":
            if isCondVar:
                ans = self.visit_nz_cond(state, unExp, "VALUE", "WSE", func_arg = is_func_arg, **kwargs)
            else:
                ans = self.visitor_visit(state, unExp, "VALUE", "WSE", func_arg = is_func_arg, **kwargs)
            return self.store_content(full_statement,ans, assn, abs_mode, dr_mode)
        if op != "=":
            fullOp = lambda: self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs)+" "+op.replace("=","")+" "+self.visitor_visit(state, assExp, "VALUE", "WSE", **kwargs)
            fullOpNode = BinaryOp(op.replace("=",""), unExp, assExp)
        unExprType = self.supportFile.get_type(unExp)
        assExpType = self.supportFile.get_type(assExp)
        is_unExprType_abs = self.is_abstractable(unExprType) and self.abstr_bits < 8 * self.abstrTypesSizeof[unExprType]
        is_assExpType_abs = self.is_abstractable(assExpType) and self.abstr_bits < 8 * self.abstrTypesSizeof[assExpType]
        
        stmts = []
        stmts.append(self.if_abs_or_dr(lambda: self.visitor_visit(state, unExp, "SET_VAL" if op == "=" else "UPD_VAL", "NO_ACCESS", **kwargs)))
        stmts.append(self.if_abs(lambda: self.__assignment_manual_bal_fail(state)))
        stmts.append(self.if_dr(lambda: self.__assignment_manual_cp_p1(state, unExp, **kwargs)))
        stmts.append(self.if_dr(lambda: self.__assignment_manual_cp_p2(state, unExp, unExprType, **kwargs)))
        if op == "=":
            stmts.append(self.if_abs_or_dr(lambda: self.visitor_visit(state, assExp, "GET_VAL", "ACCESS", **kwargs)))
            bav_or_test = [self.cp(state, "bav")]
            helpvar = None
            if self.underapprox and not isCondVar:
                bav_or_test.append(self.cp(state, "bap"))
            if not isCondVar and is_unExprType_abs and not is_assExpType_abs:
                helpvar = self.get_help_var(unExprType)
                stmts.append(helpvar + " = ("+self.visitor_visit(state, assExp, "VALUE", "WSE", **kwargs)+")")
                bav_or_test.append(self.bounds_failure(helpvar, unExprType))
            if len(bav_or_test) > 1:
                stmts.append(self.assign_with_prop(state,"bav",self.or_expr_prop(*bav_or_test)))
            stmts.append(self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, self.cp(state, "bav")))
            if not self.abs_on:
                stmts.append(self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+" = ("+self.visit_cut(state, assExp, "VALUE", "WSE", **kwargs)+")")
            elif isCondVar and is_assExpType_abs:
                stmts.append(self.assign_abstr_1(self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs), self.visit_nz(state, assExp, "VALUE", "WSE", **kwargs)))
            elif isCondVar and not is_assExpType_abs:
                stmts.append(self.assign_abstr_1(self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs), "("+self.visitor_visit(state, assExp, "VALUE", "WSE", **kwargs)+") != 0"))
            elif is_unExprType_abs and is_assExpType_abs:
                stmts.append(self.assign_abstr(self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs), self.visitor_visit(state, assExp, "VALUE", "WSE", **kwargs)))
            elif is_unExprType_abs and not is_assExpType_abs:
                stmts.append(self.assign_abstr(self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs), helpvar))
                self.release_help_var(helpvar)
            elif not is_unExprType_abs:
                stmts.append(self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+" = ("+self.visit_cut(state, assExp, "VALUE", "WSE", **kwargs)+")")
            else:
                assert(False)
        elif self.cp(state, "bav") == "1":
            # +=/*=/... and broken, don't compute anything TODO: maybe something for ||=, &&=, ...?
            stmts.append(self.if_abs_or_dr(lambda: self.visitor_visit(state, assExp, "GET_VAL", "ACCESS", **kwargs)))
            if self.cp(state, "bav") != "1":
                stmts.append(self.assign_with_prop(state,"bav","1"))
        else:
            innOp = op.replace("=","")
            if self.cp(state, "bav") == "0":
                # always ok: you can overwrite bav
                stmts.append(self.if_abs_or_dr(lambda: self.visitor_visit(state, assExp, "GET_VAL", "ACCESS", **kwargs)))
            else:
                with self.bavH() as bav1:
                    stmts.append(self.assign_var(bav1, self.cp(state, "bav")))
                    stmts.append(self.if_abs_or_dr(lambda: self.visitor_visit(state, assExp, "GET_VAL", "ACCESS", **kwargs)))
                    stmts.append(self.assign_with_prop(state,"bav",self.or_expr_prop(self.cp(state, "bav"), bav1)))
                if not is_unExprType_abs:
                    stmts.append(self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+" = ("+self.visit_cut(state, assExp, "VALUE", "WSE", **kwargs)+") " + innOp + " (" + self.visit_cut(state, assExp, "VALUE", "WSE", **kwargs) + ")")
                else:
                    bav_or_test = [self.cp(state, "bav")]
                    helpvar = None
                    rhs = None
                    if not is_assExpType_abs:
                        helpvar = self.get_help_var(unExprType)
                        stmts.append(helpvar + " = ("+unExprType+") ("+self.visitor_visit(state, assExp, "VALUE", "WSE", **kwargs)+")")
                        bav_or_test.append(self.bounds_failure(helpvar, unExprType))
                        rhs = helpvar
                    else:
                        rhs = self.visitor_visit(state, assExp, "VALUE", "WSE", **kwargs)
                    lhs = self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs)
                    if self.__binaryop_op_can_overflow(innOp):
                        with self.bavH() as bav1:
                            stmts.append(self.binary_op_of(lhs, innOp, rhs, "&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", "&"+bav1))
                            bav_or_test.append(bav1)
                            stmts.append(self.assign_with_prop(state,"bav",self.or_expr_prop(*bav_or_test)))
                    else:
                        stmts.append(self.binary_op_no_of(lhs, innOp, rhs, "&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")"))
                        if len(bav_or_test) > 1:
                            stmts.append(self.assign_with_prop(state,"bav",self.or_expr_prop(*bav_or_test)))
                    if helpvar is not None:
                        self.release_help_var(helpvar)
        ans = self.comma_expr(*stmts)
        return self.store_content(full_statement, ans, assn, abs_mode, dr_mode)
        
    def store_DeclConst(self, state, n, **kwargs):
        if self.abs_on:
            unExp = c_ast.ID(name=n.name)
            assExp = n.init
            unExprType = self.supportFile.get_type(unExp)
            if self.is_abstractable(unExprType):
                self.abs_const_decl += [self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, self.__assignment_bounds_failure(state, assExp, unExprType, unExprType, **kwargs))+";"]
            
    def rule_SpecialFuncCall(self, state, fcall, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        if dr_mode == "TOP_ACCESS":
            return self.store_content(full_statement, self.fakeIfAssignment(self.comma_expr(
                    self.visitor_visit(state, fcall, abs_mode, "ACCESS", **kwargs),
                    self.visitor_visit(state, fcall, abs_mode, "WSE", **kwargs)
                )), fcall, abs_mode, dr_mode)
        kwargs_nobavtest = {k:kwargs[k] for k in kwargs if k != "bavtest"}
        return self.comma_expr(
            self.if_abs(lambda: self.comma_expr(*[self.comma_expr(self.visitor_visit(state, x, "GET_VAL", "NO_ACCESS", **kwargs_nobavtest), self.__assignment_manual_bav_fail(state)) for x in kwargs["bavtest"]])),
            self.visitor_visit_noinstr(fcall))
        
    def rule_Type(self, state, typ, abs_mode, dr_mode, full_statement, **kwargs):
        typ_txt = kwargs['typ_txt']
        return typ_txt
        
    def fake_abstr_types(self):
        return []
        
    def rule_FunctionLocalDecls(self, state, fnc, abs_mode, dr_mode, full_statement, **kwargs):
        return self.if_ua(
            lambda: "static "+self.unsigned_1+" "+", ".join([self.bap]+["__cs_bap1_if_"+str(v) for v in range(self.bap1s_if_max)])+"; "+
                (self.bap + " = " + self.bap_passaround + "; " if 'read_bap_passthrough' in kwargs and kwargs['read_bap_passthrough'] else " ")+
                "RESETAUX();")
        
    def rule_ResetAux(self, state, fnc, abs_mode, dr_mode, full_statement, **kwargs):
        return "RESETAUX()"
        
    def rule_ChangeResetAux(self, state, fnc, abs_mode, dr_mode, full_statement, **kwargs):
        if not self.underapprox:
            return ""
            
        #self.bap1s_if_max is the first unassigned bap1_if and they are all free from that number on
        unused_bap1s_if = [self.bap_passaround+" = "] + [x+" = " for x in self.bap1s_if_free] + ["__cs_bap1_if_"+str(i)+" = " for i in range(self.bap1s_if_max, kwargs['max_nesting'])]
        
        if "__cs_bap1_if_0 = " in unused_bap1s_if:
            unused_bap1s_if = [self.bap+" = "] + unused_bap1s_if
        
        arg = "".join(unused_bap1s_if)
        return "RESETAUX_ARGS("+arg+")"
