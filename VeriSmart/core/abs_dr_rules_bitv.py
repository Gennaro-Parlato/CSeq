from pycparser import c_ast
from pycparser.c_generator import CGenerator
from core.support_file import SupportFileManager
from pycparser.c_ast import BinaryOp
from pycparser import c_ast
from core.var_simplifier import Cleaner, HasSideEffects
from collections import defaultdict
import string
import os

class CPState:
    def __init__(self):
        # Constant propagation: <value> = it is already known without reading it; None = must read it
        self.cp_bav = None 
        self.cp_bav_lhs = None 
        self.cp_bav_tmp = None 
        self.cp_bav1 = defaultdict(lambda: None)
        self.cp_bal = None 
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
        newst.cp_bal = self.cp_bal 
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
        self.cp_bal = self.__mergeVar(stateThen.cp_bal, stateEls.cp_bal) 
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
        
        
class AbsDrRules:            
    def __init__(self, visitor, abs_on, dr_possible, abstr_bits, supportFile, macroFileName, debug=False):
        # visitor module
        self.visitor = visitor
        # abstraction active
        self.abs_on = abs_on
        # data race is possible
        self.dr_possible = dr_possible
        # data race is on by default (if possible)
        self.dr_on = dr_possible
        
        # abstraction: bit abstraction Value/Lvalue
        self.bav = "__cs_baV" if abs_on else None
        self.bal = "__cs_baL" if abs_on else None
        self.bav_lhs = "__cs_baV_lhs" if abs_on else None
        self.bav_tmp = "__cs_baV_tmp" if abs_on else None
        # abstraction: signed types for which abstraction is enabled
        self.abstrTypesSigned = ['int','signed','signed int','char','signed char','short','short int','signed short','signed short int',
            'long int','long','long long','long long int','signed long int','signed long','signed long long','signed long long int'] if abs_on else []
        
        
        # abstraction: unsigned types for which abstraction is enabled
        self.abstrTypesUnsigned = ['unsigned','unsigned int','unsigned char','unsigned short','unsigned short int','unsigned long', 
            'unsigned long int','unsigned long long int'] if abs_on else []
        
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
                                   'unsigned long long int': 8}
        # abstraction: nr of bits for abstracted vars
        self.abstr_bits = abstr_bits
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
        # bav1 expressions, used in BOP
        self.bav1s = {}
        
        # abstraction: name field for dr
        self.sm_dr = "dr" if dr_possible else None
        
        # support file to compute types
        self.supportFile = supportFile
        
        # macro file with instrumented code
        self.macroFile = MacroFile(macroFileName, self, debug)
        
        # removes redundant assignments into instrumented code 
        self.cleaner = Cleaner()
        
        # checks whether some code has side effects 
        self.has_side_effects = HasSideEffects()
        
        # non-instrumented code generation
        self.plain_visitor = CGenerator()
        
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
        #TODO use __CPROVER_bitvector
        return self.compound_expr("\n",*([
            self.if_abs(lambda: "unsigned char "+self.bav+" = 0;"),
            self.if_abs(lambda: "unsigned char "+self.bal+" = 0;"),
            self.if_abs(lambda: "unsigned char "+self.bav_lhs+" = 0;"),
            self.if_abs(lambda: "unsigned char "+self.bav_tmp+" = 0;"),
            self.if_dr_possible(lambda: "unsigned char "+self.dr+" = 0;"),
            self.if_dr_possible(lambda: "unsigned char "+self.wam+" = 0;"),
            self.if_dr_possible(lambda: "unsigned char "+self.wkm+" = 0;"),
            self.if_dr_possible(lambda: 'unsigned char __cs_dataraceDetectionStarted = (unsigned char) 0;'),
            self.if_dr_possible(lambda: 'unsigned char __cs_dataraceSecondThread = (unsigned char) 0;'),
            self.if_dr_possible(lambda: 'unsigned char __cs_dataraceNotDetected = (unsigned char) 1;'),
            self.if_dr_possible(lambda: 'unsigned char __cs_dataraceContinue = (unsigned char) 1;'),
            self.if_dr_possible(lambda: 'unsigned char __cs_dataraceActiveVP1 = (unsigned char) 0;'),
            self.if_dr_possible(lambda: 'unsigned char __cs_dataraceActiveVP2 = (unsigned char) 0;'),
        ]+[
            self.if_abs(lambda: t+" __cs_bf_"+t.replace(" ","_")+" = ("+t+") 0;") for t in self.abstrTypesSigned
        ]))[0]
        
    def cond_vars_decl(self):
        #TODO use __CPROVER_bitvector
        return self.compound_expr("\n",*(['unsigned char '+v+';' for v in self.conditions.values()]))[0]
        
    def bav1_vars_decl(self):
        #TODO use __CPROVER_bitvector
        return self.compound_expr("\n",*(['unsigned char '+v+';' for v in self.bav1s.values()]))[0]
        
    def sm_field_decl(self):
        return "#define FIELD_DECLS() "+self.compound_expr(" ",*([
            self.if_abs(lambda: '__CPROVER_field_decl_global("'+self.sm_abs+'", (unsigned __CPROVER_bitvector[1])0);'),
            self.if_abs(lambda: '__CPROVER_field_decl_local("'+self.sm_abs+'", (unsigned __CPROVER_bitvector[1])0);'),
            self.if_dr(lambda: '__CPROVER_field_decl_global("'+self.sm_dr+'", (unsigned __CPROVER_bitvector[1])0);'),
            self.if_dr(lambda: '__CPROVER_field_decl_local("'+self.sm_dr+'", (unsigned __CPROVER_bitvector[1])0);'),
        ]))[0]
        
    def getAbstractionMacros(self):
        if self.abs_on:
            bitstr = str(self.abstr_bits)
            bitstr_1 = str(self.abstr_bits-1)
            mask_t = hex(2**self.abstr_bits-1)
            mask_t_1 = hex(2**(self.abstr_bits-1)-1)
            return self.compound_expr("\n",*([
                self.sm_field_decl(),
            ]+["#define MASK_"+t.replace(" ","_")+"_"+bitstr+" (("+t+") "+mask_t+")" for t in self.abstrTypesSigned]+
              ["#define MASK_"+t.replace(" ","_")+"_"+bitstr_1+" (("+t+") "+mask_t_1+")" for t in self.abstrTypesSigned]+
              #["#define BOUNDS_FAILURE_"+t.replace(" ","_")+"(exp) ((((exp)&~MASK_"+t.replace(" ","_")+"_"+bitstr_1+")!=(~MASK_"+t.replace(" ","_")+"_"+bitstr_1+")) && ((exp)&~MASK_"+t.replace(" ","_")+"_"+bitstr_1+"))" for t in self.abstrTypesSigned]+
              ["#define BOUNDS_FAILURE_"+t.replace(" ","_")+"(exp) (((__cs_bf_"+t.replace(" ","_")+"=((exp)&~MASK_"+t.replace(" ","_")+"_"+bitstr_1+"))!=(~MASK_"+t.replace(" ","_")+"_"+bitstr_1+")) && __cs_bf_"+t.replace(" ","_")+")" for t in self.abstrTypesSigned]+
              ["#define ENCODE_"+t.replace(" ","_")+"(exp) ((exp)&MASK_"+t.replace(" ","_")+"_"+bitstr+")" for t in self.abstrTypesSigned]+
              ["#define DECODE_"+t.replace(" ","_")+"(exp) (("+t+")((signed __CPROVER_bitvector["+bitstr+"]) (exp)))" for t in self.abstrTypesSigned]+
              ["#define MIN_"+t.replace(" ","_")+" "+("((~(("+t+")0)) << "+bitstr_1+")" if self.abstr_bits < self.abstrTypesSizeof[t]*8 else "((~(("+t+")0)) << "+str(self.abstrTypesSizeof[t]*8-1)+")") for t in self.abstrTypesSigned]+
              ["#define MAX_"+t.replace(" ","_")+" "+"(~(MIN_"+t.replace(" ","_")+"))" for t in self.abstrTypesSigned]+
              ["#define ISMIN_"+t.replace(" ","_")+"(exp) "+"((exp) == MIN_"+t.replace(" ","_")+")" for t in self.abstrTypesSigned]+
              ["#define ISMAX_"+t.replace(" ","_")+"(exp) "+"((exp) == MAX_"+t.replace(" ","_")+")" for t in self.abstrTypesSigned]+
              
              
             
              ["#define MASK_"+t.replace(" ","_")+"_"+bitstr+" (("+t+") "+mask_t+")" for t in self.abstrTypesUnsigned]+
              #["#define MASK_"+t.replace(" ","_")+"_"+bitstr_1+" (("+t+") "+mask_t_1+")" for t in self.abstrTypesUnsigned]+
              ["#define BOUNDS_FAILURE_"+t.replace(" ","_")+"(exp) ((exp)&~MASK_"+t.replace(" ","_")+"_"+bitstr+")" for t in self.abstrTypesUnsigned]+
              ["#define ENCODE_"+t.replace(" ","_")+"(exp) ((exp)&MASK_"+t.replace(" ","_")+"_"+bitstr+")" for t in self.abstrTypesUnsigned]+
              ["#define DECODE_"+t.replace(" ","_")+"(exp) (("+t+")((unsigned __CPROVER_bitvector["+bitstr+"]) (exp)))" for t in self.abstrTypesUnsigned]+
              ["#define MIN_"+t.replace(" ","_")+" (("+t+")0)" for t in self.abstrTypesUnsigned]+
              ["#define MAX_"+t.replace(" ","_")+" "+("(~((~(("+t+")0)) << "+bitstr+"))" if self.abstr_bits < self.abstrTypesSizeof[t]*8 else "(~(("+t+")0))") for t in self.abstrTypesUnsigned]+
              ["#define ISMIN_"+t.replace(" ","_")+"(exp) "+"((exp) == MIN_"+t.replace(" ","_")+")" for t in self.abstrTypesUnsigned]+
              ["#define ISMAX_"+t.replace(" ","_")+"(exp) "+"((exp) == MAX_"+t.replace(" ","_")+")" for t in self.abstrTypesUnsigned]
              ))[0]
        else:
            return "" 
        
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
        if full_statement:
            return self.macroFile.store_macro(macro_content, node, abs_mode, dr_mode)
        else:
            return macro_content
        
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
        
    # join parts to form a compound expression
    def compound_expr(self, jn, *items):
        clean_items = [x for x in items if x != "" and x is not None]
        joined = jn.join(clean_items)
        return joined, len(clean_items)
        
    # join parts to form a compound expression with lambda functions
    def compound_expr_lambda(self, jn, *items):
        parts = [x() for x in items]
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
            
    # join parts to form a bit or expression
    def bitor_expr(self, *items):
        ors, parts = self.compound_expr(" | ", *items)
        if parts == 0:
            return "0"
        elif parts == 1:
            return ors
        else:
            return "(" + ors + ")"
    
    # apply cp to or expression, i.e., if any item is "1" return "1", remove "0"s
    def bitor_expr_prop(self, *items):
        if "1" in items:
            return "1"
        else:
            nonzero_items = tuple(x for x in items if x != "0")
            return self.bitor_expr(*nonzero_items)
        
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
        
    # return expr() if abs is off else ""        
    def if_no_abs(self, expr):
        return "" if self.abs_on else expr()
        
    # return expr() if either abs or dr is off else ""     
    def if_abs_or_dr(self, expr):
        return expr() if self.abs_on or self.dr_on else ""
        
    def is_abstractable(self, xtype):
        return xtype in ('int',
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
                                   'unsigned long long int') #TODO fill it properly
        
    def decode(self, x, xtype):
        assert(self.abs_on)
        if self.is_abstractable(xtype):
            xtype_nospaces = xtype.replace(" ","_")
            return "DECODE_"+xtype_nospaces+"(("+xtype+")("+x+"))"
        else:
            return x
        
    def encode(self, x, xtype):
        assert(self.abs_on)
        if self.is_abstractable(xtype):
            xtype_nospaces = xtype.replace(" ","_")
            return "ENCODE_"+xtype_nospaces+"(("+xtype+")("+x+"))"
        else:
            return "("+x+")"
        
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
        return "BOUNDS_FAILURE_"+xtype_nospaces+"(("+xtype+")("+x+"))"
        
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
            ans = "(" + cond + "?" + expr_then + ":" + expr_els + ")"
            state.doMerge(stateThen, stateEls)
            return ans
        
    def assert_expr(self, val):
        #return "__CSEQ_assert("+val+")"
        return "assert("+val+")"
        
    def fail_expr(self):
        return self.assert_expr("0")
        
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
        return self.visitor.visit_with_absdr_args(state, n, abs_mode if self.abs_on else None, dr_mode if self.dr_on else None, full_statement=False, **kwargs).strip()
        
    # Perform a visit using the visitor module without any instrumentation
    def visitor_visit_noinstr(self, n):
        return self.visitor.visit_noinstr(n, full_statement=False)
           
    def __arrayref_bavtmp_dr(self, state, dr_mode, postExp, exp, **kwargs):
        # if dr_mode is NO_ACCESS/PREFIX: remove
        # if abstraction:
        # return (bav_tmp || bav)?(p2&&dr=(dr||wam||wkm)):(p2&&dr=(dr||wam||get_sm_dr(&[[postExp,VALUE,WSE]][ [[exp,VALUE,WSE]] ])))
        # else:
        # return p2&&dr=(dr||wam||get_sm_dr(&[[postExp,WSE]][ [[exp,WSE]] ]))
        assert(self.dr_on)
        ok = lambda state: self.and_expr(self.p2code(self.getVpstate(**kwargs)), self.brackets(self.assign_with_prop(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), 
            self.getsm("&("+self.brackets(self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs))+"["+self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)+"])", self.sm_dr)))))
        err = lambda state: self.and_expr(self.p2code(self.getVpstate(**kwargs)), self.brackets(self.assign_with_prop(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), self.cp(state, "wkm")))))
        if dr_mode in ("NO_ACCESS", "PREFIX"):
            return ""
        elif self.abs_on:
            tmp_bav_cp = (state.cp_bav_tmp, state.cp_bav)
            if tmp_bav_cp[0] == 1 or tmp_bav_cp[1] == 1: # True || x, x || True
                return ok(state)
            elif tmp_bav_cp[0] == 0 and tmp_bav_cp[1] == 0: # False || False
                return err(state)
            elif tmp_bav_cp[1] == 0: # ? || False
                return self.ternary_expr(state, self.cp(state, "bav"), err, ok)
            elif tmp_bav_cp[0] == 0: # False || ?
                return self.ternary_expr(state, self.cp(state, "bav_tmp"), err, ok)
            else: # ? || ?
                return self.ternary_expr(state, self.or_expr(self.cp(state, "bav"),self.cp(state, "bav_tmp")), err, ok)
        else:
            return ok()
            
    def __arrayref_bavtmp_abs(self, state, postExp, exp, **kwargs):
        # return bav = ((bal = (bav_tmp | bav)) | get_sm_abs(&[[postExp,VALUE,WSE]] [ [[exp,VALUE,WSE]] ]))
        assert(self.abs_on)
        getsm = lambda: self.getsm("&("+self.brackets(self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs))+"["+self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)+"])", self.sm_abs)
        tmp_bav_cp = (state.cp_bav_tmp, state.cp_bav) #(bav_tmp || bav) as const propagation
        if tmp_bav_cp[1] == 1: # x || True
            return self.assign_with_prop(state, "bal", "1") 
        elif tmp_bav_cp[0] == 1: # True || (False/?)
            return self.comma_expr(self.assign_with_prop(state, "bal", "1"), self.assign_with_prop(state, "bav", "1")) 
        elif tmp_bav_cp[0] == 0 and tmp_bav_cp[1] == 0: #(False || False)
            return self.comma_expr(self.assign_with_prop(state, "bal", "0"), self.assign(state, "bav", getsm()))
        else: # (? || ?) (False || ?) (? || False)
            return self.assign(state, "bav", self.bitor_expr(self.assign(state,"bal",self.bitor_expr_prop(self.cp(state,"bav_tmp"),self.cp(state,"bav"))),getsm())) 
        
            
    def rule_ArrayRef(self, state, arrexp, abs_mode, dr_mode, full_statement, **kwargs): # postExp[exp]
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        postExp = arrexp.name
        exp = arrexp.subscript
        if abs_mode in ("LVALUE", None) and dr_mode in ("WSE", None):
            return self.store_content(full_statement,self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs)+"["+self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)+"]", \
                arrexp, abs_mode, dr_mode)
        elif abs_mode in ("VALUE",) and dr_mode in ("WSE", None):
            arrexpType = self.supportFile.get_type(arrexp) #"int" #TODO get type from expression
            return self.store_content(full_statement,self.decode(self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs)+"["+self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)+"]", \
                arrexpType), arrexp, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL", "UPD_VAL", None) and dr_mode in ("ACCESS", "PREFIX", "NO_ACCESS", None):
            return self.store_content(full_statement,self.comma_expr(
                self.if_abs_or_dr(lambda: self.visitor_visit(state, postExp, "GET_VAL", "PREFIX", **kwargs)),
                self.if_abs(lambda: self.assign_with_prop(state, "bav_tmp", self.cp(state, "bav"))),
                self.if_abs_or_dr(lambda: self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs)),
                self.if_dr(lambda: self.__arrayref_bavtmp_dr(state, dr_mode, postExp, exp, **kwargs)),
                self.if_abs(lambda: self.__arrayref_bavtmp_abs(state, postExp, exp, **kwargs))
            ), arrexp, abs_mode, dr_mode)
        elif abs_mode in ("SET_VAL", "GET_ADDR",) and dr_mode in ("PREFIX", "NO_ACCESS", None):
            ans = self.comma_expr(
                self.if_abs_or_dr(lambda: self.visitor_visit(state, postExp, "GET_VAL", "PREFIX", **kwargs)),
                self.if_abs(lambda: self.assign_with_prop(state, "bav_tmp", self.cp(state, "bav"))),
                self.if_abs_or_dr(lambda: self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs)),
                self.if_abs(lambda: self.assign_with_prop(state,"bal",self.bitor_expr_prop(self.cp(state,"bav_tmp"),self.cp(state,"bav"))))
            )
            return self.store_content(full_statement,ans, arrexp, abs_mode, dr_mode)
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
            self.getsm("&("+self.brackets(self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs))+"->"+exp.name+")", self.sm_dr)))))
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
            return ok()        
    
    def __structrefptr_bavtmp_abs(self, state, postExp, exp, **kwargs):
        # return (bal = bav, bav = bav | get_sm_abs(&([[postExp,VALUE,WSE]]->exp)))
        assert(self.abs_on)
        getsm = lambda: self.getsm("&("+self.brackets(self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs))+"->"+exp.name+")", self.sm_abs)
        
        
        
        cp = (state.cp_bal, state.cp_bav) #(bal, bav) as const propagation
        if cp[0] == 0 and cp[1] == 0: #bal = False, bav = False
            return self.assign_with_prop(state, "bav", getsm()) # bav = getsm
        elif cp[0] in (1, None) and cp[1] == 0: #bal = True/?, bav = False
            return self.comma_expr(self.assign_with_prop(state, "bal", self.cp(state, "bav")), self.assign_with_prop(state, "bav", getsm())) #(bal = 0, bav = getsm)
        elif cp[0] == 1 and cp[1] == 1: #bal = True, bav = True
            return ""
        elif cp[0] in (0, None) and cp[1] == 1: #bal = False/?, bav = True
            return self.assign_with_prop(state, "bal", self.cp(state, "bav")) # bal = bav
        elif cp[1] is None: #bal = False/True/?, bav = ?
            return self.comma_expr(self.assign_with_prop(state, "bal", self.cp(state, "bav")), self.assign_with_prop(state, "bav", self.bitor_expr(self.cp(state, "bav"), getsm()))) #(bal = bav, bav = bav | getsm)
        else:
            assert(False)
            
    def rule_StructRefPtr(self, state, srexp, abs_mode, dr_mode, full_statement, **kwargs): # postExp->exp
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        assert(srexp.type == "->")
        postExp = srexp.name
        fid = srexp.field
        if abs_mode in ("LVALUE", None) and dr_mode in ("WSE", None):
            return self.store_content(full_statement,self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs)+"->"+fid.name, srexp, abs_mode, dr_mode)
        elif abs_mode in ("VALUE",) and dr_mode in ("WSE", None):
            srexpType = self.supportFile.get_type(srexp) #"int" #TODO get type from expression
            return self.store_content(full_statement,self.decode(self.visitor_visit(state, postExp, "VALUE", "WSE", **kwargs)+"->"+fid.name, srexpType), srexp, abs_mode, dr_mode)
            
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
            
    def __structrefvar_bal_dr(self, state, dr_mode, postExp, exp, **kwargs):
        # if dr_mode is NO_ACCESS/PREFIX: remove
        # if abstraction:
        # return (bal)?(p2&&dr=(dr||wam||wkm)):(p2&&dr=(dr||wam||get_sm_dr(&([[postExp,WSE]].exp)))
        # else:
        # return p2&&dr=(dr||wam||get_sm_dr(&([[postExp,WSE]].exp)))
        assert(self.dr_on)
        ok = lambda state: self.and_expr(self.p2code(self.getVpstate(**kwargs)), self.brackets(self.assign_with_prop(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), 
            self.getsm("&("+self.brackets(self.visitor_visit(state, postExp, "LVALUE", "WSE", **kwargs))+"."+exp.name+")", self.sm_dr)))))
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
            return ok()        
            
    def __structrefvar_bav_abs(self, state, postExp, exp, **kwargs):
        # return bav = bal | get_sm_abs(&([[postExp,VALUE,WSE]]->exp))
        assert(self.abs_on)
        getsm = lambda: self.getsm("&("+self.brackets(self.visitor_visit(state, postExp, "LVALUE", "WSE", **kwargs))+"."+exp.name+")", self.sm_abs)
        if state.cp_bal == 1:
            return self.assign_with_prop(state, "bav", "1")
        elif state.cp_bal == 0:
            return self.assign(state, "bav", getsm())
        elif state.cp_bal is None:
            return self.assign(state, "bav", self.bitor_expr(self.cp(state,"bal"),getsm()))
        else:
            assert(False)
            
    def rule_StructRefVar(self, state, srexp, abs_mode, dr_mode, full_statement, **kwargs): # postExp->exp
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        assert(srexp.type == ".")
        postExp = srexp.name
        fid = srexp.field
        if abs_mode in ("LVALUE", None) and dr_mode in ("WSE", None):
            return self.store_content(full_statement,self.brackets(self.visitor_visit(state, postExp, "LVALUE", "WSE", **kwargs))+"."+fid.name, srexp, abs_mode, dr_mode)
        elif abs_mode in ("VALUE",) and dr_mode in ("WSE", None):
            srexpType = self.supportFile.get_type(srexp) #"int" #TODO get type from expression
            return self.store_content(full_statement,self.decode(self.brackets(self.visitor_visit(state, postExp, "LVALUE", "WSE", **kwargs))+"."+fid.name, srexpType), srexp, abs_mode, dr_mode)
            
        elif abs_mode in ("GET_VAL", "UPD_VAL", None) and dr_mode in ("ACCESS", "PREFIX", "NO_ACCESS", None):
            return self.store_content(full_statement,self.comma_expr(
                self.if_abs_or_dr(lambda: self.visitor_visit(state, postExp, "GET_ADDR", "NO_ACCESS", **kwargs)),
                self.if_dr(lambda: self.__structrefvar_bal_dr(state, dr_mode, postExp, fid, **kwargs)), 
                self.if_abs(lambda: self.__structrefvar_bav_abs(state, postExp, fid, **kwargs))
            ), srexp, abs_mode, dr_mode)
        elif abs_mode in ("SET_VAL", "GET_ADDR",) and dr_mode in ("PREFIX", "NO_ACCESS", None):
            ans = self.if_abs_or_dr(lambda: self.visitor_visit(state, postExp, "GET_ADDR", "NO_ACCESS", **kwargs))
            return self.store_content(full_statement,ans, srexp, abs_mode, dr_mode)
        else:
            assert(False, "Invalid mode for StructRefVar: abs_mode = "+str(abs_mode)+"; dr_mode = "+str(dr_mode))
            
    def getCondition(self, cond):
        if cond not in self.conditions:
            self.conditions[cond] = "__cs_cond_"+str(len(self.conditions))
        return self.conditions[cond]
        
    def getBav1(self, bop):
        if bop not in self.bav1s:
            self.bav1s[bop] = "__cs_bav1_"+str(len(self.bav1s))
        return self.bav1s[bop]
        
    def rule_TernaryOp(self, state, top, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
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
            condvar = self.getCondition(top)
            return self.store_content(full_statement,self.comma_expr(
                self.visitor_visit(state, lorExp, "GET_VAL", "ACCESS", **kwargs),
                self.if_abs(lambda: self.assign_var(condvar, self.ternary_expr(state, self.cp(state, "bav"), lambda state: self.nondet(), lambda state:self.visitor_visit(state, lorExp, "VALUE", "WSE", **kwargs)))),
                self.if_no_abs(lambda: self.assign_var(condvar, self.visitor_visit(state, lorExp, "VALUE", "WSE", **kwargs))),
                self.ternary_expr(state, condvar, 
                    lambda state: self.brackets(self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs)), 
                    lambda state: self.brackets(self.visitor_visit(state, condExp, "GET_VAL", "ACCESS", **kwargs)))
            ), top, abs_mode, dr_mode)
        else:
            assert(False)
    
    def __ptrop_dr(self, state, dr_mode, castExp, **kwargs):
        # if dr_mode is NO_ACCESS/PREFIX: remove
        # if abstraction:
        # return (bav)?(p2&&dr=(dr||wam||wkm)):(p2&&dr=(dr||wam||get_sm_dr(*[[castExp,VALUE,WSE]]))
        # else:
        # return p2&&dr=(dr||wam||get_sm_dr(*[[castExp,VALUE,WSE]])
        assert(self.dr_on)
        ok = lambda state: self.and_expr(self.p2code(self.getVpstate(**kwargs)), self.brackets(self.assign_with_prop(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), 
            self.getsm("*("+self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs)+")", self.sm_dr)))))
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
            return ok()   
            
    def __ptrop_abs(self, state, castExp, **kwargs):
        # return (bal = bav , bav = bav | get_sm_abs([[castExp,VALUE,WSE]]))
        assert(self.abs_on)
        bav_getsm = lambda: self.brackets(self.assign(state, "bav", self.getsm(self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs), self.sm_abs)))
        bav_bav_getsm = lambda: self.brackets(self.assign(state, "bav", self.bitor_expr(self.cp(state, "bav"), self.getsm(self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs), self.sm_abs))))
        
        cp = (state.cp_bal, state.cp_bav) #(bal, bav) as const propagation
        if cp[0] == 0 and cp[1] == 0: #bal = False, bav = False
            return bav_getsm() # bav = getsm
        elif cp[0] in (1, None) and cp[1] == 0: #bal = True/?, bav = False
            return self.comma_expr(self.assign_with_prop(state, "bal", self.cp(state, "bav")), bav_getsm()) #(bal = 0, bav = getsm)
        elif cp[0] == 1 and cp[1] == 1: #bal = True, bav = True
            return ""
        elif cp[0] in (0, None) and cp[1] == 1: #bal = False/?, bav = True
            return self.assign_with_prop(state, "bal", self.cp(state, "bav")) #(bal = 1)
        elif cp[1] is None: #bal = False/True/?, bav = ?
            return self.comma_expr(self.assign_with_prop(state, "bal", self.cp(state, "bav")), bav_bav_getsm())
        else:
            assert(False)     
                    
    def rule_PtrOp(self, state, ptrop, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        assert(ptrop.op == '*')
        castExp = ptrop.expr
        if abs_mode is None and dr_mode is None:
            return self.store_content(full_statement,"*("+self.visitor_visit(state, castExp, None, None, **kwargs)+")", ptrop, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL","UPD_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS","PREFIX",None):
            return self.store_content(full_statement,self.brackets(self.comma_expr(
                self.visitor_visit(state, castExp, "GET_VAL", "ACCESS", **kwargs),
                self.if_dr(lambda:self.__ptrop_dr(state, dr_mode, castExp, **kwargs)),
                self.if_abs(lambda:self.__ptrop_abs(state, castExp, **kwargs))
            )), ptrop, abs_mode, dr_mode)
        elif abs_mode in ("SET_VAL","GET_ADDR") and dr_mode in ("ACCESS","NO_ACCESS","PREFIX",None):
            return self.store_content(full_statement,self.comma_expr(
                self.visitor_visit(state, castExp, "GET_VAL", "ACCESS", **kwargs),
                self.assign_with_prop(state, "bal", self.cp(state, "bav"))
            ), ptrop, abs_mode, dr_mode)
        elif abs_mode in ("LVALUE", None) and dr_mode in ("WSE",None):
            return self.store_content(full_statement,"*("+self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs)+")", ptrop, abs_mode, dr_mode)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            castExpType = self.supportFile.get_type(castExp) #"int" # TODO type
            return self.store_content(full_statement,self.decode("*("+self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs)+")", castExpType), ptrop, abs_mode, dr_mode)
        else:
            assert(False)
            
    def rule_AddrOp(self, state, addrop, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        assert(addrop.op == '&')
        castExp = addrop.expr
        if abs_mode is None and dr_mode is None:
            return self.store_content(full_statement,"&("+self.visitor_visit(state, castExp, None, None, **kwargs)+")", addrop, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS",None):
            return self.store_content(full_statement,self.comma_expr(
                self.visitor_visit(state, castExp, "GET_ADDR", "NO_ACCESS", **kwargs),
                self.if_abs(lambda: self.assign_with_prop(state, "bav", self.cp(state, "bal")))
            ), addrop, abs_mode, dr_mode)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            return self.store_content(full_statement,"&("+self.visitor_visit(state, castExp, "LVALUE", "WSE", **kwargs)+")", addrop, abs_mode, dr_mode)
        else:
            assert(False)
            
    def _not_getval(self, state, notop, **kwargs):
        # returns value = value = (([[castExp, GET_VAL, ACCESS]], bav) ? nondetbool(), :![[castexp, VALUE, WSE]])
        # and applies constant propagation
        castExp = notop.expr
        ok = lambda state: "!("+self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs)+")" 
        err = lambda state: self.nondet()
        if not self.abs_on:
        	return self.assign_var(value, ok(state))
        castexp_getval = self.visitor_visit(state, castExp, "GET_VAL", "ACCESS", **kwargs)
        value = self.getCondition(notop)
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
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        assert(notop.op == '!')
        castExp = notop.expr
        if abs_mode is None and dr_mode is None:
            return self.store_content(full_statement,"!("+self.visitor_visit(state, castExp, None, None, **kwargs)+")", notop, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","PREFIX","NO_ACCESS",None):
            return self.store_content(full_statement,self._not_getval(state, notop, **kwargs), notop, abs_mode, dr_mode)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            return self.getCondition(notop)
        else:
            assert(False)
            
    def rule_UnOp(self, state, unop, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        assert(unop.op in ('+','-','~'))
        castExp = unop.expr
        unOp = unop.op
        if abs_mode is None and dr_mode is None:
            return self.store_content(full_statement,unOp+"("+self.visitor_visit(state, castExp, None, None, **kwargs)+")", unop, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","PREFIX","NO_ACCESS",None):
            return self.store_content(full_statement,self.comma_expr(
                self.visitor_visit(state, castExp, "GET_VAL", "ACCESS", **kwargs)), unop, abs_mode, dr_mode)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            return self.store_content(full_statement,unOp+"("+self.visitor_visit(state, castExp, "VALUE", "WSE", **kwargs)+")", unop, abs_mode, dr_mode)
        else:
            assert(False)
            
    def rule_Sizeof(self, state, sizeof, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        assert(sizeof.op in ('sizeof',))
        unexp_type = sizeof.expr
        if abs_mode is None and dr_mode is None:
            return self.store_content(full_statement,"sizeof("+self.visitor_visit(state, unexp_type, None, None, **kwargs)+")", sizeof, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS",None):
            return self.store_content(full_statement,self.assign_with_prop(state, "bav", "0"), sizeof, abs_mode, dr_mode)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            ans = "sizeof("+self.visitor_visit_noinstr(unexp_type)+")"
            return self.store_content(full_statement,ans, sizeof, abs_mode, dr_mode)
        else:
            assert(False)
            
    def rule_Comma(self, state, comma, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs) 
        exps = comma.exprs
        if abs_mode is None and dr_mode is None:
            parts = [self.visitor_visit(state, x, None, None, **kwargs) for x in exps]
            return (self.store_content(full_statement,'('+', '.join(parts)+')', comma, abs_mode, dr_mode), parts) #This should be the only place where you need the second argument
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS",'PREFIX',None):
            parts = [self.visitor_visit(state, x, "GET_VAL", "NO_ACCESS", **kwargs) for x in exps[:-1]] + \
                [self.visitor_visit(state, exps[-1], "GET_VAL", "NO_ACCESS" if dr_mode == "NO_ACCESS" else "ACCESS", **kwargs)]
            return (self.store_content(full_statement,'('+', '.join(parts)+')', comma, abs_mode, dr_mode), None)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            return (self.store_content(full_statement,self.visitor_visit(state, exps[-1], "VALUE", "WSE", **kwargs), comma, abs_mode, dr_mode), None)
        else:
            assert(False)
            
    def __malloc_inner(self, state, **kwargs):
        # bav && fail()
        if not self.abs_on or state.cp_bav == 0:
            return ""
        elif state.cp_bav == 1:
            return self.fail_expr()
        elif state.cp_bav is None:
            return self.assert_expr("!"+self.bav)
        else:
            assert(False)
            
    def rule_Malloc(self, state, fullExpr, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs) 
        exp = fullExpr.args
        fncName = fullExpr.name.name
        if abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            ans = fncName+"("+self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)+")"
            return self.store_content(full_statement,ans, \
                fullExpr, abs_mode, dr_mode)
        
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("NO_ACCESS","ACCESS","PREFIX",None):
            return self.store_content(full_statement, \
                self.comma_expr(
                    self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs),
                    self.__malloc_inner(state, **kwargs)
                ) \
            , fullExpr, abs_mode, dr_mode)
        else:
            assert(False)
            
            
    def __assert_assume_inner(self, state, exp, fncName, **kwargs):
        assert(fncName in ("assert", "__CPROVER_assume"))
        if not self.abs_on or state.cp_bav == 0:
            return self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)
        elif state.cp_bav == 1:
            return "0" if fncName == "assert" else "1"
        elif state.cp_bav is None:
            pfx = "!" if fncName == "assert" else ""
            return pfx + "(" + self.bitor_expr(self.cp(state, "bav"), pfx+"("+self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)+")") + ")"
        else:
            assert(False)
                
    def rule_Assert_Assume(self, state, fullExpr, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs) 
        exp = fullExpr.args
        fncName = fullExpr.name.name
        # TODO this is already done by the backend's instrumenter on the c file, but it does not act on the macro file. Therefore I'll do it now here
        if fncName == "__CSEQ_assert":
            fncName = "assert"
        elif fncName == "__CSEQ_assume":
            fncName = "__CPROVER_assume"
        if abs_mode in ("GET_VAL",None) and dr_mode in ("NO_ACCESS",None):
            return self.store_content(full_statement,fncName+"("+ \
                self.comma_expr(
                    self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs),
                    self.__assert_assume_inner(state, exp, fncName, **kwargs)
                ) \
            +")", fullExpr, abs_mode, dr_mode)
        else:
            assert(False)
            
    def fakeIfAssignment(self, n):
        return self.assign_var("___fakeifvar___", n)
            
    def rule_IfCond(self, state, exp, abs_mode, dr_mode, full_statement, **kwargs):
        exp_getval = self.visitor_visit(state, exp, "GET_VAL", "ACCESS", **kwargs)
        exp_val = lambda state: self.visitor_visit(state, exp, "VALUE", "WSE", **kwargs)
        
        if not self.abs_on or state.cp_bav == 0:
            return self.store_content(full_statement,self.fakeIfAssignment(self.comma_expr(exp_getval, exp_val(state))), exp, abs_mode, dr_mode)
        elif state.cp_bav == 1:
            return self.store_content(full_statement,self.fakeIfAssignment(self.comma_expr(exp_getval, self.nondet())), exp, abs_mode, dr_mode)
        elif state.cp_bav is None:
            texp = self.ternary_expr(state, self.cp(state, "bav"),lambda state: self.nondet(), exp_val)
            return self.store_content(full_statement,self.fakeIfAssignment(self.comma_expr(exp_getval, texp)), exp, abs_mode, dr_mode)
        else:
            assert(False)
    
    def rule_Cast(self, state, cast, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        unExpr = cast.expr
        toType = cast.to_type
        if abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            ans = "("+self.visitor_visit_noinstr(toType)+") "+ \
                self.visitor_visit(state, unExpr, "VALUE", "WSE", **kwargs)
            return self.store_content(full_statement, ans, cast, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS",'PREFIX',None):
            return self.store_content(full_statement,self.visitor_visit(state, unExpr, "GET_VAL", "NO_ACCESS" if dr_mode == "NO_ACCESS" else "ACCESS", **kwargs), cast, abs_mode, dr_mode)
        else:
            assert(False)
    
    def __binaryop_bav(self, state, exp1, exp2, op, fullOp, **kwargs):
        # returns bav = bav1 || bav
        # using constant propagation     
        assert(self.abs_on)
        bav1 = self.getBav1(fullOp)
        cp = (state.cp_bav, state.cp_bav1[bav1]) #(bav, bav_1) as const propagation
        if cp[0] == 1: #(True, x)
            return ""
        if cp[1] == 1: #(x, True)
            return self.assign_with_prop(state, "bav", "1")
        e1_op_e2_type = self.supportFile.get_type(fullOp) #"int" # TODO
        e1_op_e2 = lambda: "("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+")"
        isAbs = self.is_abstractable(e1_op_e2_type)
        if cp[0] == 0 and cp[1] == 0: #(False, False)
            return ""
        if cp[0] == 0: #(False, ?)
            return self.assign(state, "bav", bav1)
        if cp[1] == 0: #(?, False)
            return ""
        if cp[0] is None and cp[1] is None: #(?,?)
            return self.assign(state, "bav",self.bitor_expr(bav1 ,self.cp(state,"bav")))
        assert(False)
    
    '''        
    def __binaryop_bav(self, state, exp1, exp2, op, fullOp, **kwargs):
        # returns bav = bav1 || bav
        # using constant propagation
        assert(self.abs_on)
        cp = (state.cp_bav, state.cp_bav_1) #(bav, bav_1) as const propagation
        if cp[0] == 1: #(True, x)
            return ""
        if cp[1] == 1: #(x, True)
            return self.assign_with_prop(state, "bav", "1")
        e1_op_e2_type = self.supportFile.get_type(fullOp) #"int" # TODO
        e1_op_e2 = lambda: "("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+" "+op+" "+self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+")"
        isAbs = self.is_abstractable(e1_op_e2_type)
        if cp[0] == 0 and cp[1] == 0: #(False, False)
            return ""
        if cp[0] == 0: #(False, ?)
            return self.assign(state, "bav",self.cp(state,"bav_1"))
        if cp[1] == 0: #(?, False)
            return ""
        if cp[0] is None and cp[1] is None: #(?,?)
            return self.assign(state, "bav",self.or_expr(self.cp(state,"bav_1"),self.cp(state,"bav")))
        assert(False)'''
        
    def __binaryShortCircuit_internal(self, state, expr, **kwargs):
        # return (([[expr, GET_VAL, ACCESS]], bav)? nondet : [[expr, VALUE]])
        # with cp
        expr_getval = self.visitor_visit(state, expr, "GET_VAL", "ACCESS", **kwargs)
        expr_val = lambda state: self.visitor_visit(state, expr, "VALUE", "WSE", **kwargs)
        if not self.abs_on or state.cp_bav == 0:
            return self.comma_expr(expr_getval, expr_val(state))
        elif state.cp_bav == 1:
            return self.comma_expr(expr_getval, self.nondet())
        elif state.cp_bav is None:
            return self.ternary_expr(state, self.comma_expr(expr_getval,self.cp(state, "bav")), lambda state: self.nondet(), expr_val)
            
    def do_join_op(self, state, expr1, expr2, op, **kwargs):
        val1 = self.visitor_visit(state, expr1, "VALUE", "WSE", **kwargs)
        val2 = self.visitor_visit(state, expr2, "VALUE", "WSE", **kwargs)
        if op[0] == "&":
            return "("+self.bav_tmp+" || "+ val1 +") && ("+self.bav+" || "+ val2 +") && !(("+self.bav_tmp+" || "+self.bav+") && nondet_bool())" #((!("+self.bav_tmp+" || "+self.bav+")) || nondet_bool())"
        else:
            return "("+self.bav_tmp+" && (!"+ val1 +")) || ("+self.bav+" && (!"+ val2 +")) || (("+self.bav_tmp+" || "+self.bav+") && nondet_bool())"
        
    def rule_OrAnd(self, state, fullOp, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        exp1 = fullOp.left
        exp2 = fullOp.right
        k = self.plain_visitor.visit(exp2)
        if self.has_side_effects.check(k):
            return self.rule_OrAndOrig(state, fullOp, abs_mode, dr_mode, full_statement, **kwargs)
        
        #return self.visitor_visit_noinstr(fullOp)
        
        assert(fullOp.op in ("||", "&&"))
        
        if abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            return self.getCondition(fullOp)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS",'PREFIX',None):
            value = self.getCondition(fullOp)
            #exp1_tr = self.__binaryShortCircuit_internal(state, exp1, **kwargs)
            #stateBetween = state.copy()
            #exp2_tr = self.__binaryShortCircuit_internal(state, exp2, **kwargs)
            #state.doMerge(state, stateBetween)
            
            
            joinop = lambda: self.do_join_op(state, exp1, exp2, fullOp.op[0], **kwargs)
        
            return self.store_content(full_statement,self.comma_expr(
                self.visitor_visit(state, exp1, "GET_VAL", "ACCESS", **kwargs),
                self.assign_with_prop(state, "bav_tmp", self.cp(state,"bav")),
                self.visitor_visit(state, exp2, "GET_VAL", "ACCESS", **kwargs),
                self.assign_var(value, joinop()),
                self.if_abs(lambda: self.assign_with_prop(state, "bav", "0"))
            ), fullOp, abs_mode, dr_mode)
        else:
            assert(False)
            
    def rule_OrAndOrig(self, state, fullOp, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        exp1 = fullOp.left
        exp2 = fullOp.right
        
        #return self.visitor_visit_noinstr(fullOp)
        
        assert(fullOp.op in ("||", "&&"))
        
        if abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            return self.getCondition(fullOp)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS",'PREFIX',None):
            value = self.getCondition(fullOp)
            exp1_tr = self.__binaryShortCircuit_internal(state, exp1, **kwargs)
            stateBetween = state.copy()
            exp2_tr = self.__binaryShortCircuit_internal(state, exp2, **kwargs)
            state.doMerge(state, stateBetween)
            
            k = self.plain_visitor.visit(exp2)
            op = fullOp.op if self.has_side_effects.check(k) else fullOp.op[0]
        
            return self.store_content(full_statement,self.comma_expr(
                self.assign_var(value, "("+exp1_tr + " " + op + " " +exp2_tr+")"),
                self.if_abs(lambda: self.assign_with_prop(state, "bav", "0"))
            ), fullOp, abs_mode, dr_mode)
        else:
            assert(False)
            
    def rule_BinaryOp(self, state, fullOp, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        exp1 = fullOp.left
        exp2 = fullOp.right
        op = fullOp.op
        
        assert(op in ('|','^','&','==','!=','<','<=','>','>=','<<','>>','+','-','*','/','%'))
        
        if abs_mode in ("VALUE", None) and dr_mode in ("WSE",None):
            ans = "(("+self.visitor_visit(state, exp1, "VALUE", "WSE", **kwargs)+") "+op+" ("+ \
                self.visitor_visit(state, exp2, "VALUE", "WSE", **kwargs)+"))"
            return self.store_content(full_statement, ans, fullOp, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",None) and dr_mode in ("ACCESS","NO_ACCESS",'PREFIX',None):
            bav1 = self.getBav1(fullOp)
            return self.store_content(full_statement,self.comma_expr(
                self.visitor_visit(state, exp1, "GET_VAL", "ACCESS", **kwargs),
                self.if_abs(lambda: self.assign_bav1_with_prop(state, bav1, self.cp(state, "bav"))), #self.assign_with_prop(state, "bav_1", self.cp(state, "bav"))),
                self.visitor_visit(state, exp2, "GET_VAL", "ACCESS", **kwargs),
                self.if_abs(lambda: self.__binaryop_bav(state, exp1, exp2, op, fullOp, **kwargs))
            ), fullOp, abs_mode, dr_mode)
        else:
            assert(False)
        
        
    def rule_ID(self, state, sid, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        if not self.abs_on and not self.dr_on:
            return sid.name
        elif abs_mode == "LVALUE":
            return sid.name
        elif abs_mode == "VALUE" :
            sidType = self.supportFile.get_type(sid) #"int" # TODO get type of ID from abstr
            return self.decode(sid.name, sidType) 
        elif dr_mode == "WSE": # and implicitly abs is disabled
            return sid.name
        else:
            return self.store_content(full_statement,self.comma_expr(
                self.if_dr(lambda: 
                    self.and_expr(
                        self.p2code(self.getVpstate(**kwargs)), 
                        self.brackets(self.assign_with_prop(state,"dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), self.getsm("&("+sid.name+")", self.sm_dr))))
                    ) if dr_mode != "NO_ACCESS" else ""),
                self.if_abs(lambda: self.assign_with_prop(state,"bal","0")),
                self.if_abs(lambda: (self.assign_with_prop(state,"bav",self.getsm("&("+sid.name+")", self.sm_abs)) if abs_mode in ("GET_VAL", "UPD_VAL") else ""))
            ), sid, abs_mode, dr_mode)
    
    def rule_ArrayID(self, state, sid, abs_mode, dr_mode, full_statement, **kwargs):   
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
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
                        self.brackets(self.assign_with_prop(state,"dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), self.getsm("&("+sid.name+")", self.sm_dr))))
                    ) if dr_mode not in ("NO_ACCESS", "PREFIX") else ""),
                self.if_abs(lambda: self.assign_with_prop(state,"bal","0")),
                self.if_abs(lambda: self.assign_with_prop(state,"bav","0") if abs_mode in ("GET_VAL", "UPD_VAL") else "")
            ), sid, abs_mode, dr_mode)
                    
    def rule_Constant(self, state, con, abs_mode, dr_mode, full_statement, **kwargs):      
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        assert(abs_mode not in ("SET_VAL", "GET_ADDR"), "Invalid: cannot get address or set the value of constants")
        if not self.abs_on and not self.dr_on:
            return con.value
        elif abs_mode == "VALUE" or dr_mode == "WSE":
            return con.value
        else:
            return self.if_abs(lambda:self.assign_with_prop(state,"bav", "0"))
            
    # nondeterministic returning function. Treat as a constant
    def rule_Nondet(self, state, fnc, abs_mode, dr_mode, full_statement, **kwargs):      
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        assert(abs_mode not in ("SET_VAL", "GET_ADDR"), "Invalid: cannot get address or set the value of constants")
        if not self.abs_on and not self.dr_on:
            return self.visitor_visit_noinstr(fnc)
        elif abs_mode == "VALUE" or dr_mode == "WSE":
            return self.visitor_visit_noinstr(fnc)
        else:
            return self.if_abs(lambda:self.assign_with_prop(state,"bav", "0"))
            
    # helper function: returns "p1 && (set_sm_dr(&[[unexp, LVALUE]],1), WKM=1)" and manually applies const propagation
    def __assignment_manual_cp_p1(self, state, unExpr, **kwargs):
        return self.and_expr(self.p1code(vpstate),
            self.comma_expr(
                self.setsm("&("+self.visitor_visit(state, unExpr, "LVALUE", "WSE", **kwargs)+")", self.sm_dr, "1"),
                self.assign(state, "wkm", "1")))
            
    # helper function: returns "p2 && (DR = DR || WAM || get_sm_dr(&[[unexp, LVALUE]]))" and manually applies const propagation
    def __assignment_manual_cp_p2(self, state, unExpr, **kwargs):
        return self.and_expr(self.p2code(vpstate),
            self.brackets(self.assign(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), 
                self.getsm("&("+self.visitor_visit(state, unExpr, "LVALUE", "WSE", **kwargs)+")", self.sm_dr))))
            )
    
    # helper function: returns "bal && fail()" and manually applies const propagation    
    def __assignment_manual_bal_fail(self, state):
        if state.cp_bal == 0:
            return ""
        elif state.cp_bal == 1:
            return fail_expr()
        elif state.cp_bal is None:
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
    def __assignment_manual_bav_fail(self, state):
        if state.cp_bav == 0:
            return ""
        elif state.cp_bav == 1:
            return fail_expr()
        elif state.cp_bav is None:
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
            
    def compileTimeBoundsFailure(self, typ, value):
        if typ in self.abstrTypesSigned:
            intVal = eval(value)
            mn = -2**(self.abstr_bits-1)
            mx = 2**(self.abstr_bits-1)-1
            return "0" if mn <= intVal and intVal <= mx else "1"
        elif typ in self.abstrTypesUnsigned:
            intVal = eval(value)
            mn = 0
            mx = 2**(self.abstr_bits)-1
            return "0" if mn <= intVal and intVal <= mx else "1"
        else:
            assert(False)
            
    def is_numeric_constant(self, v):
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
    def __assignment_bounds_failure(self, state, n, unExprType, **kwargs):
        #if not self.is_abstractable(unExprType):
        #    return ""
        #TODO check if bitwidth is compatible if vars have different abstraction bitwidths
        if type(n) in (c_ast.ArrayRef, c_ast.Assignment, c_ast.Struct, c_ast.StructRef, c_ast.Union, c_ast.ID): 
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
        elif type(n) in (c_ast.BinaryOp, c_ast.TernaryOp, c_ast.UnaryOp, c_ast.FuncCall):
            return self.bounds_failure(self.visitor_visit(state, n, "VALUE", "WSE", **kwargs), unExprType)
        elif type(n) is c_ast.ExprList:
            return self.__assignment_bounds_failure(state, n.exprs[-1], unExprType, **kwargs)
        elif type(n) is c_ast.Cast:
            return self.__assignment_bounds_failure(state, n.expr, unExprType, **kwargs)
        else:
            print(n)
            assert(False)
            
    def __assignment_big_ternary(self, state, unExp, op, assExp, unExprType, **kwargs):
        # (bav = bav | bav_lhs {if op != "="} | bf, bav? setsm([unExp, "LVALUE"], 1) : setsm([unExp, "LVALUE"], 0), unexpr = assexpr )
        bfbody = self.__assignment_bounds_failure(state, assExp, unExprType, **kwargs) if self.is_abstractable(unExprType) else "0"
        
        if op != "=":
            fullOp = lambda: self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs)+" "+op.replace("=","")+" "+self.visitor_visit(state, assExp, "VALUE", "WSE", **kwargs)
        
        assignment = lambda: self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+" = "+self.encode(self.visitor_visit(state, assExp, "VALUE", "WSE", **kwargs), unExprType) if op == "=" else self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+" = "+self.encode(fullOp(), unExprType)
        
        if state.cp_bav == 1:
            return self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "1") #setsm([unExp, "LVALUE"], 1)
        elif op != "=" and state.cp_bav_lhs == 1:
            return self.comma_expr(self.assign_with_prop(state, "bav", "1"), self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "1")) #bav = 1, setsm([unExp, "LVALUE"], 1)
        elif bfbody == "1":
            return self.comma_expr(self.assign_with_prop(state, "bav", "1"), self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "1")) #bav = 1, setsm([unExp, "LVALUE"], 1)
        elif state.cp_bav == 0 and bfbody == "0" and (op == "=" or state.cp_bav_lhs == 0):
            return self.comma_expr(self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "0"), assignment()) # (setsm([unExp, "LVALUE"], 0), assignment)
        else:
            return self.comma_expr(self.assign(state, "bav", self.bitor_expr(self.cp(state, "bav"), self.cp(state, "bav_lhs") if op != "=" else "", bfbody)),
                self.ternary_expr(state, self.cp(state, "bav"), 
                    lambda state: self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "1"),
                    lambda state: self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "0")), assignment())
                    
    def __incdec_big_ternary(self, state, unExp, op, assExp, unExprType, **kwargs):
        # (bav = bav | bf, bav? setsm([unExp, "LVALUE"], 1) : setsm([unExp, "LVALUE"], 0), unexpr = assexpr )
        bfbody = self.__assignment_bounds_failure(state, assExp, unExprType, **kwargs) if self.is_abstractable(unExprType) else "0"
        
        if op != "=":
            fullOp = lambda: self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs)+" "+op.replace("=","")+" "+self.visitor_visit(state, assExp, "VALUE", "WSE", **kwargs)
        
        assignment = lambda: self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+" = "+self.encode(self.visitor_visit(state, assExp, "VALUE", "WSE", **kwargs), unExprType) if op == "=" else self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+" = "+self.encode(fullOp(), unExprType)
        
        if state.cp_bav == 1:
            return self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "1") #setsm([unExp, "LVALUE"], 1)
        elif bfbody == "1":
            return self.comma_expr(self.assign_with_prop(state, "bav", "1"), self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "1")) #bav = 1, setsm([unExp, "LVALUE"], 1)
        elif state.cp_bav == 0 and bfbody == "0":
            return self.comma_expr(self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "0"), assignment()) # (setsm([unExp, "LVALUE"], 0), assignment)
        else:
            return self.comma_expr(self.assign(state, "bav", self.bitor_expr(self.cp(state, "bav"), bfbody)),
                self.ternary_expr(state, self.cp(state, "bav"), 
                    lambda state: self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "1"),
                    lambda state: self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "0")), assignment())
            
        
            
    #def isPlusPlus(self, assn):
    #    if type(assn.rvalue) is c_ast.BinaryOp and assn.rvalue.op == "+" left
    #    return assn.lvalue################################################################################################################################################
        
    def rule_Assignment(self, state, assn, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        #abs_mode = None
        #bkabs = self.abs_on
        #self.abs_on = False
        unExp = assn.lvalue
        assExp = assn.rvalue
        op = assn.op
        if abs_mode == "VALUE" or dr_mode == "WSE":
            ans = self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs)
            return self.store_content(full_statement,ans, assn, abs_mode, dr_mode)
        if op != "=":
            fullOp = lambda: self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs)+" "+op.replace("=","")+" "+self.visitor_visit(state, assExp, "VALUE", "WSE", **kwargs)
        
        if op == "=":
            assignee = assExp
        else:
            assignee = c_ast.BinaryOp(op.replace("=",""), unExp, assExp)
            
        unExprType = self.supportFile.get_type(unExp) #"int" #TODO proper type
        ans = self.comma_expr(
            self.if_abs_or_dr(lambda: self.visitor_visit(state, unExp, "SET_VAL" if op == "=" else "UPD_VAL", "NO_ACCESS", **kwargs)),
            self.if_abs(lambda: self.__assignment_manual_bal_fail(state) if op == "=" else self.__assignment_manual_bav_fail(state)),
            "" if op == "=" else self.if_abs(lambda: self.assign_with_prop(state,"bav_lhs", self.cp(state,"bav"))),
            self.if_dr(lambda: self.__assignment_manual_cp_p1(state, unExp, **kwargs)),
            self.if_dr(lambda: self.__assignment_manual_cp_p2(state, unExp, **kwargs)),
            self.if_abs_or_dr(lambda: self.visitor_visit(state, assExp, "GET_VAL", "ACCESS", **kwargs)),
            self.if_abs(lambda: self.__assignment_big_ternary(state, unExp, op, assignee, unExprType, **kwargs)),
            self.if_no_abs(lambda: self.visitor_visit(state, unExp, None, "WSE", **kwargs)+" = "+self.visitor_visit(state, assExp, None, "WSE", **kwargs) if op == "=" \
                else self.visitor_visit(state, unExp, None, "WSE", **kwargs)+" = "+fullOp())
        )
        ans2= self.store_content(full_statement, ans, assn, abs_mode, dr_mode)
        #self.abs_on = bkabs
        return ans2
        
        
    def __preop_manual_cp_bal(self,state, unExpr, vpstate):
        # if abstraction is on:
            # return bal?err:ok
            # where
            # err ::= (p1&&wam=1, p2&&dr=dr||wam||wkm)
            # ok  ::= (p1 && (set_sm_dr(&[[unexp, LVALUE]],1), WKM=1), p2 && (DR = DR || WAM || get_sm_dr(&[[unexp, LVALUE]]))) {i.e., __assignment_manual_cp_p1,__assignment_manual_cp_p2}
        # else: ok
        # applying manually the constant propagation
        assert(self.dr_on)
        err = lambda state: self.comma_expr(self.and_expr(self.p1code(vpstate), self.assign(state,"wam", self.cp(state, "wam"))),
                              self.and_expr(self.p2code(vpstate), self.assign(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), self.cp(state, "wkm")))))
        ok = lambda state: self.comma_expr(self.__assignment_manual_cp_p1(state, unExpr, vpstate),
                              self.__assignment_manual_cp_p2(state, unExpr, vpstate))
        if state.cp_bal == 0 or not self.abs_on:
            return ok(state)
        elif state.cp_bal == 1:
            return err(state)
        else:
            return self.ternary_expr(state, self.cp(state,"bal"),err,ok)
            
    def __preop_manual_cp_bav_bal(self,state, unExpr, op, unexprType, **kwargs):
        assert(self.abs_on)
        # unexprType is abstractable:
            # return (bav=bav||min_t([[unexp,VALUE]]))?err:ok
            # where
            # err ::= (bal||set_sm(&[[unexp,LVALUE]],1))
            # ok  ::= [[unexp,LVALUE]] = encode([[unexp,VALUE]] op 1)
        # unexprType is not abstractable:
            # return (bav || ([[unexp,LVALUE]] op op))
        # applying manually the constant propagation
        abstr_type = self.is_abstractable(unexprType)
        
        if abstr_type:
            mint = lambda: self.ismin_type(self.visitor_visit(state, unExpr, "VALUE", "WSE", **kwargs), unexprType) if op == '-' else self.ismax_type(self.visitor_visit(state, unExpr, "VALUE", "WSE", **kwargs), unexprType)
            setsm_1 = lambda state: self.setsm("&("+self.visitor_visit(state, unExpr, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "1")
            err = lambda state: setsm_1(state) if state.cp_bal == 0 else ( "" if state.cp_bal == 1 else self.or_expr(self.cp(state,"bal"), setsm_1(state)))
            ok = lambda state: self.brackets(self.visitor_visit(state, unExpr, "LVALUE", "WSE", **kwargs)+" = "+self.encode(self.visitor_visit(state, unExpr, "VALUE", "WSE", **kwargs)+" "+op+" 1", unexprType))
        
            if state.cp_bav == 1:
                return err(state)
            elif state.cp_bav == 0:
                return self.ternary_expr(state, self.assign(state, "bav", mint()), err, ok)
            else:
                return self.ternary_expr(state, self.brackets(self.assign(state, "bav", self.or_expr_prop(self.cp(state, "bav"),mint()))), err, ok)
        else:
            unexpr_op_op = lambda: self.visitor_visit(state, unExpr, "LVALUE", "WSE", **kwargs)+op+op
            
            if state.cp_bav == 1:
                return ""
            elif state.cp_bav == 0:
                return unexpr_op_op()
            else:
                return self.or_expr(self.cp(state,"bav"),unexpr_op_op())
        
        
    def rule_preOp(self, state, preop, abs_mode, dr_mode, full_statement, **kwargs): # --x, ++x
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        unExp = preop.expr
        op = preop.op
        assert(op in ("--","++"))
        assignee = c_ast.BinaryOp(op[-1], unExp, c_ast.Constant("int", "1"))
        if abs_mode is None and dr_mode in ("ACCESS", "PREFIX", "NO_ACCESS", None):
            intop = op[-1]
            unexprType = self.supportFile.get_type(unExp)#"int" #TODO proper type
            ans = self.comma_expr(
                self.if_dr(lambda: self.visitor_visit(state, unExp, "UPD_VAL", "NO_ACCESS", **kwargs)),
                self.if_dr(lambda: self.__preop_manual_cp_bal(state, unExp, self.getVpstate(**kwargs))),
                intop+intop+self.visitor_visit(state, unExp, None, "WSE", **kwargs))
            return self.store_content(full_statement,ans, preop, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",) and dr_mode in ("ACCESS", "PREFIX", "NO_ACCESS", None):
            unexprType = self.supportFile.get_type(unExp)#"int" #TODO proper type
            ans = self.comma_expr(
                self.visitor_visit(state, unExp, "UPD_VAL", "NO_ACCESS", **kwargs),
                self.__assignment_manual_bav_fail(state),
                self.if_dr(lambda: self.__assignment_manual_cp_p1(state, unExp, **kwargs)),
                self.if_dr(lambda: self.__assignment_manual_cp_p2(state, unExp, **kwargs)),
                self.if_abs(lambda: self.__incdec_big_ternary(state, unExp, "=", assignee, unexprType, **kwargs))
            )
            return self.store_content(full_statement,ans, preop, abs_mode, dr_mode)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE", None) and (abs_mode is not None or dr_mode is not None):
            return self.store_content(full_statement,self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs), preop, abs_mode, dr_mode)
        else:
            assert(False, "Invalid mode for preOp: abs_mode = "+str(abs_mode)+"; dr_mode = "+str(dr_mode))
        
        
    def rule_postOp(self, state, preop, abs_mode, dr_mode, full_statement, **kwargs): # x--, x++
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        unExp = preop.expr
        op = preop.op
        assert(op in ("p--","p++"))
        assignee = c_ast.BinaryOp(op[-1], unExp, c_ast.Constant("int", "1"))
        if abs_mode is None and dr_mode in ("ACCESS", "PREFIX", "NO_ACCESS", None):
            intop = op[-1]
            unexprType = self.supportFile.get_type(unExp)#"int" #TODO proper type
            ans = self.comma_expr(
                self.if_dr(lambda: self.visitor_visit(state, unExp, "UPD_VAL", "NO_ACCESS", **kwargs)),
                self.if_dr(lambda: self.__preop_manual_cp_bal(state, unExp, self.getVpstate(**kwargs))),
                self.visitor_visit(state, unExp, None, "WSE", **kwargs)+intop+intop)
            return self.store_content(full_statement,ans, preop, abs_mode, dr_mode)
        elif abs_mode in ("GET_VAL",) and dr_mode in ("ACCESS", "PREFIX", "NO_ACCESS", None):
            intop = op[-1]
            unexprType = self.supportFile.get_type(unExp)#"int" #TODO proper type
            ans = self.comma_expr(
                self.visitor_visit(state, unExp, "UPD_VAL", "NO_ACCESS", **kwargs),
                self.__assignment_manual_bav_fail(state),
                self.if_dr(lambda: self.__assignment_manual_cp_p1(state, unExp, **kwargs)),
                self.if_dr(lambda: self.__assignment_manual_cp_p2(state, unExp, **kwargs)),
                self.if_abs(lambda: self.__incdec_big_ternary(state, unExp, "=", assignee, unexprType, **kwargs))
            )
            return self.store_content(full_statement,ans, preop, abs_mode, dr_mode)
        elif abs_mode in ("VALUE", None) and dr_mode in ("WSE", None) and (abs_mode is not None or dr_mode is not None):
            intop = op[-1]
            invertOp = "+" if intop == "-" else "-" #invert the operator to get access to the value before op
            return self.store_content(full_statement,self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs)+" "+invertOp+" 1", preop, abs_mode, dr_mode)
        else:
            assert(False, "Invalid mode for postOp: abs_mode = "+str(abs_mode)+"; dr_mode = "+str(dr_mode))
         
            
    def rule_SpecialFuncCall(self, state, fcall, abs_mode, dr_mode, full_statement, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        kwargs_nobavtest = {k:kwargs[k] for k in kwargs if k != "bavtest"}
        return self.comma_expr(
            self.if_abs(lambda: self.comma_expr(*[self.comma_expr(self.visitor_visit(state, x, "GET_VAL", "NO_ACCESS", **kwargs_nobavtest), self.__assignment_manual_bav_fail(state)) for x in kwargs["bavtest"]])),
            self.visitor_visit_noinstr(fcall))
            
