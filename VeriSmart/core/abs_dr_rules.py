from pycparser import c_ast

class CPState:
    def __init__(self):
        # Constant propagation: <value> = it is already known without reading it; None = must read it
        self.cp_bav = None 
        self.cp_bav_lhs = None 
        self.cp_bal = None 
        self.cp_dr = None 
        self.cp_wam = None 
        self.cp_wkm = None 
        
class VPState:
    def __init__(self):
        self.VP1required = False
        self.VP2required = False
        
class AbsDrRules:            
    # TODO create a boilerplate code to define needed vars
    
    def __init__(self, visitor, abs_on, dr_possible, abstr_bits):
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
        # abstraction: signed types for which abstraction is enabled
        self.abstrTypesSigned = ["int"] if abs_on else []
        # abstraction: unsigned types for which abstraction is enabled
        self.abstrTypesUnsigned = ["unsigned int"] if abs_on else []
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
        
        # abstraction: name field for dr
        self.sm_dr = "dr" if dr_possible else None
        
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
            self.if_abs(lambda: "unsigned char "+self.bav+" = (unsigned char) 0;"),
            self.if_abs(lambda: "unsigned char "+self.bal+" = (unsigned char) 0;"),
            self.if_abs(lambda: "unsigned char "+self.bav_lhs+" = (unsigned char) 0;"),
            self.if_dr_possible(lambda: "unsigned char "+self.dr+" = (unsigned char) 0;"),
            self.if_dr_possible(lambda: "unsigned char "+self.wam+" = (unsigned char) 0;"),
            self.if_dr_possible(lambda: "unsigned char "+self.wkm+" = (unsigned char) 0;"),
            self.if_dr_possible(lambda: 'unsigned char __cs_dataraceDetectionStarted = (unsigned char) 0;'),
            self.if_dr_possible(lambda: 'unsigned char __cs_dataraceSecondThread = (unsigned char) 0;'),
            self.if_dr_possible(lambda: 'unsigned char __cs_dataraceNotDetected = (unsigned char) 1;'),
            self.if_dr_possible(lambda: 'unsigned char __cs_dataraceContinue = (unsigned char) 1;'),
            self.if_dr_possible(lambda: 'unsigned char __cs_dataraceActiveVP1 = (unsigned char) 0;'),
            self.if_dr_possible(lambda: 'unsigned char __cs_dataraceActiveVP2 = (unsigned char) 0;'),
        ]))[0]
        
    def sm_field_decl(self):
        return "#define FIELD_DECLS() "+self.compound_expr(" ",*([
            self.if_abs(lambda: '__CPROVER_field_decl_global("'+self.sm_abs+'", (_Bool)0);'),
            self.if_dr(lambda: '__CPROVER_field_decl_global("'+self.sm_dr+'", (_Bool)0);'),
        ]))[0]
        
    def macro_file_content(self):
        assert(self.abs_on or self.dr_on, "External macro file is meaningful only if we have abstraction or dr")
        if self.abs_on:
            bitstr = str(self.abstr_bits)
            bitstr_1 = str(self.abstr_bits-1)
            mask_t = hex(2**self.abstr_bits-1)
            mask_t_1 = hex(2**(self.abstr_bits-1)-1)
        return self.compound_expr("\n",*([
            self.if_abs(lambda: "#define MASK_"+bitstr_1+" "+mask_t_1),
            self.if_abs(lambda: "#define MASK_"+bitstr+" "+mask_t),
            self.sm_field_decl(),
        ]+[
            "#define BOUNDS_FAILURE_"+t.replace(" ","_")+"(exp) ((((exp)&~MASK_"+bitstr_1+")!=(~MASK_"+bitstr_1+")) && ((exp)&~MASK_"+bitstr_1+"))" for t in self.abstrTypesSigned
        ]+[
            "#define BOUNDS_FAILURE_"+t.replace(" ","_")+"(exp) ((exp)&~MASK_"+bitstr+")" for t in self.abstrTypesUnsigned
        ]))[0]
        
    def get_first_state(self):
        s = CPState()
        return s
        
    def enableDr(self):
        self.dr_on = True
        
    def disableDr(self):
        self.dr_on = False
        
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
            
    # join parts to form a comma expression
    def comma_expr(self, *items):
        commas, parts = self.compound_expr(", ", items)
        if parts >=2 :
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
            return "1"
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
        
    # join parts to form an and expression
    def and_expr(self, *items):
        ands, parts = self.compound_expr(" && ", *items)
        if parts == 0:
            return "0"
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
        if val == getattr(state, "cp_"+target):
            # value is the same as in cp: I don't even need to assign
            return ""
        if val == "0":
            setattr(state, "cp_"+target, 0)    
        elif val == "1":
            setattr(state, "cp_"+target, 1)   
        else:
            setattr(state, "cp_"+target, None)   
        return getattr(self, target) + " = " + val
        
    # assignment disabling self propagation
    def assign(self, state, target, val):
        setattr(state, "cp_"+target, None)   
        return getattr(self, target) + " = " + val
        
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
        
    def decode(self, x, xtype):
        assert(self.abs_on)
        xtype_nospaces = xtype.replace(" ","_")
        return "DECODE_"+xtype_nospaces+"("+x+")"
        
    def encode(self, x, xtype):
        assert(self.abs_on)
        xtype_nospaces = xtype.replace(" ","_")
        return "ENCODE_"+xtype_nospaces+"("+x+")"
        
    def bounds_failure(self, x, xtype):
        assert(self.abs_on)
        xtype_nospaces = xtype.replace(" ","_")
        return "BOUNDS_FAILURE_"+xtype_nospaces+"("+x+")"
        
    def ternary_expr(self, cond, then, els):
        return "(" + cond + "?" + then + ":" + els + ")"
        
    def assert_expr(self, val):
        return "__CSEQ_assert("+val+")"
        
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
        return self.visitor.visit_with_absdr_args(state, n, abs_mode if self.abs_on else None, dr_mode if self.dr_on else None, **kwargs)
        
    def rule_ID(self, state, sid, abs_mode, dr_mode, **kwargs):
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)
        #TODO this is possible! assert(not(dr_mode == "NO_ACCESS" and abs_mode in ("SET_VAL", "GET_ADDR")))
        if not self.abs_on and not self.dr_on:
            return sid.name
        elif abs_mode == "LVALUE":
            return sid.name
        elif abs_mode == "VALUE" :
            return self.decode(sid.name, "int") # TODO get type of ID from abstr
        elif dr_mode == "WSE": # and implicitly abs is disabled
            return sid.name
        else:
            return self.comma_expr(
                self.if_dr(lambda: 
                    self.and_expr(
                        self.p2code(self.getVpstate(**kwargs)), 
                        self.brackets(self.assign_with_prop(state,"dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), self.getsm("&("+sid.name+")", self.sm_dr))))
                    ) if dr_mode != "NO_ACCESS" else ""),
                self.if_abs(lambda: self.assign_with_prop(state,"bal","0")),
                self.if_abs(lambda: self.assign_with_prop(state,"bav",self.getsm("&("+sid.name+")", self.sm_abs)) if abs_mode in ("GET_VAL", "UPD_VAL") else "")
            )
            
    def rule_Constant(self, state, con, abs_mode, dr_mode, **kwargs):      
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        assert(abs_mode not in ("SET_VAL", "GET_ADDR"), "Invalid: cannot get address or set the value of constants")
        if not self.abs_on and not self.dr_on:
            return con.value
        elif abs_mode == "VALUE" or dr_mode == "WSE":
            return con.value
        else:
            return self.if_abs(lambda:self.assign_with_prop(state,"bav", "0"))
            
    # helper function: returns "p1 && (set_sm_dr(&[[unexp, LVALUE]],1), WKM=1)" and manually applies const propagation
    def __assignment_manual_cp_p1(self, state, unExpr, vpstate):
        return self.and_expr(self.p1code(vpstate),
            self.comma_expr(
                self.setsm("&("+self.visitor_visit(state, unExpr, "LVALUE", "WSE", dr_vp_state=vpstate)+")", self.sm_dr, "1"),
                self.assign(state, "wkm", "1")))
            
    # helper function: returns "p2 && (DR = DR || WAM || get_sm_dr(&[[unexp, LVALUE]]))" and manually applies const propagation
    def __assignment_manual_cp_p2(self, state, unExpr, vpstate):
        return self.and_expr(self.p2code(vpstate),
            self.brackets(self.assign(state, "dr", self.or_expr_prop(self.cp(state, "dr"), self.cp(state, "wam"), 
                self.getsm("&("+self.visitor_visit(state, unExpr, "LVALUE", "WSE", dr_vp_state=vpstate)+")", self.sm_dr))))
            )
    
    # helper function: returns "bal && fail()" and manually applies const propagation    
    def __assignment_manual_bal_fail(self, state):
        return self.assert_expr("!"+self.bal)
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
        return self.assert_expr("!"+self.bav)
        '''if state.cp_bav is None:
            return self.and_expr(self.bav, self.fail_expr())
        elif state.cp_bav == 0:
            return ""
        elif state.cp_bav == 1:
            return self.fail_expr()
        else:
            assert(False, "Invalid bav: "+str(state.cp_bav))'''
        
    def rule_Assignment(self, state, assn, abs_mode, dr_mode, **kwargs):      
        self.assertDisabledIIFModesAreNone(abs_mode, dr_mode, **kwargs)  
        unExp = assn.lvalue
        assExp = assn.rvalue
        op = assn.op
        if op != "=":
            fullOp = lambda: self.visitor_visit(state, unExp, "VALUE", "WSE", **kwargs)+" "+op.replace("=","")+" "+self.visitor_visit(state, assExp, "VALUE", "WSE", **kwargs)
        unexprType = "int" #TODO proper type
        return self.comma_expr(
            self.if_abs_or_dr(lambda: self.visitor_visit(state, unExp, "SET_VAL" if op == "=" else "UPD_VAL", "NO_ACCESS", **kwargs)),
            self.if_abs(lambda: self.__assignment_manual_bal_fail(state) if op == "=" else self.__assignment_manual_bav_fail(state)),
            "" if op == "=" else self.if_abs(lambda: self.assign_with_prop(state,"bav_lhs", self.cp(state,"bav"))),
            self.if_dr(lambda: self.__assignment_manual_cp_p1(state, unExp, self.getVpstate(**kwargs))),
            self.if_dr(lambda: self.__assignment_manual_cp_p2(state, unExp, self.getVpstate(**kwargs))),
            self.if_abs_or_dr(lambda: self.visitor_visit(state, assExp, "GET_VAL", "ACCESS", **kwargs)),
            self.if_abs(lambda:
                self.ternary_expr( 
                    self.or_expr_prop(
                        self.cp(state, "bav"),
                        "" if op == "=" else self.cp(state, "bav_lhs"),
                        self.bounds_failure(self.visitor_visit(state, assExp, "VALUE", "WSE"), unexprType) if op == "=" else 
                            self.bounds_failure(fullOp(), unexprType)
                    ),
                    self.comma_expr(
                        self.assign(state, "bav", "1"),
                        self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "1")
                    ), 
                    self.comma_expr(
                        self.setsm("&("+self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+")", self.sm_abs, "0"),
                        self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+" = "+self.encode(self.visitor_visit(state, assExp, "VALUE", "WSE", **kwargs), unexprType) if op == "=" else "",
                        "" if op == "=" else self.visitor_visit(state, unExp, "LVALUE", "WSE", **kwargs)+" = "+self.encode(fullOp(), unexprType),
                    ))
            ),
            self.if_no_abs(lambda: self.visitor_visit(state, unExp, None, "WSE", **kwargs)+" = "+self.visitor_visit(state, assExp, None, "WSE", **kwargs) if op == "=" \
                else self.visitor_visit(state, unExp, None, "WSE", **kwargs)+" = "+fullOp())
        )
            
            
            
            
