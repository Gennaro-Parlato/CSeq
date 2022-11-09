from pycparser import CParser
from pycparser.c_generator import CGenerator
from pycparser.c_ast import *
import time
import copy

class Cleaner(CGenerator):
    # remove useless assignments, i.e., x = 0 or x = getsm... where x is an interesting_var
    
    def __init__(self, doClean = True):
        self.parser = CParser()
        self.generate = CGenerator()
        self.doClean = doClean
        self.typedefs = ""
        self.typedefList = ["char ___fakeifvar___;"]
        
        self.codes_to_clean = dict()
        self.clean_codes = dict()
        
    def addTypedef(self, txt):
        self.typedefList.append(txt+";")
        
    def add_code_to_clean(self, key, code):
        if code.strip() in (";",""):
            self.clean_codes[key] = code
        else:
            self.codes_to_clean[key] = code
        
    def do_clean_codes(self):
        if self.doClean:
            self.side_effects = HasSideEffects(keep_void0 = True)
            if len(self.typedefList) > 0:
                txt = "\n".join(self.typedefList)
                self.typedefs += txt + "\n"
                self.typedefList = []
            code = "\n".join([k+": "+self.codes_to_clean[k]+";" for k in self.codes_to_clean])
            with_boilerplate = self.typedefs + "void main(){"+code+"}"
            print("A")
            parsed = self.parser.parse(with_boilerplate) # 6 sec
            print("B")
            if parsed.ext[-1].body.block_items is not None:
                #print("C", len(parsed.ext[-1].body.block_items))
                for label_stmt in parsed.ext[-1].body.block_items:
                    if type(label_stmt) is not EmptyStatement:
                        clean_ast = self.visit(label_stmt.stmt)['code']
                        #self.clean_codes[label_stmt.name] = self.generate.visit(clean_ast).replace("___fakeifvar___ = ","")
                #print("X")
            for k in self.codes_to_clean:
                self.clean_codes[k] = self.codes_to_clean[k].replace("___fakeifvar___ = ","")
        else:
            for k in self.codes_to_clean:
                self.clean_codes[k] = self.codes_to_clean[k].replace("___fakeifvar___ = ","")
                
    def get_clean_codes(self):
        return self.clean_codes
        
    '''def clean(self, code):
        if self.doClean:
            if len(self.typedefList) > 0:
                txt = "\n".join(self.typedefList)
                self.typedefs += txt + "\n"
                self.typedefList = []
            with_boilerplate = self.typedefs + "void main(){"+code+";}"
            parsed = self.parser.parse(with_boilerplate)
            ans = self.visit(parsed.ext[-1].body.block_items[0])['code']
            return self.generate.visit(ans)
        else:
            return code'''
        
    def interesting_vars(self, name):
        if name is None:
            return False
        return name == "__cs_baL" or name.startswith("__cs_cond_") or name.startswith("__cs_baV") or name.startswith("__cs_baP")
        
    def visit(self, node, read=False, acctable= dict(), posright=0):
        method = 'visit_' + node.__class__.__name__
        return getattr(self, method, self.generic_visit)(node, read, acctable, posright)
    
    def visit_Constant(self, n, read=False, acctable= dict(), posright=0):
        return {'code':n, 'acctable':acctable, 'posright':posright-1}
        
    def visit_Typename(self, n, read=False, acctable= dict(), posright=0):
        return {'code':n, 'acctable':acctable, 'posright':posright-1}
        
    def visit_ID(self, n, read=False, acctable= dict(), posright=0):
        if read and self.interesting_vars(n.name):
            acctable[n.name] = posright
        return {'code':n, 'acctable':acctable, 'posright':posright-1}
        
    def visit_ArrayRef(self, n, read=False, acctable= dict(), posright=0):
        visit_subscript = self.visit(n.subscript, read=True, acctable=acctable, posright=posright)
        posright = visit_subscript['posright']
        visit_name = self.visit(n.name, read=True, acctable=acctable, posright=posright)
        posright = visit_name['posright']
        return {'code': ArrayRef(visit_name['code'], visit_subscript['code']), 'acctable':acctable, 'posright':posright-1}
        
    def visit_StructRef(self, n, read=False, acctable= dict(), posright=0):
        visit_field = self.visit(n.field, read=read, acctable=acctable, posright=posright)
        posright = visit_field['posright']
        visit_name = self.visit(n.name, read=True, acctable=acctable, posright=posright)
        posright = visit_name['posright']
        return {'code': StructRef(visit_name['code'], n.type, visit_field['code']), 'acctable':acctable, 'posright':posright-1}
        
    def __check_encode_decode(self, n):
        # returns True if n is ENCODE_t((t) DECODE_t(...)) for some t TODO  fix
        return type(n) is FuncCall \
            and type(n.name) is ID \
            and n.name.name.startswith("ENCODE_") \
            and len(n.args.exprs) == 1 \
            and type(n.args.exprs[0]) is FuncCall \
            and type(n.args.exprs[0].name) is ID \
            and n.args.exprs[0].name.name == "DECODE_"+n.name.name[7:]
            
    def __check_boundsfailure_decode(self, n):
        # returns True if n is BOUNDS_FAILURE_t((t) DECODE_t(...)) for some t TODO  fix
        return type(n) is FuncCall \
            and type(n.name) is ID \
            and n.name.name.startswith("BOUNDS_FAILURE_") \
            and len(n.args.exprs) == 1 \
            and type(n.args.exprs[0]) is FuncCall \
            and type(n.args.exprs[0].name) is ID \
            and n.args.exprs[0].name.name == "DECODE_"+n.name.name[15:]

    def visit_FuncCall(self, n, read=False, acctable= dict(), posright=0):
        if n.args is None:
            return {'code':n, 'acctable':acctable, 'posright':posright-1}
        elif self.__check_encode_decode(n):
            return self.visit(n.args.exprs[0].args.exprs[0], read=read, acctable=acctable, posright=posright)
        elif self.__check_boundsfailure_decode(n):
            return self.visit(ExprList([n.args.exprs[0].args.exprs[0], Constant("int","0")]), read=read, acctable=acctable, posright=posright)
        else:
            visit_args = [None] * len(n.args.exprs)
            for i in range(len(n.args.exprs)-1, -1, -1):
                visit_args[i] = self.visit(n.args.exprs[i], read=True, acctable=acctable, posright=posright)
                posright = visit_args[i]['posright']

            visit_name = self.visit(n.name, read=True, acctable=acctable, posright=posright)
            posright = visit_name['posright']

            return {'code': FuncCall(visit_name['code'], ExprList([va['code'] for va in visit_args])), 'acctable':acctable, 'posright':posright-1}

    def visit_UnaryOp(self, n, read=False, acctable= dict(), posright=0):
        visit_expr = self.visit(n.expr, read=True, acctable=acctable, posright=posright)
        posright = visit_expr['posright']
        return {'code': UnaryOp(n.op, visit_expr['code']), 'acctable':acctable, 'posright':posright-1}

    def visit_BinaryOp(self, n, read=False, acctable= dict(), posright=0):
        visit_right = self.visit(n.right, read=True, acctable=acctable, posright=posright)
        posright = visit_right['posright']
        visit_left = self.visit(n.left, read=True, acctable=acctable, posright=posright)
        posright = visit_left['posright']
        return {'code': BinaryOp(n.op, visit_left['code'], visit_right['code']), 'acctable':acctable, 'posright':posright-1}
        
    def visitForName(self, n):
        if type(n) is ID:
            return n.name
        elif type(n) is UnaryOp:
            return None # never an interesting variable
        else:
            return self.visitForName(n.name)

    def isRead(self, acctable, nname, posright=float("+inf")):
        return nname in acctable and acctable[nname] <= posright

    def visit_Assignment(self, n, read=False, acctable= dict(), posright=0):
        posright1 = posright
        acctable1 = copy.deepcopy(acctable)

        nname = self.visitForName(n.lvalue)
        visit_rvalue = self.visit(n.rvalue, read=not(self.interesting_vars(nname) and not self.isRead(acctable, nname)), acctable=acctable, posright=posright)
        posright = visit_rvalue['posright']
        acctable2 = copy.deepcopy(acctable)

        visit_lvalue = self.visit(n.lvalue, read=(n.op != "="), acctable=acctable, posright=posright)
        #read_IDs = visit_lvalue['read_IDs']
        posright = visit_lvalue['posright']
        if self.interesting_vars(nname) and not self.isRead(acctable, nname):
            # n.lvalue will never be read afterwards: don't do the assignment
            if not read and not self.side_effects.visit(n.rvalue):
                # the rvalue is not read and it does not have side effects (e.g. constant or read from sm): don't even write the rvalue!
                if n.op == "=": 
                    # nname is overwritten without reading it. This value is discarded for the newly assigned one
                    acctable1.pop(nname, None)
                return {'code': EmptyStatement(), 'acctable': acctable1, 'posright': posright-1}
            else:
                return {'code': visit_rvalue['code'], 'acctable': acctable2, 'posright': posright-1}
        else:
            #visit_rvalue_without_after = self.visit(n.rvalue, read=not(self.interesting_vars(nname) and nname not in after), after=set())
            if n.op == "=" and self.interesting_vars(nname) and not self.isRead(acctable1, nname, posright1):
                # nname will be overwritten without reading its value: consider it as not being read
                acctable.pop(nname, None)
            return {'code': Assignment(n.op, visit_lvalue['code'], visit_rvalue['code']), 'acctable': acctable, 'posright': posright-1}

    def visit_Cast(self, n, read=False, acctable= dict(), posright=0):
        if type(n.to_type.type.type) is IdentifierType and "void" in n.to_type.type.type.names and type(n.expr) is Constant and n.expr.value == "0": # (void) 0 : do not remove it
            return {'code': n, 'acctable': acctable, 'posright': posright-1}
        else:
            visit_expr = self.visit(n.expr, read=read, acctable=acctable, posright=posright)
            return {'code': Cast(n.to_type, visit_expr['code']), 'acctable': acctable, 'posright': visit_expr['posright']-1}

    def visit_ExprList(self, n, read=False, acctable= dict(), posright=0):
        stats = []
        
        for i in range(len(n.exprs)-1,-1,-1):
            acctable_prev = copy.deepcopy(acctable)
            expr_i = self.visit(n.exprs[i], read=(i == len(n.exprs)-1) and read, acctable=acctable, posright=posright) #the only readable value comes from the last statement, and only if read is True
            posright = expr_i['posright']
            if (i != len(n.exprs)-1 or not read) and not self.side_effects.visit(expr_i['code']):
                # don't care about this value and no side effects: drop it
                acctable = acctable_prev
            else:
                # this value is readable or has side effects: keep it
                #stats = [expr_i['code']] + stats
                #read_IDs = expr_i['read_IDs']
                pass
        if len(stats) > 0:
            return {'code': ExprList(stats), 'acctable': acctable, 'posright': posright-1}
        else:
            return {'code': EmptyStatement(), 'acctable': acctable, 'posright': posright-1}

    def visit_EmptyStatement(self, n, read=False, acctable= dict(), posright=0):
        return {'code':n, 'acctable': acctable, 'posright': posright-1}

    def uni_acctables(self, a1, a2):
        out = copy.deepcopy(a1)
        for k in a2:
            if k not in out:
                out[k] = a2[k]
        return out

    def visit_TernaryOp(self, n, read=False, acctable= dict(), posright=0):
        acctable_true = copy.deepcopy(acctable)
        acctable_false = copy.deepcopy(acctable)
        visit_iftrue = self.visit(n.iftrue, read=read, acctable=acctable_true, posright=posright)
        posright = visit_iftrue['posright']
        visit_iffalse = self.visit(n.iffalse, read=read, acctable=acctable_false, posright=posright)
        posright = visit_iffalse['posright']
        acctable_aft = self.uni_acctables(acctable_true, acctable_false)
        visit_cond = self.visit(n.cond, read=True, acctable=acctable_aft, posright=posright)
        posright = visit_cond['posright']
        return {'code': TernaryOp(visit_cond['code'],visit_iftrue['code'],visit_iffalse['code']), 'acctable': acctable_aft, 'posright': posright-1}
        
class HasSideEffects(CGenerator):
    # check if statement has side effects
    
    def __init__(self, keep_void0 = False):
        super().__init__()
        self.parser = CParser()
        self.keep_void0 = keep_void0
        
    def check(self, code):
        with_boilerplate = "void main(){"+code+";}"
        return self.visit(self.parser.parse(with_boilerplate).ext[0].body.block_items[0])
    
    def visit_Constant(self, n):
        return False
        
    def visit_Typename(self, n):
        return False
        
    def visit_ID(self, n):
        return False
        
    def visit_ArrayRef(self, n):
        return self.visit(n.subscript) or self.visit(n.name)
        
    def visit_StructRef(self, n):
        return self.visit(n.field) or self.visit(n.name)

    def visit_FuncCall(self, n):
        if n.name.name in ("__CPROVER_set_field", "__CSEQ_assert", "assert", "__CSEQ_assume", "__CPROVER_assume", "assume"): #Add as needed
            return True
        # assuming no side effects from the function itself at this point (we are using our own made functions)
        if n.args is None:
            return False
        else:
            return any([self.visit(a) for a in n.args])

    def visit_UnaryOp(self, n):
        return n.op in ("p++", "p--", "++", "--") or self.visit(n.expr)

    def visit_BinaryOp(self, n):
        return self.visit(n.right) or self.visit(n.left)

    def visit_Assignment(self, n):
        return True

    def visit_Cast(self, n):
        if type(n.to_type.type.type) is IdentifierType and "void" in n.to_type.type.type.names and n.expr.value == "0": # (void) 0 : do not remove it
            return self.keep_void0
        else:
            return self.visit(n.expr)

    def visit_ExprList(self, n):
        return any([self.visit(e) for e in n.exprs])

    def visit_EmptyStatement(self, n):
        return False

    def visit_TernaryOp(self, n):
        return self.visit(n.iftrue) or self.visit(n.iffalse) or self.visit(n.cond)
