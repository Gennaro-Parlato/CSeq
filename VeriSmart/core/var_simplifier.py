from pycparser import CParser
from pycparser.c_generator import CGenerator
from pycparser.c_ast import *
import time

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
        self.codes_to_clean[key] = code
        
    def do_clean_codes(self):
        if self.doClean:
            if len(self.typedefList) > 0:
                txt = "\n".join(self.typedefList)
                self.typedefs += txt + "\n"
                self.typedefList = []
            code = "\n".join([k+": "+self.codes_to_clean[k]+";" for k in self.codes_to_clean])
            with_boilerplate = self.typedefs + "void main(){"+code+"}"
            #print(with_boilerplate)
            parsed = self.parser.parse(with_boilerplate)
            if parsed.ext[-1].body.block_items is not None:
                for label_stmt in parsed.ext[-1].body.block_items:
                    self.side_effects = HasSideEffects(keep_void0 = True)
                    clean_ast = self.visit(label_stmt.stmt)['code']
                    self.clean_codes[label_stmt.name] = self.generate.visit(clean_ast).replace("___fakeifvar___ = ","")
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
        return name == "__cs_baL" or name.startswith("__cs_cond_") or name.startswith("__cs_baV")
        
    def visit(self, node, read=False, after=set()):
        method = 'visit_' + node.__class__.__name__
        return getattr(self, method, self.generic_visit)(node, read, after)
    
    def visit_Constant(self, n, read=False, after=set()):
        return {'code':n, 'read_IDs':after}
        
    def visit_Typename(self, n, read=False, after=set()):
        return {'code':n, 'read_IDs':after}
        
    def visit_ID(self, n, read=False, after=set()):
        return {'code':n, 'read_IDs':after|(set([n.name]) if read and self.interesting_vars(n.name) else set())}
        
    def visit_ArrayRef(self, n, read=False, after=set()):
        visit_subscript = self.visit(n.subscript, read=True, after=after)
        visit_name = self.visit(n.name, read=read, after=visit_subscript['read_IDs'])
        read_IDs = visit_subscript['read_IDs'] | visit_name['read_IDs']
        return {'code': ArrayRef(visit_name['code'], visit_subscript['code']), 'read_IDs': read_IDs}
        
    def visit_StructRef(self, n, read=False, after=set()):
        visit_field = self.visit(n.field, read=read, after=after)
        visit_name = self.visit(n.name, read=True, after=visit_field['read_IDs'])
        read_IDs = visit_name['read_IDs'] | visit_field['read_IDs']
        return {'code': StructRef(visit_name['code'], n.type, visit_field['code']), 'read_IDs': read_IDs}
        
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

    def visit_FuncCall(self, n, read=False, after=set()):
        if n.args is None:
            return {'code':n, 'read_IDs':after}
        elif self.__check_encode_decode(n):
            return self.visit(n.args.exprs[0].args.exprs[0], read=read, after=after)
        elif self.__check_boundsfailure_decode(n):
            return self.visit(ExprList([n.args.exprs[0].args.exprs[0], Constant("int","0")]), read=read, after=after)
        else:
            visit_args = [self.visit(a, read=True, after=after) for a in n.args]
            read_IDs = set()
            for va in visit_args:
                read_IDs = read_IDs | va['read_IDs']
            visit_name = self.visit(n.name, read=True, after=read_IDs)
            read_IDs = read_IDs | visit_name['read_IDs']
            return {'code': FuncCall(visit_name['code'], ExprList([va['code'] for va in visit_args])), 'read_IDs': read_IDs}

    def visit_UnaryOp(self, n, read=False, after=set()):
        visit_expr = self.visit(n.expr, read=True, after = after)
        return {'code': UnaryOp(n.op, visit_expr['code']), 'read_IDs': visit_expr['read_IDs']}

    def visit_BinaryOp(self, n, read=False, after=set()):
        visit_right = self.visit(n.right, read=True, after= after)
        visit_left = self.visit(n.left, read=True, after = visit_right['read_IDs'])
        read_IDs = visit_left['read_IDs'] | visit_right['read_IDs']
        return {'code': BinaryOp(n.op, visit_left['code'], visit_right['code']), 'read_IDs': read_IDs}
        
    def visitForName(self, n):
        if type(n) is ID:
            return n.name
        elif type(n) is UnaryOp:
            return None # never an interesting variable
        else:
            return self.visitForName(n.name)

    def visit_Assignment(self, n, read=False, after=set()):
        nname = self.visitForName(n.lvalue)
        visit_rvalue = self.visit(n.rvalue, read=not(self.interesting_vars(nname) and nname not in after), after=after)
        visit_rvalue_without_after = self.visit(n.rvalue, read=not(self.interesting_vars(nname) and nname not in after), after=set())
        visit_lvalue = self.visit(n.lvalue, read=(n.op != "="), after=visit_rvalue['read_IDs'])
        read_IDs = visit_lvalue['read_IDs']
        if self.interesting_vars(nname) and nname not in read_IDs:
            # n.lvalue will never be read afterwards: don't do the assignment
            if not read and not self.side_effects.visit(n.rvalue):
                # the rvalue is not read and it does not have side effects (e.g. constant or read from sm): don't even write the rvalue!
                read_IDs_out = after
                if n.op == "=": 
                    # nname is overwritten without reading it. This value is discarded for the newly assigned one
                    read_IDs_out = read_IDs_out.difference(set([nname]))
                return {'code': EmptyStatement(), 'read_IDs': after}
            else:
                return {'code': visit_rvalue['code'], 'read_IDs': visit_rvalue['read_IDs']}
        else:
            if n.op == "=" and self.interesting_vars(nname) and nname not in visit_rvalue_without_after['read_IDs']:
                # nname will be overwritten without reading its value: consider it as not being read
                read_IDs = read_IDs.difference(set([nname]))
            return {'code': Assignment(n.op, visit_lvalue['code'], visit_rvalue['code']), 'read_IDs': read_IDs}

    def visit_Cast(self, n, read=False, after=set()):
        if type(n.to_type.type.type) is IdentifierType and "void" in n.to_type.type.type.names and n.expr.value == "0": # (void) 0 : do not remove it
            return {'code': n, 'read_IDs': after}
        else:
            visit_expr = self.visit(n.expr, read=read, after = after)
            return {'code': Cast(n.to_type, visit_expr['code']), 'read_IDs': visit_expr['read_IDs']}

    def visit_ExprList(self, n, read=False, after=set()):
        stats = []
        
        read_IDs = after
        for i in range(len(n.exprs)-1,-1,-1):
            expr_i = self.visit(n.exprs[i], read=(i == len(n.exprs)-1) and read, after=read_IDs) #the only readable value comes from the last statement, and only if read is True
            if (i != len(n.exprs)-1 or not read) and not self.side_effects.visit(expr_i['code']):
                # don't care about this value and no side effects: drop it
                pass
            else:
                # this value is readable or has side effects: keep it
                stats = [expr_i['code']] + stats
                read_IDs = expr_i['read_IDs']
        if len(stats) > 0:
            return {'code': ExprList(stats), 'read_IDs': read_IDs}
        else:
            return {'code': EmptyStatement(), 'read_IDs': after}

    def visit_EmptyStatement(self, n, read=False, after=set()):
        return {'code':n, 'read_IDs':after}

    def visit_TernaryOp(self, n, read=False, after=set()):
        visit_iftrue = self.visit(n.iftrue, read=read, after=after)
        visit_iffalse = self.visit(n.iffalse, read=read, after=after)
        visit_cond = self.visit(n.cond, read=True, after=visit_iftrue['read_IDs']|visit_iffalse['read_IDs'])
        return {'code': TernaryOp(visit_cond['code'],visit_iftrue['code'],visit_iffalse['code']), 'read_IDs': visit_cond['read_IDs']}
        
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
        if n.name.name in ("__CPROVER_set_field", "__CSEQ_assert", "assert", "__CSEQ_assume", "assume"): #Add as needed
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
