from pycparser.c_generator import CGenerator
from pycparser.c_ast import BinaryOp
import os
import subprocess
import shlex

class BakAndRestore:
    def __init__(self, obj, field, tmpval):
        self.obj = obj
        self.field = field
        self.tmpval = tmpval
    def __enter__(self):
        self.bak = getattr(self.obj, self.field)
        setattr(self.obj, self.field, self.tmpval)
    def __exit__(self, exc_type, exc_value, exc_traceback):
        setattr(self.obj, self.field, self.bak)
        
class SupportFileManager(CGenerator):
    def __init__(self):
        super().__init__()
        self.expr_to_label = dict()
        self.label_to_type = dict()
        self.progLbl = 0
        self.cgenerator = CGenerator()
        # True only when it might me evaluated in VALUE mode.
        self.can_value = False 
        # True only when the declaration is global.
        self.global_decl = True 
        
        self.types_map = {
            6: ('unsigned', 'unsigned char'),
            1: ('signed', 'char'),
            3: ('signed', 'short'),
            8: ('unsigned', 'unsigned short'),
            0: ('signed', 'int'),
            5: ('unsigned', 'unsigned int'),
            2: ('signed', 'long int'),
            7: ('unsigned', 'unsigned long int'),
            4: ('signed', 'long long'),
            9: ('unsigned', 'unsigned long long'),
            10: ('...', 'other')}
            
        self.boilerplate = """
#include <stdio.h>
#include \""""+os.path.abspath(os.getcwd())+"""/modules/pthread_defs.c\"
#define PRINT_DT(E,ID, EXP) printf("%s_%d, %d\\n",EXP,ID,typename(E) )
void __CPROVER_get_field(void *a, char field[100] ){return;}
void __CPROVER_set_field(void *a, char field[100], _Bool c){return;}        
void *__cs_safe_malloc(int __cs_size);
enum t_typename {
       TYPENAME_INT,
       TYPENAME_CHAR,
       TYPENAME_LONG_INT,
       TYPENAME_SHORT,
       TYPENAME_LONG_LONG,
       TYPENAME_UNSIGNED_INT,
       TYPENAME_UNSIGNED_CHAR,
       TYPENAME_UNSIGNED_LONG_INT,
       TYPENAME_UNSIGNED_SHORT,
       TYPENAME_UNSIGNED_LONG_LONG,
       TYPENAME_OTHER
};
        
                                                                                                                                                                                                                                                                                                            \
#define typename(x) _Generic((x),                                                                                                                                                                                                                                                                           \
        char: TYPENAME_CHAR,                                                                                                                                                                                                                                                                                \
        unsigned char: TYPENAME_UNSIGNED_CHAR,                                                                                                                                                                                                                                                              \
        short: TYPENAME_SHORT,                                                                                                                                                                                                                                                                              \
        unsigned short: TYPENAME_UNSIGNED_SHORT,                                                                                                                                                                                                                                                            \
        int: TYPENAME_INT,                                                                                                                                                                                                                                                                                  \
        unsigned int: TYPENAME_UNSIGNED_INT,                                                                                                                                                                                                                                                                \
        long int: TYPENAME_LONG_INT,                                                                                                                                                                                                                                                                        \
        unsigned long int: TYPENAME_UNSIGNED_LONG_INT,                                                                                                                                                                                                                                                      \
        long long : TYPENAME_LONG_LONG,                                                                                                                                                                                                                                                                     \
        unsigned long long:  TYPENAME_UNSIGNED_LONG_LONG,                                                                                                                                                                                                                                                   \
        default:  TYPENAME_OTHER)
        """
        
    def set_can_value(self, x):
        return BakAndRestore(self, 'can_value', x)
        
    def inner_decl(self):
        return BakAndRestore(self, 'global_decl', False)
        
    def bookNodeType(self, n):
        n_expr = self.cgenerator.visit(n)
        if n_expr not in self.expr_to_label:
            idx = self.progLbl
            self.progLbl += 1
            label = "TYPE_"+str(idx)
            self.expr_to_label[n_expr] = label
            print_line = 'PRINT_DT('+n_expr+','+str(idx)+', "TYPE");'
            return [print_line]
        else:
            return []
            
    def compile(self, ast, support_fname, runnable_fname):
        code = self.visit(ast)
        with open(support_fname, "w") as f:
            f.write(code)
        compile_command = "gcc --std=c11 %s -o %s" % (support_fname, runnable_fname)
        process = subprocess.Popen(shlex.split(compile_command), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        compile_out = process.communicate()[0].decode('utf-8').split('\n')
        if process.wait() != 0:
            print("Problems while compiling support file")
            print(compile_out)
            assert(False)
        
        run_command = "./"+runnable_fname
        process = subprocess.Popen(shlex.split(run_command), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        result = process.communicate()[0].decode('utf-8').split('\n')
        process.wait()
        if process.wait() != 0:
            print("Problems while running support file")
            print(result)
            assert(False)
        
        for line in result:
            lineparts = line.strip().split(",")
            if len(lineparts) > 1:
                self.label_to_type[lineparts[0]] = self.types_map[int(lineparts[1].strip())]
    
    def get_type(self, n):
        n_expr = self.cgenerator.visit(n)
        assert(n_expr in self.expr_to_label, "Expression '"+n_expr+"' was not considered for evaluation by support file")
        label = self.expr_to_label[n_expr]
        assert(label in self.label_to_type, "Expression '"+n_expr+"' was considered for evaluation by support file, but didn't produce a type evaluation")
        return self.label_to_type[label][1]
            
    def visit_FileAST(self, n):
        mainContent = []
        for ext in n.ext:
            mainContent += self.visit(ext)
        return "\n".join([self.boilerplate, "int main(){"]+mainContent+["return 0;","}"])
    
    def visit_Constant(self, n):
        if self.can_value:
            return self.bookNodeType(n)
        else:
            return []
    
    def visit_ID(self, n):
        if self.can_value:
            return self.bookNodeType(n)
        else:
            return []
        
    def visit_ArrayRef(self, n):
        ans = []
        if self.can_value:
            ans += self.bookNodeType(n)
        with self.set_can_value(True):
            ans += self.visit(n.name)
            ans += self.visit(n.subscript)
        return ans
        
    def visit_StructRef(self, n):
        ans = []
        if self.can_value:
            ans += self.bookNodeType(n)
        with self.set_can_value(n.type == "->"):
            ans += self.visit(n.name)
        return ans
        
    def visit_FuncCall(self, n):
        ans = []
        '''if self.can_value:
            ans += self.bookNodeType(n)
        # TODO might have to visit n.name for function pointers?
        with self.set_can_value(True):
            ans += self.visit(n.args)'''
        return ans
    
    def visit_UnaryOp(self, n):
        ans = []
        if self.can_value:
            ans += self.bookNodeType(n)
        with self.set_can_value(self.can_value or n.op in ("--","++","p++","p--",'+','-','~')):
            ans += self.visit(n.expr)
        return ans
    
    def visit_BinaryOp(self, n):
        ans = []
        with self.set_can_value(True):
            ans += self.bookNodeType(n)
            ans += self.visit(n.left)
            ans += self.visit(n.right)
        return ans
        
    def visit_Assignment(self, n):
        ans = []
        if self.can_value:
            ans += self.bookNodeType(n)
        with self.set_can_value(True):
            if n.op == "=":
                ans += self.bookNodeType(n.rvalue)
            else:
                ans += self.bookNodeType(BinaryOp(n.op.replace("=",""), n.lvalue, n.rvalue))
            ans += self.visit(n.lvalue)
            ans += self.visit(n.rvalue)
        return ans
    
    def visit_Decl(self, n, no_type=False):
        ans = []
        if self.global_decl:
            ans += [self.cgenerator.visit(n)+";"]
        if n.init is not None:
            with self.inner_decl():
                with self.set_can_value(True):
                    ans += self.visit(n.init)
        return ans
        
    def visit_DeclList(self, n):
        ans = []
        for d in n.decls:
            ans += self.visit(d)
        return ans
        
    def visit_Typedef(self, n):
        return [self.cgenerator.visit(n)+";"]
        
    def visit_Cast(self, n):
        return self.visit(n.expr)

    def visit_ExprList(self, n):
        ans = []
        with self.set_can_value(False):
            for expr in n.exprs[:-1]:
                ans += self.visit(expr)
        ans += self.visit(n.exprs[-1])
        return ans
        
    def visit_InitList(self, n):
        ans = []
        with self.set_can_value(True):
            for expr in n.exprs:
                ans += self.visit(expr)
        return ans

    def visit_Enum(self, n):
        ans = []
        if self.global_decl:
            ans += [self.cgenerator.visit(n)+";"]
        return ans

    def visit_Alignas(self, n):
        return []

    def visit_Enumerator(self, n):
        ans = []
        if self.global_decl:
            ans += [self.cgenerator.visit(n)+";"]
        return ans

    def visit_FuncDef(self, n):
        ans = []
        ans += self.visit(n.decl)
        if n.param_decls:
            for p in n.param_decls:
                ans += self.visit(p)
        ans += self.visit(n.body)
        return ans
        
    def visit_Compound(self, n):
        ans = []
        ans += ["{"]
        if n.block_items:
            with self.set_can_value(False):
                for stmt in n.block_items:
                    ans += self.visit(stmt)
        ans += ["}"]
        return ans

    def visit_CompoundLiteral(self, n):
        return self.visit(n.init)
    
    def visit_EmptyStatement(self, n):
        return []
    
    def visit_ParamList(self, n):
        ans = []
        for p in n.param_decls:
            ans += self.visit(p)
        return ans
            
    def visit_Return(self, n):
        if n.expr: 
            with self.set_can_value(True):
                return self.visit(n.expr)
        else:
            return []

    def visit_Break(self, n):
        assert(False)

    def visit_Continue(self, n):
        assert(False)

    def visit_TernaryOp(self, n):
        ans = []
        ans += self.visit(n.cond)
        ans += self.visit(n.iftrue)
        ans += self.visit(n.iffalse)
        return ans

    def visit_If(self, n):
        ans = []
        ans += self.bookNodeType(n.iftrue)
        ans += self.visit(n.cond)
        ans += self.visit(n.iftrue)
        ans += self.visit(n.iffalse)
        return ans

    def visit_For(self, n):
        assert(False)

    def visit_While(self, n):
        assert(False)

    def visit_DoWhile(self, n):
        assert(False)

    def visit_StaticAssert(self, n):
        assert(False)

    def visit_Switch(self, n):
        assert(False)

    def visit_Case(self, n):
        assert(False)

    def visit_Default(self, n):
        assert(False)

    def visit_Label(self, n):
        return self.visit(n.stmt)

    def visit_Goto(self, n):
        return []

    def visit_EllipsisParam(self, n):
        return []

    def visit_Struct(self, n):
        return [self.cgenerator.visit(n)+";"]

    def visit_Typename(self, n):
        return []

    def visit_Union(self, n):
        return [self.cgenerator.visit(n)+";"]

    def visit_NamedInitializer(self, n):
        assert(False)
