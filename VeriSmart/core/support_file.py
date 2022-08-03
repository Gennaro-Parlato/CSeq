from pycparser.c_generator import CGenerator
from pycparser.c_ast import *
import copy
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
        
        # Set of already printed declarations for the current scope
        self.knownDeclsStack = [set()]
        
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
#include <errno.h>
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
            print_line = 'PRINT_DT(('+n_expr+'),'+str(idx)+', "TYPE");'
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
        lastNode = None
        for ext in n.ext:
            if type(ext) is Decl and type(lastNode) is Decl:
                if ext.name == lastNode.name:
                    if ext.init is None and lastNode.init is not None:
                        pass #skip
                    elif ext.init is not None and lastNode.init is None:
                        mainContent.pop()
                        mainContent += self.visit(ext)
                        lastNode = ext
                    else:
                        mainContent += self.visit(ext)
                        lastNode = ext
                else:
                    mainContent += self.visit(ext)
                    lastNode = ext
            else:
                mainContent += self.visit(ext)
                lastNode = ext
            
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
        if n.name.name in ("__cs_safe_malloc", "__CSEQ_assert", "assert", "__CSEQ_assume"):
            with self.set_can_value(True):
                ans += self.visit(n.args.exprs[0])
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
        with self.set_can_value(self.can_value or n.op in ("--","++","p++","p--",'+','-','~','!','*')):
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
            ans += self.bookNodeType(n.lvalue)
            ans += self.visit(n.lvalue)
            ans += self.visit(n.rvalue)
        return ans
    
    def __getType(self, node_info):
        return str(type(node_info)).split('.')[-1].replace('>', ' ').replace("'", '').replace(' ', '')
    
    def visit_Decl(self, n, no_type=False):
        ans = []
        if type(n.type) is TypeDecl and type(n.type.type) is Struct:
            struct_t_name = "struct "+n.type.type.name
            for decl in self.knownDeclsStack[::-1]:
                if struct_t_name in decl:
                    old_decl = n.type.type.decls
                    n.type.type.decls = None
                    ans += [self.cgenerator.visit(n)+";"]
                    n.type.type.decls = old_decl
                    break
            else:
                self.knownDeclsStack[-1].add(struct_t_name)
                ans += [self.cgenerator.visit(n)+";"]
            if n.init is not None:
                with self.inner_decl():
                    with self.set_can_value(True):
                        ans += self.visit(n.init)
        elif type(n.type) is PtrDecl and type(n.type.type) is TypeDecl and type(n.type.type.type) is Struct:
            struct_t_name = "struct "+n.type.type.type.name
            for decl in self.knownDeclsStack[::-1]:
                if struct_t_name in decl:
                    old_decl = n.type.type.type.decls
                    n.type.type.type.decls = None
                    ans += [self.cgenerator.visit(n)+";"]
                    n.type.type.type.decls = old_decl
                    break
            else:
                self.knownDeclsStack[-1].add(struct_t_name)
                ans += [self.cgenerator.visit(n)+";"]
            if n.init is not None:
                with self.inner_decl():
                    with self.set_can_value(True):
                        ans += self.visit(n.init)
        else:
            if self.global_decl and (type(n.type) is not FuncDecl or n.name != "main"):
                ans += [self.cgenerator.visit(n)+";"]
            if type(n.type) is FuncDecl and n.type.args is not None:
                ans += self.visit(n.type.args)
            if n.init is not None:
                type_of_n = self.__getType(n.type)
                if type_of_n == 'ArrayDecl':
                    for index, ass_exp in enumerate(n.init):
                        ans += self.bookNodeType(ArrayRef(ID(n.name), Constant('int', str(index))))
                elif type_of_n in ('PtrDecl','TypeDecl'):
                    ans += self.bookNodeType(ID(n.name))
                        
                with self.inner_decl():
                    with self.set_can_value(True):
                        ans += self.visit(n.init)
        strans = "\n".join(ans)
        for decl in self.knownDeclsStack[::-1]:
            if strans in decl:
                return []
        self.knownDeclsStack[-1].add(strans)
        return ans
        
    def visit_DeclList(self, n):
        ans = []
        for d in n.decls:
            ans += self.visit(d)
        return ans
        
    def visit_Typedef(self, n):
        return [self.cgenerator.visit(n)+";"]
        
    def visit_Cast(self, n):
        ans = []
        if self.can_value:
            ans += self.bookNodeType(n)
        ans += self.visit(n.expr)
        return ans

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
        if type(n.decl.type.type.type) is IdentifierType and n.decl.type.type.type.names[0] == "void":
            #void function
            ncp = copy.copy(n)
            ncp.body = Compound([])
            ans += [self.cgenerator.visit(ncp)]
            if n.decl.type.args is not None:
                ans += self.visit(n.decl.type.args)
        elif type(n.decl.type.type.type) is IdentifierType and n.decl.type.type.type.names[0] == "int":
            #int function
            ncp = copy.copy(n)
            ncp.body = Compound([Return(Constant("int","0"))])
            ans += [self.cgenerator.visit(ncp)]
            if n.decl.type.args is not None:
                ans += self.visit(n.decl.type.args)
        else:
            ans += self.visit(n.decl)
        if n.param_decls:
            self.visit(n.param_decls)
        ans += self.visit(n.body)
        return ans
        
    def visit_Compound(self, n):
        ans = []
        ans += ["{"]
        self.knownDeclsStack.append(set())
        if n.block_items:
            with self.set_can_value(False):
                for stmt in n.block_items:
                    ans += self.visit(stmt)
        ans += ["}"]
        self.knownDeclsStack.pop()
        return ans

    def visit_CompoundLiteral(self, n):
        return self.visit(n.init)
    
    def visit_EmptyStatement(self, n):
        return []
        
    def __cleanParamDecl(self, n):
        # returns a new declaration where arrays without dimensions are replaced with pointers.
        if type(n.type) is IdentifierType:
            return n
        n_cp = copy.copy(n)
        if type(n.type) is ArrayDecl and n.type.dim is None:
            n_cp.type = self.__cleanParamDecl(PtrDecl([], n.type.type))
        else:
            n_cp.type = self.__cleanParamDecl(n.type)
        return n_cp
    
    def visit_ParamList(self, n):
        ans = []
        for p in n.params:
            ans += self.visit(self.__cleanParamDecl(p))
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
        with self.set_can_value(True):
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
        ans = []
        ans += self.visit(n.expr)
        return ans
