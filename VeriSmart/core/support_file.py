from pycparser.c_generator import CGenerator
from pycparser.c_ast import *
import copy
import os
import subprocess
import shlex
import sys

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
        self.test_struct = dict()
        self.has_side_effects = dict()
        self.child_has_side_effect = None
        self.progLbl = 0
        self.typecastLbl = 0
        self.cgenerator = CGenerator()
        # True only when it might me evaluated in VALUE mode.
        self.can_value = False 
        # True only when the declaration is global.
        self.global_decl = True 
        
        # GG: ensure that those typedef appear only once
        self.already_in = {'pthread_t':False, 'pthread_attr_t':False, 'size_t':False, '__cs_t':True}
        
        # Set of already printed declarations for the current scope
        self.knownDeclsStack = [set()]
        
        self.store_def_in_stack = True
        
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
#define PRINT_IS(E,ID, EXP) printf("%s_%d, %d\\n",EXP,ID,sizeof(E)>8 )
void __CPROVER_get_field(void *a, char field[100] ){return;}
void __CPROVER_set_field(void *a, char field[100], _Bool c){return;}        
void *__cs_safe_malloc(int __cs_size);
typedef struct {int x1;int x2;int x3;int x4;int x5;int x6;int x7;int x8;int x9;} __cs_t;
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

#ifndef THREADS
#define THREADS 2
#endif        

#ifndef __cs_thread_index
#define __cs_thread_index 0
#endif
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
        
    def bookNodeType(self, n, expr_to_evaluate=None):
        n_expr = self.cgenerator.visit(n)
        if expr_to_evaluate is None:
            expr_to_evaluate = n_expr
        if n_expr not in self.expr_to_label:
            idx = self.progLbl
            self.progLbl += 1
            label = "TYPE_"+str(idx)
            self.expr_to_label[n_expr] = label
            print_line = 'PRINT_DT(('+expr_to_evaluate+'),'+str(idx)+', "TYPE");'
            print_line += '\nPRINT_IS(('+expr_to_evaluate+'),'+str(idx)+', "STRC");'
            return [print_line]
        else:
            return []
            
    def compile(self, ast, support_fname, runnable_fname):
        code = self.visit(ast)
        with open(support_fname, "w") as f:
            f.write(code)
        compiler = "gcc"
        if sys.platform.startswith('darwin'):
            compiler = "gcc-11"
        compile_command = "%s --std=c11 %s -o %s" % (compiler, support_fname, runnable_fname)
        process = subprocess.Popen(shlex.split(compile_command), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        compile_out = process.communicate()[0].decode('utf-8').split('\n')
        if process.wait() != 0:
            print("Problems while compiling support file")
            print("\n".join([str(x) for x in compile_out]))
            assert(False)
        
        run_command = "./"+runnable_fname
        process = subprocess.Popen(shlex.split(run_command), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        result = process.communicate()[0].decode('utf-8').split('\n')
        process.wait()
        if process.wait() != 0:
            print("Problems while running support file")
            print("\n".join([str(x) for x in result]))
            assert(False)
        
        for line in result:
            lineparts = line.strip().split(",")
            if len(lineparts) > 1:
                if lineparts[0] == "ADDRBITS":
                    self.addr_bits = int(lineparts[1].strip())
                elif lineparts[0].startswith("STRC"):
                    self.test_struct[lineparts[0]] = int(lineparts[1].strip()) != 0
                else:
                    self.label_to_type[lineparts[0]] = self.types_map[int(lineparts[1].strip())]
    
    def is_struct(self, n):
        n_expr = self.cgenerator.visit(n)
        assert(n_expr in self.expr_to_label, "Expression '"+n_expr+"' was not considered for evaluation by support file")
        label = self.expr_to_label[n_expr]
        assert(("STRC"+label[4:]) in self.test_struct, "Expression '"+n_expr+"' was considered for evaluation by support file, but didn't produce a type evaluation")
        return self.test_struct["STRC"+label[4:]]

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
        return "\n".join([self.boilerplate, "int main(){","printf(\"ADDRBITS, %lld\\n\",8*sizeof(int*));"]+mainContent+["return 0;","}"])
    
    def visit_Constant(self, n):
        self.child_has_side_effect = False
        if self.can_value:
            return self.bookNodeType(n)
        else:
            return []
    
    def visit_ID(self, n):
        self.child_has_side_effect = False
        if self.can_value:
            return self.bookNodeType(n)
        else:
            return []
        
    def visit_ArrayRef(self, n):
        ans = []
        ans += self.bookNodeType(n)
        with self.set_can_value(True):
            ans += self.visit(n.name)
            left_se = self.child_has_side_effect
            ans += self.visit(n.subscript)
            self.child_has_side_effect = self.child_has_side_effect or left_se
        return ans
        
    def visit_StructRef(self, n):
        ans = []
        ans += self.bookNodeType(n)
        with self.set_can_value(True):
            ans += self.visit(n.name)
        return ans
        
    def visit_FuncCall(self, n):
        self.child_has_side_effect = True
        ans = []
        if n.name.name in ("__cs_safe_malloc", "__CSEQ_assert", "assert", "__CSEQ_assume", "assume_abort_if_not", "__cs_mutex_lock", "__cs_mutex_unlock"):
            with self.set_can_value(True):
                ans += self.visit(n.args.exprs[0])
        elif n.name.name in ("__cs_create",):
            with self.set_can_value(True):
                ans += self.visit(n.args.exprs[0])
                ans += self.visit(n.args.exprs[3])
        elif n.name.name in ("__cs_join", "__cs_mutex_init"):
            with self.set_can_value(True):
                ans += self.visit(n.args.exprs[0])
                ans += self.visit(n.args.exprs[1])
        '''if self.can_value:
            ans += self.bookNodeType(n)
        # TODO might have to visit n.name for function pointers?
        with self.set_can_value(True):
            ans += self.visit(n.args)'''
        return ans
    
    def visit_UnaryOp(self, n):
        ans = []
        ans += self.bookNodeType(n)
        with self.set_can_value(self.can_value or n.op in ("--","++","p++","p--",'+','-','~','!','*')):
            ans += self.visit(n.expr)
            self.child_has_side_effect = self.child_has_side_effect or n.op in ("--","++","p++","p--") #TODO unsure about ("*","&") 
            if n.op in ("++", "p++"):
                ans += self.bookNodeType(BinaryOp("+", n.expr, Constant("int","1")))
            elif n.op in ("--", "p--"):
                ans += self.bookNodeType(BinaryOp("-", n.expr, Constant("int","1")))
        return ans
    
    def visit_BinaryOp(self, n):
        ans = []
        ans += self.bookNodeType(n)
        ans += self.bookNodeType(n.left)
        ans += self.bookNodeType(n.right)
        with self.set_can_value(True):
            ans += self.visit(n.left)
            left_se = self.child_has_side_effect
            ans += self.visit(n.right)
            if n.op in ("&&","||"):
                self.has_side_effects[n.right] = self.child_has_side_effect
            self.child_has_side_effect = self.child_has_side_effect or left_se
        return ans
        
    def visit_Assignment(self, n):
        ans = []
        if self.can_value:
            ans += self.bookNodeType(n)
        if n.op != "=":
            ans += self.bookNodeType(BinaryOp(n.op.replace("=",""), n.lvalue, n.rvalue))
        with self.set_can_value(True):
            ans += self.bookNodeType(n.lvalue)
            ans += self.bookNodeType(n.rvalue)
            ans += self.visit(n.lvalue)
            ans += self.visit(n.rvalue)
            self.child_has_side_effect = True
        return ans
    
    def __getType(self, node_info):
        return str(type(node_info)).split('.')[-1].replace('>', ' ').replace("'", '').replace(' ', '')
    
    def visit_Decl(self, n, no_type=False):
        ans = []
        if type(n.type) is TypeDecl and type(n.type.type) is Struct:
            struct_t_name = "struct "+n.type.type.name
            if hasattr(n, 'quals') and len(getattr(n, 'quals')) >= 1 and getattr(n, 'quals')[0] == 'const':
                ans += self.bookNodeType(n.name)
            for decl in self.knownDeclsStack[::-1]:
                if struct_t_name in decl:
                    old_decl = n.type.type.decls
                    n.type.type.decls = None
                    ans += [self.cgenerator.visit(n)+";"]
                    n.type.type.decls = old_decl
                    break
            else:
                if self.store_def_in_stack:
                    self.knownDeclsStack[-1].add(struct_t_name)
                ans += [self.cgenerator.visit(n)+";"]
            if n.init is not None:
                with self.inner_decl():
                    with self.set_can_value(True):
                        oldsdis = self.store_def_in_stack
                        self.store_def_in_stack = False
                        ans += self.visit(n.init)
                        self.store_def_in_stack = oldsdis
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
                if self.store_def_in_stack:
                    self.knownDeclsStack[-1].add(struct_t_name)
                ans += [self.cgenerator.visit(n)+";"]
            if n.init is not None:
                with self.inner_decl():
                    with self.set_can_value(True):
                        oldsdis = self.store_def_in_stack
                        self.store_def_in_stack = False
                        ans += self.visit(n.init)
                        self.store_def_in_stack = oldsdis
        else:
            if self.global_decl and (type(n.type) is FuncDecl and n.name != "main"):
                ncp = copy.deepcopy(n)
                if ncp.type.args is not None:
                    for i in range(len(ncp.type.args.params)):
                        if type(ncp.type.args.params[i]) is Typename:
                            tdf = ncp.type.args.params[i]
                            if not(type(tdf.type) is TypeDecl and type(tdf.type.type) is IdentifierType and tdf.type.type.names == ["void"]):
                                ncp.type.args.params[i] = Decl(None, tdf.quals, [], [], tdf.type, None, None)
                                type_ptr = ncp.type.args.params[i].type #that might be a pointer: recur until you find a typedecl, for which you can assign the name; IdentifierType block the chain (it should only appear with void, or inside a typedecl)
                                while type(type_ptr) not in (TypeDecl, IdentifierType) :
                                    type_ptr = type_ptr.type
                                if type(type_ptr) is TypeDecl:
                                    type_ptr.declname = "p"+str(i)
                        else:
                            type_ptr = ncp.type.args.params[i].type #that might be a pointer: recur until you find a typedecl, for which you can assign the name; IdentifierType block the chain (it should only appear with void, or inside a typedecl)
                            while type(type_ptr) not in (TypeDecl, IdentifierType) :
                                type_ptr = type_ptr.type
                            if type(type_ptr) is TypeDecl:
                                type_ptr.declname = "p"+str(i)
                        #else:
                        #    ncp.type.args.params[i].name = "p"+str(i)
                fbody = "{}"
                if type(n.type.type.type) is IdentifierType and n.type.type.type.names[0] == "int": # int fnc
                    fbody = "{return 01;}"
                visitNcp = self.cgenerator.visit(ncp)
                if visitNcp.endswith("(void)"):
                    visitNcp = visitNcp[:-6]+"()"
                ans += [visitNcp+fbody]
            elif self.global_decl and (type(n.type) is not FuncDecl or n.name != "main"):
                if type(n.type) is Struct:
                    n = copy.deepcopy(n)
                    self.bump_size_struct(n.type)
                ans += [self.cgenerator.visit(n)+";"]
            if type(n.type) is FuncDecl and n.type.args is not None:
                oldsdis = self.store_def_in_stack
                self.store_def_in_stack = False
                ans += self.visit(n.type.args)
                self.store_def_in_stack = oldsdis
            if n.init is not None:
                type_of_n = self.__getType(n.type)
                if type_of_n == 'ArrayDecl':
                    for index, ass_exp in enumerate(n.init):
                        ans += self.bookNodeType(ArrayRef(ID(n.name), Constant('int', str(index))))
                elif type_of_n in ('PtrDecl','TypeDecl'):
                    ans += self.bookNodeType(ID(n.name))
                        
                with self.inner_decl():
                    with self.set_can_value(True):
                        oldsdis = self.store_def_in_stack
                        self.store_def_in_stack = False
                        ans += self.visit(n.init)
                        self.store_def_in_stack = oldsdis
        #strans = "\n".join(ans)
        ans_no_dup = []
        for strans in ans:
            for decl in self.knownDeclsStack[::-1]:
                if strans in decl:
                    break
            else:
                ans_no_dup.append(strans)
                if self.store_def_in_stack:
                    self.knownDeclsStack[-1].add(strans)
        return ans_no_dup
        
    def visit_DeclList(self, n):
        ans = []
        for d in n.decls:
            ans += self.visit(d)
        return ans

    def bump_size_struct(self, n):
        # add fake fields so as its size is bigger than 8 (pointer size)
        if n.decls is None:
            return
        for i in range(9):
            n.decls.append(Decl(name='__cs_bump_struct_size'+str(i),
                                              quals=[],
                                              storage=[],
                                              funcspec=[],
                                              type=TypeDecl(declname='__cs_bump_struct_size'+str(i),
                                                            quals=[],
                                                            type=IdentifierType(names=['int'])),
                                              init=None,
                                              bitsize=None
                                              ))
        
    def visit_Typedef(self, n):
        if n.name in self.already_in:
            if not self.already_in[n.name]:
                self.already_in[n.name] = True
                if type(n.type.type) is Struct: 
                    n = copy.deepcopy(n)
                    self.bump_size_struct(n.type.type)
                return [self.cgenerator.visit(n)+";"]
            else:
                return []
        else:
            if type(n.type.type) is Struct: 
                n = copy.deepcopy(n)
                self.bump_size_struct(n.type.type)
            return [self.cgenerator.visit(n)+";"]
        
    def visit_Cast(self, n):
        ans = []
        if self.can_value:
            ans += self.bookNodeType(n)
            ans+=[self.cgenerator.visit(n.to_type)+' __cs_typeofcast_'+str(self.typecastLbl)+';']
            ans += self.bookNodeType(n.to_type, '__cs_typeofcast_'+str(self.typecastLbl))
            self.typecastLbl+=1
            ans += self.visit(n.to_type)
        ans += self.visit(n.expr)
        return ans

    def visit_ExprList(self, n):
        ans = []
        any_se = False
        with self.set_can_value(False):
            for expr in n.exprs[:-1]:
                ans += self.visit(expr)
                any_se = any_se or self.child_has_side_effect
        ans += self.visit(n.exprs[-1])
        self.child_has_side_effect = self.child_has_side_effect or any_se
        return ans
        
    def visit_InitList(self, n):
        ans = []
        any_se = False
        with self.set_can_value(True):
            for expr in n.exprs:
                ans += self.visit(expr)
                any_se = any_se or self.child_has_side_effect
        self.child_has_side_effect = any_se
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
            #ncp = copy.copy(n)
            #ncp.body = Compound([])
            #ans += [self.cgenerator.visit(ncp)]
            ans += self.visit(n.decl)
            if n.decl.type.args is not None:
                ans += self.visit(n.decl.type.args)
        elif type(n.decl.type.type.type) is IdentifierType and n.decl.type.type.type.names[0] == "int":
            #int function
            #ncp = copy.copy(n)
            #ncp.body = Compound([Return(Constant("int","0"))])
            ans += self.visit(n.decl)
            if n.decl.type.args is not None:
                ans += self.visit(n.decl.type.args)
        else:
            ans += self.visit(n.decl)
        if n.param_decls:
            ans += self.visit(n.param_decls)
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
        self.child_has_side_effect = False
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
        any_se = self.child_has_side_effect
        ans += self.visit(n.iftrue)
        self.has_side_effects[n.iftrue] = self.child_has_side_effect
        any_se = self.child_has_side_effect or any_se
        ans += self.visit(n.iffalse)
        self.has_side_effects[n.iffalse] = self.child_has_side_effect
        self.child_has_side_effect = self.child_has_side_effect or any_se
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
