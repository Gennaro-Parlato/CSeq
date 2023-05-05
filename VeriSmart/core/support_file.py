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
        
class StructTypeInfo:
    def __init__(self, n, typenames_enum):
        self.name = n.name
        self.type_idx = len(typenames_enum)
        self.typemap_name = "other_struct_"+self.name+"_"+str(self.type_idx)
        self.type_name = "struct "+self.name
        self.typename_enum = "TYPENAME_"+self.type_name.upper().replace(" ","_")+"_"+str(self.type_idx)
        typenames_enum.append(self.typename_enum)
        self.fields = {f.name: ID(self.typemap_name+"."+f.name) for f in n.decls if not f.name.startswith('__cs_bump_struct_size')}
        
    def compute_struct_field_types(self, bookNodeType):
        ans = []
        for fname, fobj in self.fields.items():
            expr_to_evaluate = "(("+self.type_name+" *)0)->"+fname
            ans += (bookNodeType(fobj, expr_to_evaluate))
        return ans
        
class SupportFileManager(CGenerator):
    def __init__(self):
        super().__init__()
        self.expr_to_label = dict()
        self.label_to_type = dict()
        self.test_struct = dict()
        self.has_side_effects = dict()
        self.if_nesting_level = dict() #function -> deepest if level
        self.current_nesting_level = None
        self.max_nesting_level = None
        self.bap1if_level = dict() #function -> deepest bap1if level
        self.needs_bap1if = dict() #if.iffalse -> needs a bap1if
        self.current_bap1if_level = None
        self.max_bap1if_level = None
        self.do_assume_bap_in_cond = dict() #if -> do an assume !bap in cond, as a branch leads to assume !bap
        self.child_has_side_effect = None
        self.progLbl = 0
        self.typecastLbl = 0
        self.cgenerator = CGenerator()
        # True only when it might me evaluated in VALUE mode.
        self.can_value = False 
        # True only when the declaration is global.
        self.global_decl = True 
        
        self.has_compulsory_assumeBap = list() # True iff a path leads to assume(!bap)
        self.has_assumeBap = list() # True iff a path leads to assume(!bap)
        self.has_assumeBap_idx = -1
        
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
            
        self.struct_types = dict()
        
        self.typenames_enum = "TYPENAME_INT,TYPENAME_CHAR,TYPENAME_LONG_INT,TYPENAME_SHORT,TYPENAME_LONG_LONG,TYPENAME_UNSIGNED_INT,TYPENAME_UNSIGNED_CHAR,TYPENAME_UNSIGNED_LONG_INT,TYPENAME_UNSIGNED_SHORT,TYPENAME_UNSIGNED_LONG_LONG,TYPENAME_OTHER".split(",")
            
        self.base_typename_def = self.get_typename_def()
        self.boilerplate = lambda: """
#include <stdio.h>
#include <errno.h>
#include \""""+os.path.abspath(os.getcwd())+"""/modules/pthread_defs.c\"
#define PRINT_DT(E,ID, EXP) printf("%s_%d, %d\\n",EXP,ID,typename(E) )
#define PRINT_IS(E,ID, EXP) printf("%s_%d, %d\\n",EXP,ID,sizeof(E)>8 )
void __CPROVER_get_field(void *a, char field[100] ){return;}
void __CPROVER_set_field(void *a, char field[100], _Bool c){return;}        
void *__cs_safe_malloc(int __cs_size);
void *__cs_getspecific(int key){return 0;}
typedef struct {int x1;int x2;int x3;int x4;int x5;int x6;int x7;int x8;int x9;} __cs_t;
enum t_typename {"""+",\n".join(self.typenames_enum)+"""};

#ifndef THREADS
#define THREADS 2
#endif        

#ifndef __cs_thread_index
#define __cs_thread_index 0
#endif
                                                                                                                                                                                                                                                                                                            \
""" + self.base_typename_def

    def new_assumeBap_block(self):
        self.has_assumeBap_idx += 1
        if self.has_assumeBap_idx == len(self.has_assumeBap):
            self.has_assumeBap.append(False)
        else:
            self.has_assumeBap[self.has_assumeBap_idx] = False
            
    def release_assumeBap_block(self):
        self.has_assumeBap_idx -= 1
        
    def newrel_assumeBap_block(self, val=False):
        self.new_assumeBap_block()
        if val:
            self.mark_assumeBap_block(val)
        self.release_assumeBap_block()
        
    def mark_assumeBap_block(self, val=True):
        self.has_assumeBap[self.has_assumeBap_idx] = self.has_assumeBap[self.has_assumeBap_idx] or val
        
    def mark_bottom_assumeBap_block(self):
        self.mark_assumeBap_block(self.has_assumeBap[self.has_assumeBap_idx+1])
        
    def get_assumeBap_block(self, delta=0):
        return self.has_assumeBap[self.has_assumeBap_idx + delta]
        
    def get_typename_def(self):
        return """#define typename(x) _Generic((x),                                                                                                                                                                                                                                                                           \
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
        """+"".join([s.type_name+": "+s.typename_enum+", " for s in self.struct_types.values()])+""" \
        default:  TYPENAME_OTHER)"""
        
    def get_struct_field_types(self, typemap_name):
        sti = self.struct_types[typemap_name]
        out = dict()
        for fname, fid in sti.fields.items():
            tp_f = self.get_type(fid)
            isstr_f = self.is_struct(fid)
            if isstr_f:
                out[fname] = self.get_struct_field_types(tp_f)
            else:
                out[fname] = tp_f
        return out
        
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
                self.new_assumeBap_block()
                mainContent += self.visit(ext)
                self.release_assumeBap_block()
                lastNode = ext
        return "\n".join([self.boilerplate(), "int main(){","printf(\"ADDRBITS, %lld\\n\",8*sizeof(int*));"]+mainContent+["return 0;","}"])
    
    def visit_Constant(self, n):
        self.child_has_side_effect = False
        self.newrel_assumeBap_block()
        if self.can_value:
            return self.bookNodeType(n)
        else:
            return []
    
    def visit_ID(self, n):
        self.child_has_side_effect = False
        self.newrel_assumeBap_block()
        if self.can_value:
            return self.bookNodeType(n)
        else:
            return []
        
    def visit_ArrayRef(self, n):
        self.new_assumeBap_block()
        ans = []
        ans += self.bookNodeType(n)
        with self.set_can_value(True):
            ans += self.visit(n.name)
            self.mark_bottom_assumeBap_block()
            left_se = self.child_has_side_effect
            ans += self.visit(n.subscript)
            self.mark_bottom_assumeBap_block()
            self.child_has_side_effect = self.child_has_side_effect or left_se
        return ans
        
    def visit_StructRef(self, n):
        self.new_assumeBap_block()
        ans = []
        ans += self.bookNodeType(n)
        with self.set_can_value(True):
            ans += self.visit(n.name)
            self.mark_bottom_assumeBap_block()
        self.release_assumeBap_block()
        return ans
        
    def visit_FuncCall(self, n):
        self.new_assumeBap_block()
        #assumeBap: it might/might not, let's say we do not restrict this unless specific functions
        if n.name.name in ("__cs_safe_malloc", "__CSEQ_assert", "assert", "__CSEQ_assume", "assume_abort_if_not", "__cs_mutex_lock", "__cs_mutex_unlock", "__cs_attr_init", "__cs_create", "__cs_join", "__cs_mutex_init", "__cs_exit", "exit", "__assert_fail"):
             self.mark_assumeBap_block()
        self.child_has_side_effect = True
        ans = []
        '''if n.name.name in ("__cs_safe_malloc", "__CSEQ_assert", "assert", "__CSEQ_assume", "assume_abort_if_not", "__cs_mutex_lock", "__cs_mutex_unlock", "__cs_attr_init"):
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
        else:'''
        if n.name.name in ("__CSEQ_ROWLINE"):
            return ans
        with self.set_can_value(True):
            ans += self.bookNodeType(n)
            if n.args is not None:
                for a in n.args.exprs:
                    ans += self.visit(a)
                    self.mark_bottom_assumeBap_block()
        '''if self.can_value:
            ans += self.bookNodeType(n)
        # TODO might have to visit n.name for function pointers?
        with self.set_can_value(True):
            ans += self.visit(n.args)'''
        self.release_assumeBap_block()
        return ans
    
    def visit_UnaryOp(self, n):
        self.new_assumeBap_block()
        ans = []
        ans += self.bookNodeType(n)
        with self.set_can_value(self.can_value or n.op in ("--","++","p++","p--",'+','-','~','!','*')):
            ans += self.visit(n.expr)
            self.mark_bottom_assumeBap_block()
            self.child_has_side_effect = self.child_has_side_effect or n.op in ("--","++","p++","p--") #TODO unsure about ("*","&") 
            if n.op in ("++", "p++"):
                ans += self.bookNodeType(BinaryOp("+", n.expr, Constant("int","1")))
            elif n.op in ("--", "p--"):
                ans += self.bookNodeType(BinaryOp("-", n.expr, Constant("int","1")))
        self.release_assumeBap_block()
        return ans
    
    def visit_BinaryOp(self, n):
        self.new_assumeBap_block()
        ans = []
        ans += self.bookNodeType(n)
        ans += self.bookNodeType(n.left)
        ans += self.bookNodeType(n.right)
        with self.set_can_value(True):
            ans += self.visit(n.left)
            self.mark_bottom_assumeBap_block()
            left_se = self.child_has_side_effect
            ans += self.visit(n.right)
            self.mark_bottom_assumeBap_block()
            if n.op in ("&&","||"):
                self.has_side_effects[n.right] = self.child_has_side_effect
            self.child_has_side_effect = self.child_has_side_effect or left_se
        self.release_assumeBap_block()
        return ans
        
    def visit_Assignment(self, n):
        self.new_assumeBap_block()
        ans = []
        if self.can_value:
            ans += self.bookNodeType(n)
        if n.op != "=":
            ans += self.bookNodeType(BinaryOp(n.op.replace("=",""), n.lvalue, n.rvalue))
        with self.set_can_value(True):
            ans += self.bookNodeType(n.lvalue)
            ans += self.bookNodeType(n.rvalue)
            ans += self.visit(n.lvalue)
            self.mark_bottom_assumeBap_block()
            ans += self.visit(n.rvalue)
            self.mark_bottom_assumeBap_block()
            self.child_has_side_effect = True
        self.release_assumeBap_block()
        return ans
    
    def __getType(self, node_info):
        return str(type(node_info)).split('.')[-1].replace('>', ' ').replace("'", '').replace(' ', '')
    
    def visit_Decl(self, n, no_type=False):
        ans = []
        self.new_assumeBap_block()
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
                        self.mark_bottom_assumeBap_block()
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
                        self.mark_bottom_assumeBap_block()
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
                sti_decl = []
                if type(n.type) is Struct:
                    n = copy.deepcopy(n)
                    self.bump_size_struct(n.type)
                    if n.type.decls is not None:
                        sti = StructTypeInfo(n.type, self.typenames_enum)
                        self.struct_types[sti.typemap_name] = sti
                        self.types_map[sti.type_idx] = ("...", sti.typemap_name)
                        sti_decl = [l+";" for l in sti.compute_struct_field_types(lambda x,e: self.bookNodeType(x,e))]+[self.get_typename_def()]
                ans += [self.cgenerator.visit(n)+";"] + sti_decl
            if type(n.type) is FuncDecl and n.type.args is not None:
                oldsdis = self.store_def_in_stack
                self.store_def_in_stack = False
                ans += self.visit(n.type.args)
                self.mark_bottom_assumeBap_block()
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
                        self.mark_bottom_assumeBap_block()
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
        self.release_assumeBap_block()
        return ans_no_dup
        
    def visit_DeclList(self, n):
        self.new_assumeBap_block()
        ans = []
        for d in n.decls:
            ans += self.visit(d)
            self.mark_bottom_assumeBap_block()
        self.release_assumeBap_block()
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
        self.new_assumeBap_block()
        if n.name in self.already_in:
            if not self.already_in[n.name]:
                self.already_in[n.name] = True
                sti_decl=[]
                if type(n.type.type) is Struct: 
                    n = copy.deepcopy(n)
                    self.bump_size_struct(n.type.type)
                    if n.type.type.decls is not None:
                        sti = StructTypeInfo(n.type.type, self.typenames_enum)
                        self.struct_types[sti.typemap_name] = sti
                        self.types_map[sti.type_idx] = ("...", sti.typemap_name)
                        sti_decl = [l+";" for l in sti.compute_struct_field_types(lambda x,e: self.bookNodeType(x,e))]+[self.get_typename_def()]
                self.release_assumeBap_block()
                return [self.cgenerator.visit(n)+";"]+sti_decl
            else:
                self.release_assumeBap_block()
                return []
        else:
            sti_decl=[]
            if type(n.type.type) is Struct: 
                n = copy.deepcopy(n)
                self.bump_size_struct(n.type.type)
                if n.type.type.decls is not None:
                    sti = StructTypeInfo(n.type.type, self.typenames_enum)
                    self.struct_types[sti.typemap_name] = sti
                    self.types_map[sti.type_idx] = ("...", sti.typemap_name)
                    sti_decl = [l+";" for l in sti.compute_struct_field_types(lambda x,e: self.bookNodeType(x,e))]+[self.get_typename_def()]
            self.release_assumeBap_block()
            return [self.cgenerator.visit(n)+";"]+sti_decl
        
    def visit_Cast(self, n):
        self.new_assumeBap_block()
        ans = []
        if self.can_value:
            ans += self.bookNodeType(n)
            ans+=[self.cgenerator.visit(n.to_type)+' __cs_typeofcast_'+str(self.typecastLbl)+';']
            ans += self.bookNodeType(n.to_type, '__cs_typeofcast_'+str(self.typecastLbl))
            self.typecastLbl+=1
            ans += self.visit(n.to_type)
            self.mark_bottom_assumeBap_block()
        with self.set_can_value(True):
            ans += self.visit(n.expr)
            self.mark_bottom_assumeBap_block()
        self.release_assumeBap_block()
        return ans

    def visit_ExprList(self, n):
        self.new_assumeBap_block()
        ans = []
        any_se = False
        with self.set_can_value(False):
            for expr in n.exprs[:-1]:
                ans += self.visit(expr)
                self.mark_bottom_assumeBap_block()
                any_se = any_se or self.child_has_side_effect
        ans += self.visit(n.exprs[-1])
        self.child_has_side_effect = self.child_has_side_effect or any_se
        self.release_assumeBap_block()
        return ans
        
    def visit_InitList(self, n):
        self.mark_bottom_assumeBap_block()
        ans = []
        any_se = False
        with self.set_can_value(True):
            for expr in n.exprs:
                ans += self.visit(expr)
                self.mark_bottom_assumeBap_block()
                any_se = any_se or self.child_has_side_effect
        self.child_has_side_effect = any_se
        self.release_assumeBap_block()
        return ans

    def visit_Enum(self, n):
        self.newrel_assumeBap_block()
        ans = []
        if self.global_decl:
            ans += [self.cgenerator.visit(n)+";"]
        return ans

    def visit_Alignas(self, n):
        self.newrel_assumeBap_block()
        return []

    def visit_Enumerator(self, n):
        self.newrel_assumeBap_block()
        ans = []
        if self.global_decl:
            ans += [self.cgenerator.visit(n)+";"]
        return ans

    def visit_FuncDef(self, n):
        self.new_assumeBap_block()
        ans = []
        if type(n.decl.type.type.type) is IdentifierType and n.decl.type.type.type.names[0] == "void":
            #void function
            #ncp = copy.copy(n)
            #ncp.body = Compound([])
            #ans += [self.cgenerator.visit(ncp)]
            ans += self.visit(n.decl)
            self.mark_bottom_assumeBap_block()
            if n.decl.type.args is not None:
                ans += self.visit(n.decl.type.args)
                self.mark_bottom_assumeBap_block()
        elif type(n.decl.type.type.type) is IdentifierType and n.decl.type.type.type.names[0] == "int":
            #int function
            #ncp = copy.copy(n)
            #ncp.body = Compound([Return(Constant("int","0"))])
            ans += self.visit(n.decl)
            self.mark_bottom_assumeBap_block()
            if n.decl.type.args is not None:
                ans += self.visit(n.decl.type.args)
                self.mark_bottom_assumeBap_block()
        else:
            ans += self.visit(n.decl)
            self.mark_bottom_assumeBap_block()
        if n.param_decls:
            ans += self.visit(n.param_decls)
            self.mark_bottom_assumeBap_block()
        self.current_nesting_level = 0
        self.max_nesting_level = 0
        self.current_bap1if_level = 0
        self.max_bap1if_level = 0
        ans += self.visit(n.body)
        self.mark_bottom_assumeBap_block()
        self.if_nesting_level[n.decl.name] = self.max_nesting_level
        self.bap1if_level[n.decl.name] = self.max_bap1if_level
        self.current_nesting_level = None
        self.max_nesting_level = None
        self.current_bap1if_level = None
        self.max_bap1if_level = None
        self.release_assumeBap_block()
        return ans
        
    def visit_Compound(self, n):
        self.new_assumeBap_block()
        ans = []
        ans += ["{"]
        self.knownDeclsStack.append(set())
        if n.block_items:
            with self.set_can_value(False):
                for stmt in n.block_items:
                    ans += self.visit(stmt)
                    self.mark_bottom_assumeBap_block()
        ans += ["}"]
        self.knownDeclsStack.pop()
        self.release_assumeBap_block()
        return ans

    def visit_CompoundLiteral(self, n):
        self.new_assumeBap_block()
        ans = self.visit(n.init)
        self.mark_bottom_assumeBap_block()
        self.release_assumeBap_block()
        return ans
    
    def visit_EmptyStatement(self, n):
        self.child_has_side_effect = False
        self.newrel_assumeBap_block()
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
        self.new_assumeBap_block()
        ans = []
        for p in n.params:
            ans += self.visit(self.__cleanParamDecl(p))
            self.mark_bottom_assumeBap_block()
        self.release_assumeBap_block()
        return ans
            
    def visit_Return(self, n):
        self.new_assumeBap_block()
        self.mark_assumeBap_block()
        if n.expr: 
            with self.set_can_value(True):
                ans = self.visit(n.expr)
                self.release_assumeBap_block()
                return ans
        else:
            self.release_assumeBap_block()
            return []

    def visit_Break(self, n):
        assert(False)

    def visit_Continue(self, n):
        assert(False)

    def visit_TernaryOp(self, n):
        self.new_assumeBap_block()
        ans = []
        ans += self.visit(n.cond)
        self.mark_bottom_assumeBap_block()
        any_se = self.child_has_side_effect
        ans += self.visit(n.iftrue)
        self.mark_bottom_assumeBap_block()
        self.has_side_effects[n.iftrue] = self.child_has_side_effect
        any_se = self.child_has_side_effect or any_se
        ans += self.visit(n.iffalse)
        self.mark_bottom_assumeBap_block()
        self.has_side_effects[n.iffalse] = self.child_has_side_effect
        self.child_has_side_effect = self.child_has_side_effect or any_se
        self.release_assumeBap_block()
        return ans

    def visit_If(self, n):
        self.new_assumeBap_block()
        ans = []
        self.current_nesting_level += 1
        self.max_nesting_level = max(self.max_nesting_level, self.current_nesting_level)
        with self.set_can_value(True):
            ans += self.visit(n.cond)
            self.mark_bottom_assumeBap_block()
        ans += self.visit(n.iftrue)
        self.mark_bottom_assumeBap_block()
        self.needs_bap1if[n.iffalse] = not self.check_elseif(n.iffalse)
        if self.needs_bap1if[n.iffalse]:
            self.current_bap1if_level += 1
            self.max_bap1if_level = max(self.max_bap1if_level, self.current_bap1if_level)
        ans += self.visit(n.iffalse)
        self.mark_bottom_assumeBap_block()
        if self.needs_bap1if[n.iffalse]:
            self.current_bap1if_level -= 1
        self.do_assume_bap_in_cond[n] = self.get_assumeBap_block()
        self.current_nesting_level -= 1
        self.release_assumeBap_block()
        return ans
        
    def check_elseif(self, cmpnd):
        #returns True <==> cmpnd represents an elseif block: i.e, it is
        #  static bool cond;
        #  cond = ....
        #  if(cond){...} (else {...})?
        if type(cmpnd) is not Compound:
            return False
        decl_cond = None
        has_assn_cond = False
        has_if_cond = False
        for n in cmpnd.block_items:
            if type(n) is EmptyStatement:
                continue
            elif type(n) is Decl:
                #print("CE_D")
                if decl_cond is not None:
                    return False
                ifcond_idx = n.name.rfind("if_cond")
                if ifcond_idx == -1:
                    return False
                if len(n.name) > ifcond_idx + 7 and (n.name[ifcond_idx + 7] != "_" or any(n.name[i] not in "0123456789" for i in range(ifcond_idx + 8, len(n.name)))):
                    return False
                decl_cond = n.name
            elif type(n) is Assignment:
                #print("CE_A")
                if type(n.lvalue) is not ID or n.lvalue.name != decl_cond:
                    return False
                has_assn_cond = True
            elif type(n) is If:
                #print("CE_I")
                if type(n.cond) is not ID or n.cond.name != decl_cond:
                    return False
                else:
                    has_if_cond = True
            else:
                return False
        #print("CE", decl_cond is not None, has_assn_cond, has_if_cond)
        return decl_cond is not None and has_assn_cond and has_if_cond

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
        self.new_assumeBap_block()
        ans = self.visit(n.stmt)
        self.mark_bottom_assumeBap_block()
        self.release_assumeBap_block()
        return ans

    def visit_Goto(self, n):
        self.new_assumeBap_block()
        self.mark_assumeBap_block()
        self.release_assumeBap_block()
        return []

    def visit_EllipsisParam(self, n):
        self.newrel_assumeBap_block()
        return []

    def visit_Struct(self, n):
        self.newrel_assumeBap_block()
        return [self.cgenerator.visit(n)+";"]

    def visit_Typename(self, n):
        self.newrel_assumeBap_block()
        return []

    def visit_Union(self, n):
        self.newrel_assumeBap_block()
        return [self.cgenerator.visit(n)+";"]

    def visit_NamedInitializer(self, n):
        self.new_assumeBap_block()
        ans = []
        ans += self.visit(n.expr)
        self.mark_bottom_assumeBap_block()
        self.release_assumeBap_block()
        return ans
