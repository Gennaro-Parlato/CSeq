from modules import lazyseqnewschedule
from pycparser import c_ast
from pycparser.c_generator import CGenerator
from core import abs_dr_rules
import os

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
        
def getType(node_info):
    return str(type(node_info)).split('.')[-1].replace('>', ' ').replace("'", '').replace(' ', '')

class abstr_dr_common(lazyseqnewschedule.lazyseqnewschedule):
        
    def init(self, abs_on, dr_on):
        super().init()
        #Instrument this node and its children
        self.abs_instrument = True 
        
        self.abs_on = True
        self.dr_on = False
        
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
        
        # Macro file name. TODO make it parametric (see abstraction_prep.loadfromstring)
        self.macro_file_name = "macro_plain.h"
        
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
        
    def loadfromstring(self, string, env):
        self.env = env  
        self.abs_bitwidth = env.bit_width
        self.abs_dr_rules = abs_dr_rules.AbsDrRules(self, self.abs_on, self.dr_on, self.abs_bitwidth)
        
        # Instrumentation arguments: {'abs_mode':abs_mode, 'dr_mode':dr_mode} or {'abs_mode':'GET_VAL', 'dr_mode':'NO_ACCESS'} when translating a statement
        self.abs_dr_mode = {'abs_mode':'GET_VAL' if self.abs_on else None, 'dr_mode':'NO_ACCESS' if self.dr_on else None}
        self.abs_dr_state = abs_dr_rules.State()
        super().loadfromstring(string, env)
        
        abs_mfn = os.path.abspath(self.macro_file_name) #TODO
        self.setOutputParam('header_abstraction','#include "%s"\n' % abs_mfn)
        with open(abs_mfn, "w") as f:
            f.write(self.abs_dr_rules.macro_file_content())
    
    # allows to create blocks where abstraction instrumentation is avoided                                
    def no_abs_instrument(self): 
        return BakAndRestore(self, 'abs_instrument', False)
        
    def visit_with_absdr_args(self, state, n, abs_mode, dr_mode):
        with BakAndRestore(self, 'abs_dr_mode', {'abs_mode':abs_mode, 'dr_mode':dr_mode}):
            with BakAndRestore(self, 'abs_dr_state', state):
                return self.visit(n)
        
    def visit_FileAST(self, n):
        if not self.abs_instrument:
            return super().visit_FileAST(n)

        #Print on macro file, the first set of variables,define and so on...
        # TODO self.transformation_rule.utility.printFirsMacroSet(self.support_variables)

        s = ''
        s += self.abs_dr_rules.aux_vars_decl()

        for ext in n.ext:
            if isinstance(ext, c_ast.FuncDef):
                s += self.visit(ext)
                self.scope = 'global'
            elif isinstance(ext, c_ast.Pragma):
                s += self.visit(ext) + '\n'
            else:
                s += self.visit(ext) + ';\n'

        #TODO check what it means
        #ris = self.faked_typedef_start \
        #      + '\n'.join([item for item in self.transformation_rule.getFakedDefinition()]) \
        #      + '\n' \
        #      + self.faked_typedef_end \
        #      + '\n' \
        #      + s
        ris = s

        #self.addOutputParam('abstraction')
        #self.setOutputParam('abstraction', self)
        #logging.info("Performed transformation: %s" % json.dumps(self.transformation_rule.rules_counter, indent=4))

        #TODO self.dynamicSelection()
        
        self.dynamicSelectionInfoForDebug()

        return ris
        
    def dynamicSelectionInfoForDebug(self):
        print("Starting SSM:",self.string_support_macro)
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
        
        print("Type macro SSM:",self.string_support_macro)
        
    def visit_FuncDef(self, n):
        if not self.abs_instrument:
            return super().visit_FuncDef(n)
        self.scope = 'local'
        func_name = n.decl.name
        if func_name.startswith('__cs_') or func_name == 'assume_abort_if_not':
            # those functions are made by us: won't touch them
            with self.no_abs_instrument():
                ans = super().visit_FuncDef(n)
            return ans
        else:
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
        if not self.abs_instrument:
            return super().visit_Assignment(n)
        return self.abs_dr_rules.rule_Assignment(self.abs_dr_state, n, self.abs_dr_mode['abs_mode'], self.abs_dr_mode['dr_mode'])
        
    def visit_ID(self, n):
        if not self.abs_instrument:
            return super().visit_ID(n)
        ans = super().visit_ID(n) # do the lazy... part
        if n.name in self.funcNames:
            # this is a function name: return verbatim
            return n.name
        return self.abs_dr_rules.rule_ID(self.abs_dr_state, n, self.abs_dr_mode['abs_mode'], self.abs_dr_mode['dr_mode'])
        
    def visit_Constant(self, n):
        if not self.abs_instrument:
            return super().visit_Constant(n)
        return self.abs_dr_rules.rule_Constant(self.abs_dr_state, n, self.abs_dr_mode['abs_mode'], self.abs_dr_mode['dr_mode'])
        
    # TODO do it properly. Just there to make valid code for now
    def visit_FuncCall(self, n):
        if not self.abs_instrument:
            return super().visit_FuncCall(n)
        fref = self.cGen_original._parenthesize_unless_simple(n.name)
        
        if fref == '__CSEQ_assert':
            assert(False, "assert not implemented")
        # all functions are either instrumentation ones or thread functions. Anyways, don't instrument
        with self.no_abs_instrument():
            return super().visit_FuncCall(n)

            
    def visit_Decl(self, n, no_type=False):
        if not self.abs_instrument:
            return super().visit_Decl(n, no_type)
        if no_type:
            return n.name
        if not self.abs_instrument:
            return super().visit_Decl(n)
        else:
            type_of_n = getType(n.type)
            assert(type_of_n == 'TypeDecl' or type_of_n == 'FuncDecl' or type_of_n == 'PtrDecl' or type_of_n == 'ArrayDecl' or type_of_n == 'Struct', 'Invalid type: '+type_of_n)
            
            if hasattr(n,'name') and n.name != None:
                self.saveDeclarationIntoTypeGeneration(type_of_n, n)
                
            if type_of_n == 'FuncDecl':
                assert(n.name != None, "Function declaration does not have a name")
                # store it as function name
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
                with self.no_abs_instrument():
                    ans = super().visit_Decl(n)
                    
            elif type_of_n == 'Struct':
                ans = self.visit_Struct(n.type)
                
            elif type_of_n == 'TypeDecl': # Variable/Constant
                if hasattr(n, 'quals') and len(getattr(n, 'quals')) >= 1 and getattr(n, 'quals')[0] == 'const':
                    with self.no_abs_instrument():
                        ans = super().visit_Decl(n)
                else:
                    # Antonio's comment: struct when no typedef is specified
                    type_st = getType(n.type.type) if n.type.type else None
                    if type_st == 'Struct':
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
                    ans = super().visit_Decl(n)
            elif type_of_n in ('PtrDecl', 'ArrayDecl') :
                type_st = getType(n.type.type) if n.type.type else None
                if type_st == 'Struct':
                    self.integral_type_list.append(n.type.type.name)
                elif hasattr(n.type.type.type, 'names'): #array
                    type_of_arrptr = n.type.type.type.names[0]
                elif hasattr(n.type.type.type, 'name'): #This condition capture the following case: 'static struct device *__local_csmy_callback_dev'
                    type_of_arrptr = n.type.type.type.name 
                elif hasattr(n.type.type.type.type, 'names'): #pointer to array
                    type_of_arrptr = n.type.type.type.type.names[0]
                elif hasattr(n.type.type, 'names'): #variable case
                    assert(False, "This type condition represents a variable in a PtrDecl/ArrayDecl, and it is not expected: "+str(n))
                else:
                    assert(False, "This type condition is not expected: "+str(n))
                
                if type_of_n == 'ArrayDecl' and type_of_arrptr != None and n.name != 'main' and n.type != 'FuncDecl':
                    self.interest_variables_list[n.name] = type_of_arrptr
                    self.program_arrays.append(n.name)


                elif type_of_n == 'PtrDecl' and n.name != None:
                    self.interest_variables_list[n.name] = type_of_arrptr
                    self.program_pointers.append(n.name)
                        
                ans = super().visit_Decl(n)
            else:
                assert(False, "Unknown declaration type: "+type_of_n)
            
            if n.bitsize: 
                #TODO Do I need to treat this?
                pass
            if n.init:
                #TODO
                ans = ans + " /* INSTR DECL "+type_of_n+" init not treated */"
            # TODO have a look at this once you have the initialization ready    
            """
            if self.scope == 'global' and n.name != 'main' and flag_init:
                self.global_declaration.append(final)
                self.translationPerformed = 1
                if print_string != '':
                    self.global_support_macro.append(declaration + '\n' + print_string)
                return ans+';'+'\n'

            elif flag_init and self.scope == 'local':
                last_semicolon = final.rfind(';')
                self.resetOperationBit()
                return ans + ';' + '\n' + final[0:last_semicolon]
            else:
                self.resetOperationBit()
                return ans
            """
            return ans
