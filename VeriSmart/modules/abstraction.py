# coding=utf-8
""" Verismart Abstraction  module
    written by Antonio Mastropaolo for the University of Molise (UNIMOL).
"""
# VERSION = 'abstraction-0.0-2020.06.20'

# This aim of this class and transformation_rule.py is to accomodate the verismart's abstraction integration only.
# Ergo, it's looks like a stub

from __future__ import unicode_literals

import logging
import os


from pycparser import c_ast
from pycparser.c_generator import CGenerator

import core.module
from core.abstractionDir.transformation_rule import TransformationsRule
class abstraction(core.module.Translator):


    def init(self):

        self.typedef_lock = 0
        self.atomic_bit = 0
        self.operationBit = None
        self.indent_level = 0


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


        self.interest_variables_list = {}
        self.program_arrays = []
        self.program_pointers = []
        self.initialized = False
        self.structures = ''

        self.cGen_original = CGenerator()
        self.scope = 'global'
        self.global_declaration = []
        self.main = 0

        self.ignore_list = [
            '__cs_active_thread',
            '__cs_pc',
            '__cs_pc_cs',
            '__cs_last_thread',
            '__cs_thread_local_COND'
            '__cs_thread_lines',
            '__cs_thread_index',
            '__cs_baV',
            '__cs_baL',
            '__cs_ba_assert'
        ]

        self.counter_thread_create = 0

        self.upper_bound = 0
        self.lower_bound = 0
        self.bit_for_bitmask = 0


        #extends the following list when special function or void function are found during parsing
        self.funcCall_to_exclude = ['sscanf',
                                    'exit',
                                    'fprintf',
                                    'printf',
                                    'free',
                                    '__CSEQ_rawline',
                                    '__CSEQ_assume',
                                    '__CSEQ_assert',
                                    'assume_abort_if_not']



        self.placeholder_strip_start = 'START_STRIP_ABT'
        self.placeholder_strip_end = 'END_STRIP_ABT'

        self.faked_typedef_start = 'typedef int %s;\n' % self.placeholder_strip_start
        self.faked_typedef_end = 'typedef int %s;\n' % self.placeholder_strip_end


    #Since abstractionatomicfunction shouldnt exists, when we use the chain with the latter, we have to comment here the method loadfromstring
    def loadfromstring(self, string, env):


        # Set-up unrolling parameters:
        self.env = env
        
        dirname, fname = os.path.split(os.path.abspath(self.env.opts[0][1]))
        #print (self.env.opts[0][1])

        basePath = dirname + '/' + self.env.outputDir

        filename = basePath + fname[0:-1] + 'log'

        #if os.path.exists(filename):
        #    os.remove(filename)

        logging.basicConfig(filename=filename, level=logging.INFO)

        if 'encoding' not in env.paramvalues:
            encoding = 'clean'
        else:
            if env.paramvalues['encoding'] == 'pack_n_repack':
                encoding = 'pack_n_repack'
            else:
                encoding = 'clean'

        self.addInputParam('encoding',
                           'specify the mechanism of encoding for over-approximation (can be "clean" or "pack_n_repack" - see the doc for further information)......',
                           '', default=None, optional=True)

        self.bitmask_interval = int(env.paramvalues['bit_width'])
        self.bitmask_encoding = int(env.paramvalues['bit_width'])

        if 'macro-file' in env.paramvalues:
            self.macro_file_name = basePath + env.paramvalues['macro-file']
            self.transformation_rule = TransformationsRule(self, encoding, self.bitmask_encoding,
                                                               macro_file_name=self.macro_file_name)
        else:
            self.macro_file_name = basePath + 'macro_plain.h'
            self.transformation_rule = TransformationsRule(self, encoding, self.bitmask_encoding)

        self.addInputParam('bid_width', 'specify the bit_width for over-approximation', '', default=None, optional=True)

        self.setOutputParam('header_abstraction', '#include "%s"\n' % self.macro_file_name)

        super(self.__class__, self).loadfromstring(string, env)


    def make_indent(self, level):
        return ' ' * level

    def resetOperationBit(self):
        self.operationBit = None

    def visit_FuncCall(self, n):

        tmp = self.operationBit

        fref = self.cGen_original._parenthesize_unless_simple(n.name)

        if fref == '__CSEQ_assert':

            s = self.transformation_rule.getTR_assert_call()

            if tmp is None:
                self.resetOperationBit()
                return self.transformation_rule.getDeclarations() + '\n' + s

            else:
                self.resetOperationBit()
                return s

        elif fref in self.funcCall_to_exclude:
            return fref + '(' + self.cGen_original.visit(n.args) + ')'

        call = fref + '(' + self.cGen_original.visit(n.args) + ')'

        s = self.transformation_rule.getTR_FuncCall('TRANSF_READ', call, 1) if tmp is None else self.transformation_rule.getTR_FuncCall(tmp, call, 0)

        if tmp is None:
            self.resetOperationBit()
            return self.transformation_rule.getDeclarations() + '\n' + s
        else:
            self.resetOperationBit()
            return s

    def visit_ID(self, n):

        original_exp = self.cGen_original.visit(n)

        if original_exp in self.ignore_list:  # or original_exp in self.special_function_for_seq:
            return original_exp

        elif original_exp.startswith('__cs'):
            return self.cGen_original.visit(n)

        elif not self.interest_variables_list.has_key(original_exp):
            return self.cGen_original.visit(n)

        tmp = None
        if self.operationBit is not None:
            tmp = self.operationBit

        s = self.transformation_rule.getTR_Identifier('TRANSF_READ', n.name,1) if tmp is None else self.transformation_rule.getTR_Identifier(
            self.operationBit, n.name, 0)


        if tmp is None and not self.initialized:
            self.resetOperationBit()
            return self.transformation_rule.getDeclarations() + '\n' + s
        else:
            self.resetOperationBit()
            return s

    def visit_ArrayRef(self, n):

        tmp = self.operationBit
        arrref = self.cGen_original._parenthesize_unless_simple(n.name)

        if arrref.startswith('__cs'):
            return self.cGen_original.visit(n)


        if self.operationBit is None:
            s = self.transformation_rule.getTR_postfix_array('TRANSF_READ', n.subscript, n.name, arrref, 1)

        else:
            s = self.transformation_rule.getTR_postfix_array(self.operationBit, n.subscript, n.name, arrref, 0)


        if tmp is None and not self.initialized:

            declaration = self.transformation_rule.getDeclarations()
            s = declaration + '\n' + s

        self.resetOperationBit()
        return '%s' % s

    def visit_StructRef(self, n):

        tmp = self.operationBit

        sref = self.cGen_original._parenthesize_unless_simple(n.name)
        field = n.field.name
        postfix_expID = sref + n.type + field
        reference = '.'

        if sref.startswith('__cs'):
            return self.cGen_original.visit(n)

        if '->' in postfix_expID:
            reference = '->'

        if tmp is None:

            s = self.transformation_rule.getTR_postfixReference('TRANSF_READ', field, n.name,
                                                                reference, sref, 1)
            declaration = self.transformation_rule.getDeclarations()
            self.resetOperationBit()
            return '%s %s\n ' % (declaration, s)

        else:

            s = self.transformation_rule.getTR_postfixReference(self.operationBit, field, n.name,
                                                                reference, sref, 0)

            self.resetOperationBit()
            return s


    def visit_UnaryOp(self, n):

        tmp = self.operationBit
        operand = self.cGen_original._parenthesize_unless_simple(n.expr)
        original_exp = self.cGen_original.visit(n)

        type_of_expr = self.transformation_rule.getType(n)

        if '[' in operand:
            operand = operand.split('[')[0]
        elif '(*' in operand:
            operand = operand[operand.find("(") + 1:operand.find(")")]
            operand = operand[1:]

        if operand.startswith('__cs'):
            return self.cGen_original.visit(n)

        if type_of_expr == 'StructRef':
            operand = operand.split('.', -1)[1]

        elif type_of_expr == 'ArrayRef':
            operand = operand.split('[')[0]

        # Here we reconstruct the original operand for example employee.id
        # In our interest_variable_list we only have the variable name without the specification of the struct/union

        if n.op == '&':

            # In this case the parameters original_exp and getMacro are dummy and act like placeholders

            s = self.transformation_rule.getTR_unaryOP_castExp('TRANSF_READ', n.expr,
                                                               '&', original_exp,
                                                               1) if self.operationBit is None else self.transformation_rule.getTR_unaryOP_castExp(
                self.operationBit, n.expr, '&', 0)

        elif n.op == '*':

            s = self.transformation_rule.getTR_unaryOP_castExp('TRANSF_READ', n.expr,
                                                               '*', original_exp,
                                                               1) if self.operationBit is None else self.transformation_rule.getTR_unaryOP_castExp(
                self.operationBit, n.expr, '*', 0)


        elif n.op == 'p++':


            s = self.transformation_rule.getTR_postfix_plusplus('TRANSF_READ', operand,
                                                                n.expr,
                                                                1) if self.operationBit is None else self.transformation_rule.getTR_postfix_plusplus(
                self.operationBit, operand, n.expr, 0)


        elif n.op == 'p--':


            s = self.transformation_rule.getTR_postfix_minusminus('TRANSF_READ', operand,
                                                                  n.expr, original_exp,
                                                                  1) if self.operationBit is None else self.transformation_rule.getTR_postfix_minusminus(
                self.operationBit, operand, n.expr, original_exp, 0)



        elif n.op == 'sizeof':

            s = self.transformation_rule.getTR_sizeofUnaryexp('TRANSF_READ', n.expr, original_exp,
                                                              1) if self.operationBit is None else self.transformation_rule.getTR_sizeofUnaryexp(
                self.operationBit, n.expr, original_exp, 0)

        else:

            if len(n.op) == 1:

                if n.op == '+' or n.op == '-' or n.op == '~':
                    s = self.transformation_rule.getTR_plus_minus_tilde_castExp('TRANSF_READ', n.expr,
                                                                                n.op,
                                                                                1) if self.operationBit is None else self.transformation_rule.getTR_plus_minus_tilde_castExp(
                        self.operationBit, n.expr, n.op, 0)



                elif n.op == '!':
                    s = self.transformation_rule.getTR_not_castExp('TRANSF_READ', n.expr,
                                                                   1) if self.operationBit is None else self.transformation_rule.getTR_not_castExp(
                        self.operationBit, n.expr, 0)



                else:
                    s = self.transformation_rule.getTR_unaryOP_castExp('TRANSF_READ', n.expr,
                                                                       n.op, 1) if self.operationBit is None else self.transformation_rule.getTR_unaryOP_castExp(
                        self.operationBit, n.expr, n.op, 0)

            else:

                if n.op == '++':

                    s = self.transformation_rule.getTR_plusplus_unaryexp('TRANSF_READ', operand,
                                                                         n.expr,
                                                                         1) if self.operationBit is None else self.transformation_rule.getTR_plusplus_unaryexp(
                        self.operationBit, operand, n.expr, 0)


                elif n.op == '--':


                    s = self.transformation_rule.getTR_minusminus_unaryexp('TRANSF_READ', operand,
                                                                           n.expr,
                                                                           1) if self.operationBit is None else self.transformation_rule.getTR_minusminus_unaryexp(
                        self.operationBit, operand, n.expr, 0)

                else:
                    s = self.visit(n)

        if tmp is None and not self.initialized:

            self.resetOperationBit()
            declarations = self.transformation_rule.getDeclarations()
            return declarations + '\n' + s

        else:
            self.resetOperationBit()
            return s

    def visit_BinaryOp(self, n):

        tmp = self.operationBit


        if n.op == '&&' or n.op == '||':
            s = self.transformation_rule.getTR_binary_exp_shortcut('TRANSF_READ', n.left, n.right, n.op, 1) if self.operationBit is None else self.transformation_rule.getTR_binary_exp_shortcut(
                self.operationBit, n.left, n.right, n.op, 0)

        else:

            s = self.transformation_rule.getTR_binary_exp_no_shortcut('TRANSF_READ', n.left, n.right, n.op, 1) if self.operationBit is None \
                else self.transformation_rule.getTR_binary_exp_no_shortcut(self.operationBit, n.left, n.right, n.op, 0)



        if tmp is None and not self.initialized:

            declaration = self.transformation_rule.getDeclarations()
            s = declaration + '\n' + s

        self.resetOperationBit()

        return s

    def visit_Assignment(self, n):

        tmp = self.operationBit

        lhs = self.cGen_original.visit(n.lvalue)

       #Seems that we can remove this condition
        if lhs.startswith('__cs') and '__cs_create' not in lhs:
            logging.info('catched')
            return self.cGen_original.visit(n)


        s = self.transformation_rule.getTR_generic_assignment('TRANSF_READ', n.lvalue, n.rvalue,n.op, 1) if self.operationBit is None \
        else self.transformation_rule.getTR_generic_assignment(self.operationBit, n.lvalue, n.rvalue, n.op, 0)


        if tmp is None and not self.initialized:
            declaration = self.transformation_rule.getDeclarations()
            return declaration + '\n' + s

        else:
            self.resetOperationBit()
            return s


    def visit_Decl(self, n, no_type=False):

        # no_type is used when a Decl is part of a DeclList, where the type is
        # explicitly only for the first declaration in a list.
        #
        original_exp = self.cGen_original.visit(n)

        type_of_n = self.transformation_rule.getType(n.type)

        if type_of_n == 'FuncDecl' and hasattr(n,'name'):
            if n.name != None and  not n.name.startswith('__cs_'):
                self.visit(n.type)

        #addressing special case like the functions in self.cas_special_function
        if type_of_n == 'FuncDecl' and hasattr(n.type.type.type, 'names'):
            function_type = ' '.join(n.type.type.type.names)
            if 'void' in function_type:
                self.funcCall_to_exclude.append(n.name)
            if n.name.startswith('__CSEQ_atomic'):
                self.visit(n.type.args)


        qualifier = []
        if hasattr(n, 'quals'):
            qualifier = n.quals
            if len(qualifier) >= 1 and qualifier[0] == 'const':
                if type_of_n == 'TypeDecl':
                    return original_exp


        if n.name in self.ignore_list:
            return original_exp

        #leveraging the short circuit evaluation

        elif n.name is not None and n.name.startswith('__cs'):
            return original_exp

        s = n.name if no_type else self.cGen_original._generate_decl(n)
        if s == 'int main()':
            self.main = 1

        flag_init = False
        final = ''

        all_transformation = ''

        if type_of_n == 'Struct':
            return self.visit_Struct(n.type)
        else:

            # struct when no typedef is specified
            type_st = self.transformation_rule.getType(n.type.type) if n.type.type else None

            if type_st == 'Struct':

                self.integral_type_list.append(n.type.type.name)

            # variable case
            elif (hasattr(n.type.type, 'names')):
                # logging.debug('decl_n: %s ' % str(n.name))

                qualifier = []
                if hasattr(n, 'quals'):
                    qualifier = n.quals


                type_of_var = n.type.type.names[0]
                if n.name != None:
                    #if type_of_var in self.integral_type_list and n.name != 'main':
                        if len(qualifier) >= 1:
                            self.interest_variables_list.__setitem__(n.name, qualifier[0] + ' ' + type_of_var)
                        else:
                            self.interest_variables_list.__setitem__(n.name, type_of_var)
                else:
                    return original_exp



            # array case
            elif hasattr(n.type.type.type, 'names'):
                # We have to assur1e the type of the node we're going to consider is an arraydecl

                if type_of_n == 'ArrayDecl':


                    type_of_array = n.type.type.type.names[0]

                    if type_of_array != None  and n.name != 'main' and n.type != 'FuncDecl':
                        self.interest_variables_list.__setitem__(n.name, type_of_array)
                        self.program_arrays.append(n.name)


                elif type_of_n == 'PtrDecl':

                    type_of_pointer = n.type.type.type.names[0]

                    #if type_of_pointer.startswith('__cs_'):
                    #    self.ignore_list.append(n.name)

                    if n.name != None:

                        self.interest_variables_list.__setitem__(n.name, type_of_pointer)
                        self.program_pointers.append(n.name)


            #This condition capture the following case: 'static struct device *__local_csmy_callback_dev'
            elif hasattr(n.type.type.type, 'name'):

                if type_of_n == 'ArrayDecl':


                    type_of_array = n.type.type.type.name
                    if type_of_array != None and n.name != 'main' and n.type != 'FuncDecl':
                        #if type_of_array in self.integral_type_list and n.name != 'main' and n.type != 'FuncDecl':
                            self.interest_variables_list.__setitem__(n.name, type_of_array)
                            self.program_arrays.append(n.name)


                elif type_of_n == 'PtrDecl':

                    type_of_pointer = n.type.type.type.name

                    if n.name != None:
                        self.interest_variables_list.__setitem__(n.name, type_of_pointer)
                        self.program_pointers.append(n.name)

            #pointer to array
            elif hasattr(n.type.type.type.type, 'names'):

                if type_of_n == 'ArrayDecl':


                    type_of_array = n.type.type.type.type.names[0]
                    if type_of_array != None and n.name != 'main' and n.type != 'FuncDecl':
                        #if type_of_array in self.integral_type_list and n.name != 'main' and n.type != 'FuncDecl':
                            self.interest_variables_list.__setitem__(n.name, type_of_array)
                            self.program_arrays.append(n.name)


                elif type_of_n == 'PtrDecl':

                    type_of_pointer = n.type.type.type.type.names[0]

                    if n.name != None:
                        #if type_of_pointer in self.integral_type_list:
                            self.interest_variables_list.__setitem__(n.name, type_of_pointer)
                            self.program_pointers.append(n.name)

        if n.bitsize: s += ' : ' + self.visit(n.bitsize)
        if n.init:
            flag_init = True
            self.initialized = True
            print_string = ''

            if type_of_n == 'ArrayDecl':
                # I have to create new unary_exp node in this case an array_ref node

                for index, ass_exp in enumerate(n.init):
                    unary_exp = c_ast.ArrayRef(c_ast.ID(n.name), c_ast.Constant('int', str(index)))
                    tr = self.transformation_rule.getTR_assignment('TRANSF_READ', unary_exp, ass_exp, '=', 1)

                    declaration = self.transformation_rule.getDeclarations()
                    all_transformation += declaration + tr + ';' + '\n'
                    final = all_transformation



            elif type_of_n == 'TypeDecl' or type_of_n == 'PtrDecl':
                ass_exp = n.init
                unary_exp = c_ast.ID(n.name)
                tr = self.transformation_rule.getTR_assignment('TRANSF_READ', unary_exp, ass_exp, '=', 1)
                declaration = self.transformation_rule.getDeclarations()
                all_transformation += declaration + tr + ';' + '\n'
                final += all_transformation


            self.initialized = False

        if self.scope == 'global' and n.name != 'main' and flag_init:
            self.global_declaration.append(final)
            return s+';'+'\n'

        elif flag_init and self.scope == 'local':
            last_semicolon = final.rfind(';')
            self.resetOperationBit()
            return s + ';' + '\n' + final[0:last_semicolon]
        else:
            self.resetOperationBit()
            return s

    def visit_Typedef(self, n):

        s = self.cGen_original.visit(n)

        type = self.transformation_rule.getType(n.type.type)

        if n.name  == '_____STARTSTRIPPINGFROMHERE_____':
            self.typedef_lock = 1

        #here we had to customize the condition according to sequenzialization of some specific file of the competition like the ones in C-DAC folder
        if type == 'IdentifierType' and ( n.type.type.names[0] in self.integral_type_list and not self.typedef_lock):
            self.integral_type_list.append(n.name)


        elif type == 'Struct' and n.name not in self.integral_type_list and not n.name.startswith('__cs_') and not self.typedef_lock:
            self.integral_type_list.append(n.name)

        #this branch captures some edge cases like the following one: typedef int (*FuncType)(int,int)
        elif 'typedef' in s and not self.typedef_lock:
            self.integral_type_list.append(n.name)

        if n.name == '_____STOPSTRIPPINGFROMHERE_____':
            self.typedef_lock = 0

        return s

    def visit_Compound(self, n):


        s = self._make_indent() + '{\n'

        self.indent_level += 2
        if n.block_items:
            s += ''.join(self._generate_stmt(stmt) for stmt in n.block_items)
        self.indent_level -= 2
        s += self._make_indent() + '}\n'

        return s

    def visit_Constant(self, n):

        tmp = self.operationBit

        s = self.transformation_rule.getTR_constant('TRANSF_READ', n.value, 1 ) if self.operationBit is None \
            else self.transformation_rule.getTR_constant(self.operationBit, n.value, 0)

        if tmp is None:
            declaration = self.transformation_rule.getDeclarations()
            s = declaration + '\n' + s

        self.resetOperationBit()

        return s


    def visit_FuncDef(self, n):

        self.resetOperationBit()
        self.scope = 'local'
        func_name = n.decl.name

        if func_name.startswith('__cs_'):

            if hasattr(n.decl.type.type.type, 'names'):
                function_type = ' '.join(n.decl.type.type.type.names)
                if 'void' in function_type:
                    self.funcCall_to_exclude.append(func_name)

            elif hasattr(n.decl.type.type.type.type, 'names'):
                function_type = ' '.join(n.decl.type.type.type.type.names)
                if 'void' in function_type:
                    self.funcCall_to_exclude.append(func_name)

            self.visit(n.decl)
            return self.cGen_original.visit_FuncDef(n)

        elif func_name == 'main':

            main_function = self.cGen_original.visit_FuncDef(n)
            main_refined = main_function.strip('int main(void)\n{')
            main_refined = "int main(void){\n\nFIELD_DECLARATION_GLOBAL();\nFIELD_DECLARATION_LOCAL();\n" + '\n'.join([item for item in self.global_declaration]) + '\n' + main_refined

            return main_refined

        decl = self.visit(n.decl)


        self.indent_level = 0

        self.resetOperationBit()


        body = self.visit(n.body)

        if n.param_decls:
            knrdecls = ';\n'.join(self.visit(p) for p in n.param_decls)
            return "....\n" + '\n' + '\n' + "\n" + knrdecls + ';\n' + body + '\n'

        else:

            return decl + '\n' + body + '\n'


    def visit_FileAST(self, n):


        s = ''

        for ext in n.ext:
            if isinstance(ext, c_ast.FuncDef):
                s += self.visit(ext)
                self.scope = 'global'
            elif isinstance(ext, c_ast.Pragma):
                s += self.visit(ext) + '\n'
            else:
                s += self.visit(ext) + ';\n'

        self.addOutputParam('abstraction')
        self.setOutputParam('abstraction', self)

        return s

    def visit_Return(self, n):

        s = 'return '
        if n.expr: s += ' ' + self.cGen_original.visit(n.expr)

        if self.main == 1:
            self.main = 0
            return '\n' + s + ';'
        else:
            return s + ';'

    def visit_ExprList(self, n):

        tmp = self.operationBit

        s = self.transformation_rule.getTR_expr_list('TRANSF_READ', n,  1) if self.operationBit is None \
            else self.transformation_rule.getTR_expr_list(self.operationBit, n, 0)

        if tmp is None:
            declaration = self.transformation_rule.getDeclarations()
            self.resetOperationBit()
            return declaration + '\n' + s

        else:
            self.resetOperationBit()
            return s


    def visit_Cast(self, n):

        tmp = self.operationBit
        if self.operationBit == None:
            tmp = self.operationBit
            self.operationBit = 'TRANSF_READ'

        original_exp = self.cGen_original.visit(n.expr)
        if original_exp.startswith('__cs'):
            return self.cGen_original.visit(n)

        s = '(' + self._generate_type(n.to_type) + ')'

        ris = self.transformation_rule.getTR_typename_castExp(self.operationBit, s, n.expr,1) if tmp is None \
                                                        else self.transformation_rule.getTR_typename_castExp(self.operationBit, s, n.expr, 0)
        self.resetOperationBit()

        if tmp is None:
            declaration = self.transformation_rule.getDeclarations()
            if declaration == '':
                self.transformation_rule.utility.counter_declaration+=1
                return declaration + '\n' + ris
        else:
            return ris

    def visit_TernaryOp(self, n):

        tmp = self.operationBit

        ris = self.transformation_rule.getTR_cond_exp(1, n.cond, n.iftrue, n.iffalse, 1) \
            if tmp is None \
            else self.transformation_rule.getTR_cond_exp(self.operationBit, n.cond, n.iftrue, n.iffalse, 0)

        self.resetOperationBit()
        return ris


    def visit_If(self, n):

            original_exp = self.cGen_original.visit(n.cond)

            #check if is it correct!
            if original_exp.startswith('__cs'):
                return super(abstraction, self).visit(n)

            condition = self.transformation_rule.getTR_if_statement(n.cond, original_exp)


            s = 'if ('
            if n.cond: s += condition
            s += ')\n'

            s += self.visit(n.iftrue)

            if n.iffalse:

                s += self._make_indent() + 'else\n'
                s += self._make_indent()
                s +=  self._generate_stmt(n.iffalse, add_indent=True)

            self.resetOperationBit()
            return 'DECL_%s;\n' % (condition[4:]) + s

    def visit_Struct(self, n):

        if n.name not in self.integral_type_list:
            self.integral_type_list.append(n.name)

        s = self._generate_struct_union_enum(n, 'struct')

        return s



