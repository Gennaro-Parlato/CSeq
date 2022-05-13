# coding=utf-8
""" Verismart Abstraction  module
    written by Antonio Mastropaolo for the University of Molise (UNIMOL).
"""
# VERSION = 'abstraction-0.0-2020.06.20'
from __future__ import unicode_literals

import logging
import json
import os
import re
import subprocess
import shlex
import time
from datetime import datetime
#from flashtext import KeywordProcessor

from pycparser import c_ast
from pycparser.c_generator import CGenerator
#from tqdm import tqdm

import core.module
from core.abstractionDir.transformation_rule_prep import TransformationsRulePrep
import math

import sys

class abstraction_prep(core.module.Translator):


    def init(self):
        self.name_support_file = ''
        # 1 if we are in the zone between _____STARTSTRIPPINGFROMHERE_____ and _____STOPSTRIPPINGFROMHERE_____ (i.e., things that must not be written in the output file)
        self.typedef_lock = 0
        # OPT for the abstraction rules. It is set to None before any statement, and reset to None once the statement ends.
        self.operationBit = None
        # Indentation level (to keep the output code pretty)
        self.indent_level = 0
        # TODO 1 if already computed the new value of the variable (++, --, =, +=, ...) ?
        self.translationPerformed = 0

        # Local expressions for which I should evaluate the type
        self.string_support_macro = ""
        # Header for local expressions type file
        self.string_support_macro_headers = """
#include <stdio.h>
#define PRINT_DT(E,ID, EXP) printf("%s_%d, %d\\n",EXP,ID,typename(E) )
void __CPROVER_get_field(void *a, char field[100] ){return;}
void __CPROVER_set_field(void *a, char field[100], _Bool c){return;}        
        
        """

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

        #The following list need to be expanded every time we found new type. This is a short one
        #self.ammisible_types = ['double','float','void','FuncType']

        #self.visiting_struct = False


        # TODO Global variables. Should I also consider thread locals?
        self.interest_variables_list = {}
        # Array declarations
        self.program_arrays = []
        # Pointer declarations
        self.program_pointers = []
        # True if what we are visiting is part of a variable initialization expression
        self.initialized = False

        # vanilla CGenerator to copy the original code
        self.cGen_original = CGenerator()
        # variable scope (global/local) ?
        self.scope = 'global'
        # TODO ?
        self.field_declaration_global = 'FIELD_DECLARATION_GLOBAL()'
        # TODO ?
        self.field_declaration_local =  'FIELD_DECLARATION_LOCAL()'
        # Global declarations (of everythong)
        self.global_declaration = []
        # Global expressions for which I should evaluate the type
        self.global_support_macro = []
        # 1 if we are visiting nodes inside the main() function, else 0
        self.main = 0
        # Global expressions for which I should evaluate the type support macros
        self.global_support_macro_declarations = ''

        # variables used for instrumentation: they shouldn't be touched
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


        #The following 3 variables are initialized in loadFromString function by considering the input parameters
        # TODO ?
        self.upper_bound = -1
        # TODO ?
        self.lower_bound = -1
        # TODO ?
        self.bit_for_bitmask = -1

        self.support_variables = []

        # Don't touch those functions. Extend the following list when special function or void function are found during parsing
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



        self.placeholder_strip_start = 'START_STRIP_ABT'
        self.placeholder_strip_end = 'END_STRIP_ABT'

        # Delete all the code between those typedefs
        self.faked_typedef_start = 'typedef int %s;\n' % self.placeholder_strip_start
        self.faked_typedef_end = 'typedef int %s;\n' % self.placeholder_strip_end
        
    def setInstanceInfo(self, swarmdirname, filename, confignumber, configintervals):
        self.__swarmdirname = swarmdirname
        self.__filename = filename
        self.__confignumber = confignumber
        self.__intervals = configintervals


    def loadfromstring(self, string, env):
        self.env = env
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).loadfromstring(string, env)
        # Extract the inputfile's directory: we need to create some auxiliary files in the same directory.
        dirname, filename = os.path.split(os.path.abspath(self.env.inputfile))
        basePath = dirname + '/' #dirname + '/' + self.env.outputDir

        if (not os.path.exists(basePath)):
            os.mkdir(basePath)

        # basePath = os.path.abspath(os.getcwd()) + '/' + self.env.outputDir
        
        # AIUI, fname == filename and dname == dirname 
        # TODO keep only one pair of names
        dname, fname = os.path.split(self.env.opts[0][1])

	    # Now, filename represents the logfile 
	    # TODO: rename to log_filename
        filename = basePath + fname[0:-1] + 'log'

        if os.path.exists(filename):
            os.remove(filename)

        logging.basicConfig(filename=str(filename), level=logging.INFO)

        if 'encoding' not in env.paramvalues:
            encoding = 'clean'
        else:
            encoding = 'pack_n_repack'

        self.addInputParam('encoding',
                           'specify the mechanism of encoding for over-approximation (can be "clean" or "pack_n_repack" - see the doc for further information)......',
                           '', default=None, optional=True)

        if 'bit_width' not in env.paramvalues:
            env.paramvalues['bit_width'] = '3'

        if 'encoding' not in env.paramvalues:
            env.paramvalues['encoding'] = 'pack_n_repack'

        # They both represent the abstraction bit_width, once for checking the domains and once for encoding the abstracted values
        self.bitmask_interval = int(env.paramvalues['bit_width'])
        self.bitmask_encoding = int(env.paramvalues['bit_width'])

        # Macro file (the one with all the translations)
        if 'macro-file' in env.paramvalues:
            self.macro_file_name = basePath + env.paramvalues['macro-file']
            self.name_support_file = basePath + fname[0:-1] + 'supp.c' + env.paramvalues['macro-file'][:-2] + '.c'
            self.support_macro_file = open(self.name_support_file, 'a')
            self.transformation_rule = TransformationsRulePrep(self, encoding, self.bitmask_encoding,macro_file_name=self.macro_file_name)
        else:
            self.macro_file_name = basePath + fname[0:-1] + 'macro_plain.h'
            # self.name_support_file = basePath + self.env.opts[0][1][0:-1] + 'supp.c'
            self.name_support_file = basePath + fname[0:-1] + 'supp.c'
            self.support_macro_file = open(self.name_support_file, 'a')
            self.transformation_rule = TransformationsRulePrep(self, encoding, self.bitmask_encoding,macro_file_name=self.macro_file_name)


        # bav & bal for abstraction rules
        self.support_variables.append('_Bool __cs_baL;')
        self.support_variables.append('_Bool __cs_baV;')
        # TODO ?
        self.support_variables.append('_Bool __cs_ba_assert;')
        # TODO ?
        self.support_variables.append('BITVECTOR __cs_bitvector_tmp;')

        self.support_variables.append('_Bool nondetbool(void);\n')

        # Bounds for data types
        self.support_variables.append('const int __cs_int_mask=(1 << %s) - 1;' % self.bitmask_encoding)
        self.support_variables.append('const int __cs_int_min = (%s <= (sizeof(int) * 8) ?  ( 1 << (%s-1) ):  (1 << ((sizeof(int) * 8) - 1)) );'  % ( self.bitmask_interval, self.bitmask_interval) )
        self.support_variables.append('const int __cs_int_max = (%s <= (sizeof(int) * 8) ?  ( (1 << (%s-1) ) - 1 ):  ~(1 << ((sizeof(int) * 8) - 1)) );\n'  % ( self.bitmask_interval, self.bitmask_interval) )


        self.support_variables.append('const short __cs_short_mask=(1 << %s) - 1;' % self.bitmask_encoding)
        self.support_variables.append('const short __cs_short_min = (%s <= (sizeof(short) * 8) ?  ( 1 << (%s-1) ):  (1 << ((sizeof(short) * 8) - 1)) );' % (
        self.bitmask_interval, self.bitmask_interval) )
        self.support_variables.append('const short __cs_short_max = (%s <= (sizeof(short) * 8) ?  ( (1 << (%s-1) ) - 1 ):  ~(1 << ((sizeof(short) * 8) - 1)) );\n' % (
        self.bitmask_interval, self.bitmask_interval) )

        self.support_variables.append('const long  __cs_long_mask=(1 << %s) - 1;' % self.bitmask_encoding )
        self.support_variables.append('const long  __cs_long_min = (%s <= (sizeof(long) * 8) ?  ( 1 << (%s-1) ):  (1 << ((sizeof(long) * 8) - 1)) );' % (
            self.bitmask_interval, self.bitmask_interval) )
        self.support_variables.append('const long  __cs_long_max = (%s <= (sizeof(long) * 8) ?  ( (1 << (%s-1) ) - 1 ):  ~(1 << ((sizeof(long) * 8) - 1)) );\n' % (
        self.bitmask_interval, self.bitmask_interval) )

        self.support_variables.append('const long long __cs_long_long_mask=(1 << %s) - 1;' % self.bitmask_encoding)
        self.support_variables.append(
            'const long long __cs_long_long_min = (%s <= (sizeof(long long) * 8) ?  ( 1 << (%s-1) ):  (1 << ((sizeof(long long) * 8) - 1)) );' % (
            self.bitmask_interval, self.bitmask_interval) )
        self.support_variables.append(
            'const long long __cs_long_long_max = (%s <= (sizeof(long long) * 8) ?  ( (1 << (%s-1) ) - 1 ):  ~(1 << ((sizeof(long long) * 8) - 1)) );\n' % (
            self.bitmask_interval, self.bitmask_interval) )

        self.support_variables.append('const char __cs_char_mask=(1 << %s) - 1;' % self.bitmask_encoding)
        self.support_variables.append(
            'const char __cs_char_min = (%s <= (sizeof(char) * 8) ?  ( 1 << (%s-1) ):  (1 << ((sizeof(char) * 8) - 1)) );' % (
            self.bitmask_interval, self.bitmask_interval) )
        self.support_variables.append(
            'const char __cs_char_max = (%s <= (sizeof(char) * 8) ?  ( (1 << (%s-1) ) - 1 ):  ~(1 << ((sizeof(char) * 8) - 1)) );\n' % (
            self.bitmask_interval, self.bitmask_interval) )

        self.addInputParam('bid_width', 'specify the bit_width for over-approximation', '', default=None, optional=True)

        # Include the macro file
        self.setOutputParam('header_abstraction','#include "%s"\n' % self.macro_file_name)

        super(self.__class__, self).loadfromstring(string, env)


    def make_indent(self, level):
        return ' ' * level

    def resetOperationBit(self):
        self.operationBit = None

    def visit_FuncCall(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_FuncCall(n)
        
        
        tmp = self.operationBit

        fref = self.cGen_original._parenthesize_unless_simple(n.name)
        
        if fref == '__CSEQ_assert':
            # that's an assert

            s = self.transformation_rule.getTR_assert_call(n.args)

            if tmp is None: # this is a full statement: return also the declarations you might have needed to compile the statement
                self.resetOperationBit()
                return self.transformation_rule.getDeclarations() + '\n' + s

            else: # this is part of an expression: just return the instrumented call
                self.resetOperationBit()
                return s

        elif fref in self.funcCall_to_exclude:
            # That's either a special function or a void function. Don't touch it
            return fref + '(' + self.cGen_original.visit(n.args) + ')'


        # call expression
        call = fref + '(' + self.cGen_original.visit(n.args) + ')'

        # instrument call
        s = self.transformation_rule.getTR_FuncCall('TRANSF_READ', call, 1) if tmp is None else self.transformation_rule.getTR_FuncCall(tmp, call, 0)

        if tmp is None: # this is a full statement: return also the declarations you might have needed to compile the statement
            self.resetOperationBit()
            return self.transformation_rule.getDeclarations() + '\n' + s
        else: # this is part of an expression: just return the instrumented call
            self.resetOperationBit()
            return s

    def visit_ID(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_ID(n)
        

        original_exp = self.cGen_original.visit(n)

        # Those variables were introduced for instrumentation: don't touch them and return the original expression.
        if original_exp in self.ignore_list:  # or original_exp in self.special_function_for_seq:
            return original_exp

        # TODO in previous infrastructure, __cs didn't identify thread local variables. Check that this is ok in this edition.
        # An instrumentation variable or threadlocal is the first operand of the condition. Ok only if no brackets or whatsoever before. Keep this in mind while instrumenting in previous modules.
        elif original_exp.startswith('__cs'):
            # TODO why repeating the visit?
            return self.cGen_original.visit(n)

        # TODO what is self.interest_variables_list?
        elif original_exp not in self.interest_variables_list:
            # TODO why repeating the visit?
            return self.cGen_original.visit(n)

        # backup the operationBit
        tmp = None
        if self.operationBit is not None:
            tmp = self.operationBit

        # get the translation using a fresh macro name
        s = self.transformation_rule.getTR_Identifier('TRANSF_READ', n.name,
                                                      1) if tmp is None else self.transformation_rule.getTR_Identifier(
            self.operationBit, n.name, 0)

        if tmp == 'GET_VALUE': 
            # get the type for ID
            macro_key = self.transformation_rule.macro_key.pop()
            local_exp = self.transformation_rule.getLocal(macro_key)
            print_string = 'PRINT_DT(%s, %s, "LOCALEXP" )' % (
                local_exp, self.transformation_rule.utility.local_macro_counter - 1)
            if self.scope == 'global':
                self.global_support_macro.append(print_string + ';\n')
            else:
                self.string_support_macro += print_string + ';\n'


        if tmp is None and not self.initialized:
            # that's a full statement not during any variable initialization: return also the declarations you might have needed to compile the statement
            self.resetOperationBit()
            return self.transformation_rule.getDeclarations() + '\n' + s
        else: # you are in an expression: just return the instrumented call
            self.resetOperationBit()
            return s

    def visit_ArrayRef(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_ArrayRef(n)
        

        macro_key = None

        tmp = self.operationBit
        arrref = self.cGen_original._parenthesize_unless_simple(n.name)

        if arrref.startswith('__cs'):
            # that's something coming from instrumentation: don't touch it
            return self.cGen_original.visit(n)


        if self.operationBit is None:
            # statement
            s = self.transformation_rule.getTR_postfix_array('TRANSF_READ', n.subscript, n.name, arrref, 1)

        else:
            # inside an expression
            s = self.transformation_rule.getTR_postfix_array(self.operationBit, n.subscript, n.name, arrref, 0)

            if tmp == 'GET_VALUE':
                # you need its type: compute it
                macro_key = self.transformation_rule.macro_key.pop()
                local_exp = self.transformation_rule.getLocal(macro_key)
                print_string = 'PRINT_DT(%s, %s, "LOCALEXP" )' % (local_exp, self.transformation_rule.utility.local_macro_counter - 1)
                if self.scope == 'global':
                    self.global_support_macro.append( print_string + ';\n')
                else:
                    self.string_support_macro += print_string + ';\n'


        if tmp is None and not self.initialized:
            # statement on it's own not in an initialization: return also the declarations you might have needed to compile the statement.
            declaration = self.transformation_rule.getDeclarations()
            s = declaration + '\n' + s

        self.resetOperationBit()
        return '%s' % s

    def visit_StructRef(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_StructRef(n)
        

        tmp = self.operationBit

        macro_key = None

        sref = self.cGen_original._parenthesize_unless_simple(n.name)
        field = n.field.name
        # structure (./->) field
        postfix_expID = sref + n.type + field
        reference = '.'

        if sref.startswith('__cs'):
            # that's something coming from instrumentation: don't touch it
            return self.cGen_original.visit(n)

        if '->' in postfix_expID:
            # accessing through pointer (->)
            reference = '->'
        # else: accessing through variable (.)

        if tmp is None:
            # statement: return also the declarations you might have needed to compile the statement.
            s = self.transformation_rule.getTR_postfixReference('TRANSF_READ', field, n.name,
                                                                reference, sref, 1)
            declaration = self.transformation_rule.getDeclarations()
            self.resetOperationBit()
            # TODO shouldn't that be \n and ; ?
            return '%s %s\n ' % (declaration, s)

        else:
            # part of expression
            s = self.transformation_rule.getTR_postfixReference(self.operationBit, field, n.name,
                                                                reference, sref, 0)

            if tmp == 'GET_VALUE':
                # you need also its type
                macro_key = self.transformation_rule.macro_key.pop()
                local_exp = self.transformation_rule.getLocal(macro_key)
                print_string = 'PRINT_DT(%s, %s, "LOCALEXP" )' % (
                local_exp, self.transformation_rule.utility.local_macro_counter - 1)
                self.string_support_macro += print_string + ';\n'


            self.resetOperationBit()
            return s


    def visit_UnaryOp(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_UnaryOp(n)
        

        macro_key = None

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
            # that's something coming from instrumentation: don't touch it
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


            if tmp == 'GET_VALUE':
                # you need its type
                macro_key = self.transformation_rule.macro_key.pop()
                local_exp = self.transformation_rule.getLocal(macro_key)
                print_string = 'PRINT_DT(%s, %s, "LOCALEXP" )' % (
                    local_exp, self.transformation_rule.utility.local_macro_counter - 1)

                if self.scope == 'global':
                    self.global_support_macro.append(print_string + ';\n')
                else:
                    self.string_support_macro += print_string + ';\n'

                macro_key = None

        elif n.op == 'p++':

            self.translationPerformed = 1

            s = self.transformation_rule.getTR_postfix_plusplus('TRANSF_READ', operand,
                                                                n.expr,
                                                                1) if self.operationBit is None else self.transformation_rule.getTR_postfix_plusplus(
                self.operationBit, operand, n.expr, 0)

            macro_key = self.transformation_rule.macro_key.pop()

        elif n.op == 'p--':

            self.translationPerformed = 1

            s = self.transformation_rule.getTR_postfix_minusminus('TRANSF_READ', operand,
                                                                  n.expr, original_exp,
                                                                  1) if self.operationBit is None else self.transformation_rule.getTR_postfix_minusminus(
                self.operationBit, operand, n.expr, original_exp, 0)

            macro_key = self.transformation_rule.macro_key.pop()

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

                    if tmp == 'TRANSF_READ' and n.op == '-':
                        macro_key = self.transformation_rule.macro_key.pop()

                elif n.op == '!':
                    s = self.transformation_rule.getTR_not_castExp('TRANSF_READ', n.expr,
                                                                   1) if self.operationBit is None else self.transformation_rule.getTR_not_castExp(
                        self.operationBit, n.expr, 0)

                    if tmp=='TRANSF_READ':
                        macro_key = self.transformation_rule.macro_key.pop()

                else:
                    s = self.transformation_rule.getTR_unaryOP_castExp('TRANSF_READ', n.expr,
                                                                       n.op, 1) if self.operationBit is None else self.transformation_rule.getTR_unaryOP_castExp(
                        self.operationBit, n.expr, n.op, 0)

            else:

                if n.op == '++':

                    self.translationPerformed = 1

                    s = self.transformation_rule.getTR_plusplus_unaryexp('TRANSF_READ', operand,
                                                                         n.expr,
                                                                         1) if self.operationBit is None else self.transformation_rule.getTR_plusplus_unaryexp(
                        self.operationBit, operand, n.expr, 0)

                    macro_key = self.transformation_rule.macro_key.pop()

                elif n.op == '--':

                    self.translationPerformed = 1

                    s = self.transformation_rule.getTR_minusminus_unaryexp('TRANSF_READ', operand,
                                                                           n.expr,
                                                                           1) if self.operationBit is None else self.transformation_rule.getTR_minusminus_unaryexp(
                        self.operationBit, operand, n.expr, 0)

                    macro_key = self.transformation_rule.macro_key.pop()
                else:
                    s = self.visit(n)

        if tmp is None and not self.initialized:
            # statement: return also the declarations you might have needed to compile the statement.
            self.resetOperationBit()
            declarations = self.transformation_rule.getDeclarations()

            if macro_key is not None:
                # you need its type: compute it
                self.string_support_macro+=declarations+'\n'
                local_exp = self.transformation_rule.getLocal(macro_key)
                print_string = 'PRINT_DT(%s, %s, "EXP" )' % (local_exp, self.transformation_rule.utility.macro_counter - 1)

                if self.scope == 'global':
                    self.global_support_macro.append(print_string + ';\n')
                else:
                    self.string_support_macro += print_string + ';\n'

            return declarations + '\n' + s
        else:
            self.resetOperationBit()

            if macro_key is not None:
                # you need its type: compute it
                local_exp = self.transformation_rule.getLocal(macro_key)
                print_string = 'PRINT_DT(%s, %s, "LOCALEXP" )' % (local_exp, self.transformation_rule.utility.local_macro_counter - 1)

                if self.scope == 'global':
                    self.global_support_macro.append(print_string + ';\n')
                else:
                    self.string_support_macro += print_string + ';\n'

            return s

    def visit_BinaryOp(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_BinaryOp(n)
        

        tmp = self.operationBit


        if n.op == '&&' or n.op == '||':
            s = self.transformation_rule.getTR_binary_exp_shortcut('TRANSF_READ', n.left, n.right, n.op, 1) if self.operationBit is None else self.transformation_rule.getTR_binary_exp_shortcut(
                self.operationBit, n.left, n.right, n.op, 0)

        else:

            s = self.transformation_rule.getTR_binary_exp_no_shortcut('TRANSF_READ', n.left, n.right, n.op, 1) if self.operationBit is None \
                else self.transformation_rule.getTR_binary_exp_no_shortcut(self.operationBit, n.left, n.right, n.op, 0)

            if tmp == 'TRANSF_READ':

                macro_key = self.transformation_rule.macro_key.pop()
                local_exp = self.transformation_rule.getLocal(macro_key)
                print_string = 'PRINT_DT(%s, %s, "LOCALEXP" )' % (local_exp, self.transformation_rule.utility.local_macro_counter - 1)

                if self.scope == 'global':
                    self.global_support_macro.append(print_string + ';\n')
                else:
                    self.string_support_macro += print_string + ';\n'

        if tmp is None and not self.initialized:

            declaration = self.transformation_rule.getDeclarations()
            macro_key = self.transformation_rule.macro_key.pop()
            local_exp = self.transformation_rule.getLocal(macro_key)
            print_string = 'PRINT_DT(%s, %s, "EXP" )' % (
            local_exp, self.transformation_rule.utility.macro_counter - 1)
            self.string_support_macro += print_string + ';\n'

            s = declaration + '\n' + s

        self.resetOperationBit()

        return s

    def visit_Assignment(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_Assignment(n)
        

        tmp = self.operationBit

        lhs = self.cGen_original.visit(n.lvalue)

       #Seems that we can remove this condition
        if lhs.startswith('__cs') and '__cs_create' not in lhs:
            logging.info('catched')
            return self.cGen_original.visit(n)


        s = self.transformation_rule.getTR_generic_assignment('TRANSF_READ', n.lvalue, n.rvalue,n.op, 1) if self.operationBit is None \
        else self.transformation_rule.getTR_generic_assignment(self.operationBit, n.lvalue, n.rvalue, n.op, 0)

        if tmp is None and not self.initialized:

            self.translationPerformed = 1
            declaration = self.transformation_rule.getDeclarations()
            self.resetOperationBit()
            self.string_support_macro += declaration
            macro_key = self.transformation_rule.macro_key.pop()
            local_exp = self.transformation_rule.getLocal( macro_key )

            print_string = 'PRINT_DT(%s, %s, "EXP" )' % ( local_exp, self.transformation_rule.utility.macro_counter-1)

            if self.scope == 'global':
                self.global_support_macro.append(print_string + ';\n')
            else:
                self.string_support_macro += print_string + ';\n'

            return declaration + '\n' + s

        else:
            self.resetOperationBit()

            macro_key = self.transformation_rule.macro_key.pop()
            local_exp = self.transformation_rule.getLocal( macro_key)
            print_string = 'PRINT_DT(%s, %s, "LOCALEXP" )' % (
            local_exp, self.transformation_rule.utility.local_macro_counter - 1)

            if self.scope == 'global':
                self.global_support_macro.append(print_string + ';\n')
            else:
                self.string_support_macro += print_string + ';\n'

            return s


    def visit_Decl(self, n, no_type=False):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_Decl(n)

        original_exp = self.cGen_original.visit(n)

        type_of_n = self.transformation_rule.getType(n.type)

        if type_of_n == 'FuncDecl' and hasattr(n,'name'):
            if n.name != None and not n.name.startswith('__cs_'):
                self.visit(n.type)

        if hasattr(n,'name'):
            if n.name != None and (not n.name.startswith('__cs_') or n.name.startswith('__cs_local_') or n.name.startswith('__cs_retval_') or n.name.startswith('__cs_param_')): #or (n.name.startswith('__cs_thread_local_') and n.name != "__cs_thread_local_COND")): #and not self.visiting_struct:
                self.checkForWriting(type_of_n, n)

        if type_of_n == 'FuncDecl':

            if hasattr(n.type.type.type, 'names'):
                function_type = ' '.join(n.type.type.type.names)
                if 'void' in function_type:
                    self.funcCall_to_exclude.append(n.name)

            elif hasattr(n.type.type.type.type, 'names'):
                function_type = ' '.join(n.type.type.type.type.names)
                if 'void' in function_type:
                    self.funcCall_to_exclude.append(n.name)

            if n.name.startswith('__CSEQ_atomic'):
                self.visit(n.type.args)


        if hasattr(n, 'quals'):
            qualifier = n.quals
            if len(qualifier) >= 1 and qualifier[0] == 'const':
                if type_of_n == 'TypeDecl':
                    return original_exp

        if n.name in self.ignore_list:
            return original_exp


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

                    #local_exp = self.transformation_rule.getLocal(self.transformation_rule.macro_key.pop())
                    #print_string = 'PRINT_DT(%s, %s, "EXP");' % (local_exp, self.transformation_rule.utility.macro_counter - 1)
                    #self.global_support_macro.append(declaration + '\n' + print_string)

            elif type_of_n == 'TypeDecl' or type_of_n == 'PtrDecl':
                ass_exp = n.init
                unary_exp = c_ast.ID(n.name)
                tr = self.transformation_rule.getTR_assignment('TRANSF_READ', unary_exp, ass_exp, '=', 1)
                declaration = self.transformation_rule.getDeclarations()
                all_transformation += declaration + tr + ';' + '\n'
                final += all_transformation
                local_exp = self.transformation_rule.getLocal(self.transformation_rule.macro_key.pop() )
                print_string = 'PRINT_DT(%s, %s, "EXP");' % (local_exp, self.transformation_rule.utility.macro_counter - 1)

            self.initialized = False

        if self.scope == 'global' and n.name != 'main' and flag_init:
            self.global_declaration.append(final)
            self.translationPerformed = 1
            if print_string != '':
                self.global_support_macro.append(declaration + '\n' + print_string)
            return s+';'+'\n'

        elif flag_init and self.scope == 'local':
            last_semicolon = final.rfind(';')
            self.resetOperationBit()
            return s + ';' + '\n' + final[0:last_semicolon]
        else:
            self.resetOperationBit()
            return s

    def visit_Typedef(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_Typedef(n)

        s = self.cGen_original.visit(n)

        type = self.transformation_rule.getType(n.type.type)

        if n.name  == '_____STARTSTRIPPINGFROMHERE_____':
            self.typedef_lock = 1

        #here we had to customize the condition according to sequenzialization of some specific file of the competition like the ones in C-DAC folder
        if type == 'IdentifierType' and ( n.type.type.names[0] in self.integral_type_list and not self.typedef_lock):
            self.global_support_macro_declarations += s + ';\n'
            self.integral_type_list.append(n.name)

        elif type == 'Struct' and n.name not in self.integral_type_list and not n.name.startswith('__cs_') and not self.typedef_lock:
            self.integral_type_list.append(n.name)
            self.global_support_macro_declarations+=s+';\n'

        #this branch captures some edge cases like the following one: typedef int (*FuncType)(int,int)
        elif 'typedef' in s and not self.typedef_lock:
            self.global_support_macro_declarations += s + ';\n'
            self.integral_type_list.append(n.name)

        if n.name == '_____STOPSTRIPPINGFROMHERE_____':
            self.typedef_lock = 0

        return s

    def visit_Compound(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_Compound(n)

        # In the instrumented version (s), convert each instruction and put {} around to keep the scope.
        # In the macro file to get types (string_support_macro), you need to put the macros for the types (together with declarations), and keep the {} for the scope
        s = self._make_indent() + '{\n'

        self.string_support_macro += s+'\n'


        self.indent_level += 2
        if n.block_items:
            # instrument each instruction
            s += ''.join(self._generate_stmt(stmt) for stmt in n.block_items)
        self.indent_level -= 2
        s += self._make_indent() + '}\n'

        self.string_support_macro +=  self._make_indent() + '}\n'

        return s

    def visit_Constant(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_Constant(n)
        

        tmp = self.operationBit

        s = self.transformation_rule.getTR_constant('TRANSF_READ', n.value, 1 ) if self.operationBit is None \
            else self.transformation_rule.getTR_constant(self.operationBit, n.value, 0)

        if tmp is None:
            declaration = self.transformation_rule.getDeclarations()
            s = declaration + '\n' + s

        self.resetOperationBit()

        return s



    def visit_FuncDef(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_FuncDef(n)
        self.resetOperationBit()
        self.scope = 'local'
        func_name = n.decl.name

        if func_name.startswith('__cs_') or func_name == 'assume_abort_if_not':

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
            self.string_support_macro += '{\n'
            self.string_support_macro +=  ';\n'.join(self.global_support_macro)
            self.string_support_macro += '\n}\n'

            return main_refined

        decl = self.visit(n.decl)

        """if func_name.startswith('__CSEQ_atomic'):
            decl = self.visit(n.decl)
        else:
            decl = self.cGen_original.visit(n.decl)"""

        self.indent_level = 0

        self.resetOperationBit()

        #self.string_support_macro+='{\n'

        body = self.visit(n.body)

        #if not self.translationPerformed:
        #    self.string_support_macro = self.string_support_macro[0:(len(self.string_support_macro)-2)]

        if n.param_decls:

            knrdecls = ';\n'.join(self.visit(p) for p in n.param_decls)
            if self.translationPerformed:
                #self.string_support_macro += '}\n'
                self.translationPerformed = 0

            return "....\n" + '\n' + '\n' + "\n" + knrdecls + ';\n' + body + '\n'

        else:
            if self.translationPerformed:
                #self.string_support_macro += '}\n'
                self.translationPerformed = 0

            return decl + '\n' + body + '\n'


    def visit_FileAST(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_FileAST(n)

        #Print on macro file, the first set of variables,define and so on...
        self.transformation_rule.utility.printFirsMacroSet(self.support_variables)

        s = ''

        for ext in n.ext:
            if isinstance(ext, c_ast.FuncDef):
                s += self.visit(ext)
                self.scope = 'global'
            elif isinstance(ext, c_ast.Pragma):
                s += self.visit(ext) + '\n'
            else:
                s += self.visit(ext) + ';\n'

        ris = self.faked_typedef_start \
              + '\n'.join([item for item in self.transformation_rule.getFakedDefinition()]) \
              + '\n' \
              + self.faked_typedef_end \
              + '\n' \
              + s

        self.addOutputParam('abstraction')
        self.setOutputParam('abstraction', self)
        logging.info("Performed transformation: %s" % json.dumps(self.transformation_rule.rules_counter, indent=4))

        self.dynamicSelection()

        return ris

    def visit_Return(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_Return(n)
        

        s = 'return '
        if n.expr: s += ' ' + self.cGen_original.visit(n.expr)

        if self.main == 1:
            self.main = 0
            return '\n' + s + ';'
        else:
            return s + ';'

    def visit_ExprList(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_ExprList(n)
        

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
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_Cast(n)
        

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
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_TernaryOp(n)
        


        tmp = self.operationBit

        ris = self.transformation_rule.getTR_cond_exp(1, n.cond, n.iftrue, n.iffalse, 1) \
            if tmp is None \
            else self.transformation_rule.getTR_cond_exp(self.operationBit, n.cond, n.iftrue, n.iffalse, 0)

        if tmp == 'GET_VALUE':
            macro_key = self.transformation_rule.macro_key.pop()
            local_exp = self.transformation_rule.getLocal(macro_key)

            print_string = 'PRINT_DT(%s, %s, "LOCALEXP" )' % (
                local_exp, self.transformation_rule.utility.local_macro_counter - 1)

            if self.scope == 'global':
                self.global_support_macro.append(print_string + ';\n')
            else:
                self.string_support_macro += print_string + ';\n'

        self.resetOperationBit()
        return ris


    def visit_If(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_If(n)
        

        original_exp = self.cGen_original.visit(n.cond)


        if original_exp.startswith('__cs'):
            #print('visit_If',original_exp,n.cond)
            #return super(abstraction_prep, self).visit(n)
            return super(self.__class__, self).visit_If(n)

        condition = self.transformation_rule.getTR_if_statement(n.cond, original_exp)
        decl = self.transformation_rule.getDeclarations()

        s = 'if ('
        if n.cond: s += condition
        s += ')\n'

        s += self.visit(n.iftrue)

        if n.iffalse:

            s += self._make_indent() + 'else\n'
            s += self._make_indent()
            s +=  self._generate_stmt(n.iffalse, add_indent=True)

        self.resetOperationBit()
        if 'DECL' in decl:
            return decl + s
        else:
            return  s


    def visit_Struct(self, n):
        if not self.env.enableAbstraction:
            #not interested in abstraction: passthrough
            return super(self.__class__, self).visit_Struct(n)

        #self.visiting_struct = True

        if n.name not in self.integral_type_list:
            self.integral_type_list.append(n.name)

        s = self._generate_struct_union_enum(n, 'struct')

        if not n.name.startswith('__cs_'):
            clean = self.transformation_rule.utility.cleanDirtyString(s)
            if '{'  in clean:
                clean = clean.replace('\n','')+';\n'
                self.string_support_macro+=clean

        #self.visiting_struct = False

        return s


    def checkForWriting(self, type, node):

        to_write = False
        write_this = self.cGen_original.visit(node)

        if type == 'TypeDecl' or type == 'FuncDecl' or type == 'PtrDecl' or type == 'ArrayDecl':
            to_write = True

        # Struct addressed in visit struct
        elif type == 'Struct':
            pass

        if to_write:
            if self.scope == 'global':
                self.global_support_macro_declarations += write_this + ';\n'
            else:
                self.string_support_macro += write_this + ';\n'


    def findnth(self, string, substring, n):
        parts = string.split(substring, n + 1)
        if len(parts) <= n + 1:
            return -1
        return len(string) - len(parts[-1]) - len(substring)

    def dynamicSelection(self):

        #this will be the text to put into a main
        str_to_append = ''
        global_text = ''
        inRecording = False

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

        self.support_macro_file.write(self.string_support_macro)
        self.support_macro_file.close()
        self.transformation_rule.utility.macro_file.close()


        logging.info("Time before compiling: %s\n", datetime.fromtimestamp(time.time()) )

        command = "gcc --std=c11 %s" % self.name_support_file
        process = subprocess.Popen(shlex.split(command), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        _ = process.communicate()[0].decode('utf-8').split('\n')
        process.wait()

        logging.info("Time after compiling: %s\n", datetime.fromtimestamp(time.time()))

        logging.info("Time before running: %s", datetime.fromtimestamp(time.time()))

        # run (to get types)
        command = "./a.out"
        process = subprocess.Popen(shlex.split(command), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        result = process.communicate()[0].decode('utf-8').split('\n')

        process.wait()

        logging.info("Time after running: %s", datetime.fromtimestamp(time.time()))

        current_path = os.path.abspath(os.getcwd())

        if os.path.exists('%s' % (self.name_support_file) ):
            os.remove('%s' % (self.name_support_file) )
            os.remove('%s/a.out' % current_path)


            # ----------------------------------------------------------------#

            macro_file = open(self.macro_file_name,'r+')
            data = macro_file.read()
            data = data.replace('#define BITVECTOR int',"#define BITVECTOR __CPROVER_bitvector[%s]" % (self.bitmask_encoding))
            macro_file.write(data)
            macro_file.close()


            # ----------------------------------------------------------------#

            # processing the output of a.out

            dictExpressions={}

            for exp in (result):

                if 'LOCALEXP' in exp or 'EXP' in exp:
                    type_exp = exp.split(',')[1]
                    idx_expression = exp.split(',')[0].split('_')[1]

                    if 'LOCALEXP' in exp:
                        string_exp_type = 'LOCAL_EXP_%s' % idx_expression
                        dict_key = self.transformation_rule.placeholder % string_exp_type
                    else:
                        string_exp_type = 'EXP_%s()' % idx_expression
                        dict_key = self.transformation_rule.placeholder % string_exp_type[0:-2]

                    #expression_object = self.transformation_rule.placeholder_object[dict_key].values()[0]
                    expression_object = list(self.transformation_rule.placeholder_object[dict_key].values())[0]
                    expression_name = expression_object.name


                    # abstractable case
                    if int(type_exp) < 10:

                        if expression_name == 'postfix_plusplus' or expression_name == 'plusplus_unaryexp':

                            if expression_object.t_type != 'GET_VALUE':
                                body = expression_object.body['abt']
                                matching_tuple = self.transformation_rule.types_map.get(int(type_exp))
                                position_max = self.transformation_rule.getTypeMatch(matching_tuple[1])

                                if position_max>=5: position_max=abs(position_max-5)

                                max_item = expression_object.body['max_list'][position_max]
                                body = body.replace('__place__', max_item)

                                encoding_type = expression_object.body['encoding'][position_max]
                                body = body.replace('__encoding__', encoding_type)

                            else:
                                body = expression_object.body['abt']

                        elif expression_name == '-_castExp':

                            if expression_object.t_type == 'TRANSF_READ':
                                body = expression_object.body['abt']
                                matching_tuple = self.transformation_rule.types_map.get(int(type_exp))
                                position_min = self.transformation_rule.getTypeMatch(matching_tuple[1])

                                if position_min >= 5: position_min = abs(position_min - 5)

                                min_item = expression_object.body['min_list'][position_min]
                                body = body.replace('__place__', min_item)


                        elif expression_name == 'binary_exp_no_shortcut':

                            if expression_object.t_type == 'TRANSF_READ':

                                body = expression_object.body['abt']
                                matching_tuple = self.transformation_rule.types_map.get(int(type_exp))
                                position_bounds = self.transformation_rule.getTypeMatch(matching_tuple[1])

                                if matching_tuple[0] == 'signed':
                                    bounds_item = expression_object.body['bounds_signed_list'][position_bounds]
                                else:
                                    bounds_item = expression_object.body['bounds_unsigned_list'][position_bounds - 5]

                                body = body.replace('__place__', bounds_item)


                        elif expression_name == 'postfix_minusminus' or expression_name == 'minusminus_unaryexp':

                            if expression_object.t_type != 'GET_VALUE':
                                body = expression_object.body['abt']
                                matching_tuple = self.transformation_rule.types_map.get(int(type_exp))
                                position_min = self.transformation_rule.getTypeMatch(matching_tuple[1])

                                if position_min >= 5: position_min = abs(position_min - 5)

                                min_item = expression_object.body['min_list'][position_min]
                                body = body.replace('__place__', min_item)

                                encoding_type = expression_object.body['encoding'][position_min]
                                body = body.replace('__encoding__', encoding_type)

                            else:
                                body = expression_object.body['abt']


                        elif expression_name == 'generic_assignment' or expression_name == 'assignment':


                            #int char long int short long long

                            if expression_object.t_type != 'GET_VALUE':
                                body = expression_object.body['abt']
                                matching_tuple = self.transformation_rule.types_map.get(int(type_exp))
                                position_bounds = self.transformation_rule.getTypeMatch(matching_tuple[1])

                                if matching_tuple[0] == 'signed':
                                    bounds_item = expression_object.body['bounds_signed_list'][position_bounds]
                                    encoding_type = expression_object.body['encoding'][position_bounds]
                                else:
                                    bounds_item = expression_object.body['bounds_unsigned_list'][position_bounds-5]
                                    encoding_type = expression_object.body['encoding'][position_bounds-5]


                                body = body.replace('__place__', bounds_item)
                                body = body.replace('__encoding__', encoding_type)

                            else:
                                body = expression_object.body['abt']

                        elif expression_name == 'postfixReference_arrow' or expression_name == 'postfixReference_dot' \
                                or expression_name == '*_castExp' or expression_name == 'postfix_array' \
                                or expression_name == 'cond_exp' or expression_name == 'not_castExp' or expression_name == 'identifier':

                            body = expression_object.body['abt']
                            if 'DECODE' in body:
                                type_decode = self.transformation_rule.types_map[int(type_exp)]
                                type_decode = type_decode[0]
                                if type_decode == 'unsigned':
                                    body = body.replace('DECODE', 'DECODE_UNSIGNED')
                                else:
                                    body = body.replace('DECODE', 'DECODE_SIGNED')
                        else:
                            pass

                    else:
                        body = expression_object.body['no_abt']



                    macro_to_write = '#define %s\n%s' % (string_exp_type, body)
                    macro_to_write = self.transformation_rule.utility.prepareMacro(macro_to_write)
                    data = re.sub('#define %s' % (dict_key), macro_to_write, data, 1)

                    # ----------------------------------------------------------------#



            macro_file = open(self.macro_file_name,'w')
            macro_file.write(data)
            macro_file.close()



