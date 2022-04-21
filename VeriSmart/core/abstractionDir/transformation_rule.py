# coding=utf-8
# EXIT CODE -5 --> The Transformation is not feasible according to translation schema


from pycparser.c_generator import CGenerator
from transformation import Transformation
from utility import Utility


class TransformationsRule(object):

    def __init__(self, cGen, encoding, bit_size, macro_file_name='macro_plain.h'):

        self.prefix = 'abt'  # this variable is useful when we transform the atomic functions. We want to avoid variables overlapping

        self.cGen = cGen

        self.utility = Utility(encoding, bit_size, macroFileName=macro_file_name)

        self.val_phi = '__cs_{0}_val_phi_{1}'


        # logging.basicConfig(filename="test.log", level=logging.DEBUG)
        self.object_list = {}
        self.rules_counter = {}
        self.valphi_map = {}
        self.indentation_base = self.make_indent(2)
        self.transformations_list = ['identifier', 'plusplus_unaryexp', 'minusminus_unaryexp', 'postfix_plusplus',
                                     'binary_exp_shortcut_or', 'binary_exp_shortcut_and',
                                     'postfix_minusminus', 'postfix_array', 'assignment',
                                     'cond_exp', 'not_castExp', 'sizeof_unaryExp', '~_castExp', '-_castExp',
                                     '+_castExp',
                                     'postfixReference_arrow', 'postfixReference_dot', '*_castExp', '&_castExp',
                                     'if_statement', 'binary_exp_no_shortcut',
                                     'typename_castExp', 'constant', 'generic_assignment', 'func_call', 'expr_list',
                                     'assert_statement',
                                     ]

        for rule in self.transformations_list:
            self.object_list[rule] = []
            self.rules_counter[rule] = 0
            self.valphi_map[rule] = []


    # get the type of a node by parsing a string
    def getType(self, node_info):
        return str(type(node_info)).split('.')[-1].replace('>', ' ').replace("'", '').replace(' ', '')

    # For the following translation rule we can avoid to call the function printMacro() since the output is very short, so well fit into recursive call

    def make_indent(self, level):
        return ' ' * level

    def getTR_Identifier(self, t_type, identifier, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)

    def getTR_plusplus_unaryexp(self, t_type, operand, node, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)

    def getTR_minusminus_unaryexp(self, t_type, operand, node, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)

    def getTR_postfix_plusplus(self, t_type, operand, node, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)


    def getTR_postfix_minusminus(self, t_type, operand, node, original_exp, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)


    def getTR_postfix_array(self, t_type, subscript, postfix_exp, arref, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)


    def getTR_FuncCall(self, t_type, call, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)


    def getTR_generic_assignment(self, t_type, unary_exp, ass_exp, ass_op, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)

    def getTR_assignment(self, t_type, unary_exp, ass_exp, ass_op, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)

    # Here i decide to use the following method as an end-point in order to not change the interface
    def getTR_postfixReference(self, t_type, id, postfix_exp, reference_type, sref, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)

    def getTR_binary_exp_shortcut(self, t_type, binary_exp1, binary_exp2, binary_op, getMacro):

        if binary_op == '||':
            return self.getTR_binary_exp_shortcut_or(t_type, binary_exp1, binary_exp2, getMacro)
        else:
            return self.getTR_binary_exp_shortcut_and(t_type, binary_exp1, binary_exp2, getMacro)

    def getTR_binary_exp_shortcut_or(self, t_type, binary_exp1, binary_exp2, getMacro):

        new_transformation = Transformation('binary_exp_shortcut_or')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('binary_exp_shortcut_or')

        cGen_orignal = CGenerator()
        b_exp1 = cGen_orignal.visit(binary_exp1)
        b_exp2 = cGen_orignal.visit(binary_exp2)

        if t_type == 'TRANSF_READ':
            ###---DECLARATION-START----####

            val_phi = self.val_phi.format(self.prefix, str(self.VAL_PHI))

            val_phi_definition = '_Bool %s=0;\n' % (val_phi)
            self.valphi_map['binary_exp_shortcut_or'].append(val_phi)
            # self.valphi_map['binary_exp_shortcut_or'].insert(0, val_phi)

            declaration = val_phi_definition

            new_transformation.declaration = declaration
            new_transformation.declaration_index_val_phi = self.VAL_PHI

            self.VAL_PHI += 1

            ###---DECLARATION-END----####

            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['binary_exp_shortcut_or'] = obj_list

            if getMacro:
               self.utility.macro_counter +=1
               return 'EXP_%s()' % (self.utility.macro_counter-1)
            else:
               self.utility.local_macro_counter += 1
               return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)



    def getTR_binary_exp_shortcut_and(self, t_type, binary_exp1, binary_exp2, getMacro):


        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)



    def getTR_binary_exp_no_shortcut(self, t_type, binary_exp1, binary_exp2, binary_op, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)

    def getTR_cond_exp(self, t_type, condition, branch_true, branch_false, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)

    def getTR_cond_exp_abt(self, t_type, condition, branch_true, branch_false, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)



    def getTR_if_statement(self, condition, original_exp):

        self.utility.macro_counter += 1
        return 'EXP_%s()' % (self.utility.macro_counter - 1)

    def __getTR_unaryOP_ampersand_castExp(self, t_type, cast_exp, new_transformation, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)

    def getTR_plus_minus_tilde_castExp(self, t_type, cast_exp, unary_op, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)


    def getTR_not_castExp(self, t_type, cast_exp, getMacro):


            if getMacro:
                self.utility.macro_counter += 1
                return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
            else:
                self.utility.local_macro_counter += 1
                return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)


    def getTR_sizeofUnaryexp(self, t_type, unaryExp, original_exp, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)

    def getTR_constant(self, t_type, constant, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)

    def getTR_typename_castExp(self, t_type, typename, castExp, getMacro):
        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)

    def getTR_unaryOP_castExp(self, t_type, cast_exp, unary_op, getMacro):

        if getMacro:
            self.utility.macro_counter += 1
            return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
        else:
            self.utility.local_macro_counter += 1
            return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)

        # Gestire anche gli altri unary_op

    def getTR_assert_call(self):

        self.utility.macro_counter += 1
        return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)



    def getTR_expr_list(self, t_type, n, getMacro):

        self.rules_counter['expr_list'] += 1

        new_transformation = Transformation('expr_list')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('expr_list')

        if t_type == 'TRANSF_READ':

            """
                [( (EXP_1, EXP_2, ... , EXP_N ) , V_R )] ::= 

                            ( [(EXP_1, V_R )], [(EXP_2, V_R )], ... , [(EXP_N, V_R )] )
            """

            expr_list = []

            for expr in n.exprs:
                self.cGen.operationBit = 'TRANSF_READ'
                tr_1 = self.cGen.visit(expr)
                tr_1 = self.utility.beautifyString(tr_1)
                expr_list.append(tr_1)

            body = ' ' + self.indentation_base + '( ' + ', '.join(expr_list) + ' )'
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['expr_list'] = obj_list

            if getMacro:
                self.utility.macro_counter += 1
                return 'DECL_%s()' %(self.utility.macro_counter - 1) + ';\n' + 'EXP_%s()' % (self.utility.macro_counter - 1)
            else:
                self.utility.local_macro_counter += 1
                return 'LOCAL_EXP_%s' % (self.utility.local_macro_counter - 1)


        elif t_type == 'GET_VALUE':

            """
             [( (EXP_1, EXP_2, ... , EXP_N ), V )] ::= ( [( EXP_N )], V )
            """

            tr_1 = ''
            number_of_exprs = len(n.exprs)
            for (item, expr) in enumerate(n.exprs):
                if number_of_exprs - 1 == item:
                    self.cGen.operationBit = 'GET_VALUE'
                    tr_1 = self.cGen.visit(expr)
                    tr_1 = self.utility.beautifyString(tr_1)

            body = tr_1
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['expr_list'] = obj_list

            s = self.lparen + '\n' + body + '\n' + self.rparen
            return self.utility.printMacro(getMacro, s)

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getDeclarations(self):
        declaration = ""

        for tr in self.transformations_list:

            len_lista = len(self.object_list[tr])

            for index in range(0, len_lista):
                item = self.object_list[tr][index]
                declaration += item.declaration

        self.__clearObjList()

        if declaration == '':
            self.utility.counter_declaration += 1
            return ''
        else:
            decl_string = self.utility.declaration_type % self.utility.counter_declaration
            return decl_string

    def __clearObjList(self):
        for tr in self.transformations_list:
            self.object_list[tr] = []

    def getFakedDefinition(self):
        return self.utility.faked_typedef

    def checkItemType(self, item):
        type = ''
        if self.cGen.interest_variables_list.has_key(item):
            type = self.cGen.interest_variables_list.get(item)

        return type

