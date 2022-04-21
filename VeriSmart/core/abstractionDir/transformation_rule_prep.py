# coding=utf-8
# EXIT CODE -5 --> The Transformation is not feasible according to our translation schema
# if *_abt function returns '__PLACEHOLDER__' then we want to determine a run time the type of the expression. In this case we rely on external c file called support_macro.c
# See function dynamicSelection in abstraction


from pycparser.c_generator import CGenerator
from core.abstractionDir.transformation import Transformation
from core.abstractionDir.utility import Utility


class TransformationsRulePrep(object):

    def __init__(self, cGen, encoding, bit_size, macro_file_name='output/macro_plain.h'):

        self.macro_key = []  # this list is going to be used only when we have multiple types, so when we performing the dynamic type selection
        self.prefix = 'abt'  # this variable is useful when we transform the atomic functions. We want to avoid variables overlapping

        #The following two variables help us to implement the static constant propagation
        self.baL_track = 0
        self.baV_track = 0

        self.placeholder = '__PLACEHOLDER__%s'
        self.placeholder_map = {}

        self.placeholder_object = {}

        self.macro_dict = {}

        # This variables is useful to keep track of constant for (V) operation
        self.constant_number = 0
        self.constant_prefix = 'const_%s' % str(self.constant_number)

        # Global variables
        self.global_atomic_exchange = '__cs_atomic_exchange_exp'
        self.baL = '__cs_baL'
        self.baV = '__cs_baV'
        self.ba_assert = '__cs_ba_assert'

        # Local variables

        self.val_phi = '__cs_{0}_val_phi_{1}'
        self.val_ue = '__cs_{0}_val_ue_{1}'
        self.val_idx = '__cs_{0}_val_idx_{1}'
        self.baV_base = '__cs_{0}_baV_base_{1}'
        self.ba_if = '__cs_{0}_ba_if_{1}'
        self.val_rhs = '__cs_{0}_val_rhs_{1}'
        self.baV_rhs = '__cs_{0}_baV_rhs_{1}'
        self.val_exp_1 = '__cs_{0}_val_exp_{1}'
        self.val_exp_2 = '__cs_{0}_val_exp_{1}'
        self.func_val = '__cs_{0}_func_val_{1}'

        self.bav_1 = '__cs_{0}_baV_{1}'
        self.val_then = '__cs_{0}_val_then_{1}'
        self.val_else = '__cs_{0}_val_else_{1}'
        self.val_bexp = '__cs_{0}_val_bexp_{1}'

        self.ba_nondet = '__cs_{0}_ba_nondet_{1}'
        self.nondet1 = '__cs_{0}_nondetbool_{1}'
        self.nondet2 = '__cs_{0}_nondetbool_{1}'
        self.nondet = '__cs_{0}_nondet_{1}'
        self.val_cond = '__cs_{0}_cond_{1}'
        self.bool_nondet = '__cs_{0}_bool_nondet_{1}'
        self.nondetbool = 'nondetbool()'

        #print("-->: ",macro_file_name)
        self.utility = Utility(encoding, bit_size, True, macroFileName=macro_file_name)  # optional bit True since we want to write the file macro_plain.h,
                                                         # default is False
        self.declarations_if = ''
        self.field = 'abstraction'
        self.lparen = '('
        self.rparen = ')'

        #VARIABLES COUNTER

        self.GENERIC_BA = 0
        self.VAL_PHI = 0
        self.GENERIC_VAL = 0
        self.BA_IF = 0
        self.NONDET = 0


        ###############################################


        self.bv_variable = '__cs_bitvector_tmp'
        self.cast_bitvector = '__CPROVER_bitvector[%s]' % bit_size



        self.cGen = cGen

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

        self.types = ['INT', 'CHAR', 'LONG', 'SHORT', 'LONG_LONG']

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

        ###################################

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

        self.rules_counter["identifier"] += 1

        body = self.getTR_Identifier_abt(t_type, identifier, getMacro)

        if '__PLACEHOLDER__' in body:

            if getMacro:
                self.macro_key.append(self.getMacroKey('identifier', 1))
            else:
                self.macro_key.append(self.getMacroKey('identifier', 0))

            self.utility.printCustomMacro(body)

            return self.utility.printMacro(getMacro, body, 'yes')
        else:
            return self.utility.printMacro(getMacro, body)



    def getTR_Identifier_abt(self, t_type, identifier, getMacro):

        new_transformation = Transformation('identifier')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('identifier')

        # logging.debug('method getTR_Identifier is called with bit: %s ' % t_type)

        if t_type == 'TRANSF_READ':

            self.baV_track = None

            body = "%s ( %s = __CPROVER_get_field( &(%s), \"%s\"), (void)0 )" % (self.indentation_base, self.baV, identifier, self.field)

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['identifier'] = obj_list

            return self.lparen + '\n' + body + '\n' + self.rparen



        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_OBJECT':

            """
                [( identifier, V_W / V_O )] ::= ( baL = 0, (void)0 )

            """

            self.baL_track = 0

            body = '%s (void)0 ' % (self.indentation_base)

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['identifier'] = obj_list

            # in this case we put a placeholder to help us during beautification of the strings
            return self.lparen + '\n' + body + '\n' + self.rparen

        elif t_type == 'TRANSF_RW':

            self.baL_track = 0
            self.baV_track = None

            """

            (
                  baL = 0, 
                  baV = getfield(& identifier), (void)0
            )

            """

            body = "%s ( %s = 0),\n" \
                    "%s ( %s = __CPROVER_get_field( &(%s), \"%s\"), (void)0 )" % (
                           self.indentation_base, self.baL,
                           self.indentation_base, self.baV, identifier, self.field
                    )

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['identifier'] = obj_list

            return self.lparen + '\n' + body + '\n' + self.rparen

        elif t_type == 'GET_LVALUE':

            new_transformation.body = identifier
            new_transformation.t_type = t_type
            self.object_list['identifier'].append(new_transformation)

            return '( %s )' % identifier

        elif t_type == 'GET_VALUE':

            body_abt = "%s DECODE( %s )" % (self.indentation_base, identifier)
            body_no_abt = "%s %s" % (self.indentation_base, identifier)

            key = 'identifier_%s' % (
                self.utility.macro_counter) if getMacro else 'identifier_%s' % (
                self.utility.local_macro_counter)

            self.macro_dict[key] = '%s' % ( identifier )

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['identifier'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'identifier': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_plusplus_unaryexp(self, t_type, operand, node, getMacro):

        self.rules_counter["plusplus_unaryexp"] += 1

        if getMacro:
            self.macro_key.append(self.getMacroKey('plusplus_unaryexp', 1))
        else:
            self.macro_key.append(self.getMacroKey('plusplus_unaryexp', 0))

        body_plusplus_unaryexp = self.getTR_plusplus_unaryexp_abt(t_type, operand, node, getMacro)

        if '__PLACEHOLDER__' in body_plusplus_unaryexp:
            self.utility.printCustomMacro(body_plusplus_unaryexp)

            return self.utility.printMacro(getMacro, body_plusplus_unaryexp, 'yes')
        else:
            return self.utility.printMacro(getMacro, body_plusplus_unaryexp)

    def getTR_plusplus_unaryexp_abt(self, t_type, operand, node, getMacro):

        new_transformation = Transformation('plusplus_unaryexp')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('plusplus_unaryexp')

        # logging.debug('method getTR_plusplus_unaryexp is called --> %s\n' % t_type)

        if getMacro:
            key = 'plusplus_unaryexp_%s' % self.utility.macro_counter
        else:
            key = 'plusplus_unaryexp_%s' % self.utility.local_macro_counter

        max_list = []
        encoding_list = []

        if t_type == 'TRANSF_READ':

            ###---BODY-START----####

            self.cGen.operationBit = 'TRANSF_RW'
            tr_1 = self.cGen.visit(node)

            flag_baL = self.baL_track

            flag_baV = self.baV_track

            self.cGen.operationBit = 'GET_VALUE'
            tr_3 = self.cGen.visit(node)

            self.cGen.operationBit = 'GET_LVALUE'
            tr_2 = self.cGen.visit(node)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)
            tr_3 = self.utility.beautifyString(tr_3)

            self.macro_dict[key] = operand

            for type in self.types:
                max_list.append("MAX_%s( ((%s)%s)) " % (type, self.cast_bitvector, tr_3))
                encoding_list.append(
                    'ENCODE_%s( ( ((%s)%s) + ((%s)1) ) )' % (type, self.cast_bitvector, tr_3, self.cast_bitvector))

            if flag_baV:

                if flag_baL:

                    # abt case
                    body_abt = '%s %s,\n' \
                               '%s (void) 0\n' \
                               % (self.indentation_base, tr_1,
                                  self.indentation_base
                                  )

                    body_no_abt = body_abt

                    self.baV_track = 1

                elif (flag_baL == 0):

                    body_abt = '%s %s,\n' \
                               '%s ( __CPROVER_set_field( &(%s), "%s", 1 ) )\n' \
                               '%s (void) 0\n' \
                               % (self.indentation_base, tr_1,
                                  self.indentation_base, tr_2, self.field,
                                  self.indentation_base
                                  )

                    body_no_abt = '%s %s,\n' \
                                  '%s (void) 0\n' \
                                  % (self.indentation_base, tr_1,
                                     self.indentation_base
                                     )

                    self.baV_track = 1


                else:
                    # abt case
                    body_abt = '%s %s,\n' \
                               '%s ( \n' \
                               '%s ( %s || __CPROVER_set_field( &(%s), "%s", 1 ) )\n' \
                               '%s (void) 0\n' \
                               '%s )\n' \
                               % (self.indentation_base, tr_1,
                                  self.indentation_base * 4,
                                  self.indentation_base * 8, self.baL, tr_2, self.field,
                                  self.indentation_base * 6,
                                  self.indentation_base * 4,
                                  )

                    self.baV_track = 1
                    self.baL_track = None

                    # no abt case
                    body_no_abt = "%s %s,\n" \
                                  "%s (void)0" \
                                  % (
                                      self.indentation_base, tr_1,
                                      self.indentation_base
                                  )


            elif flag_baV is None:

                body_abt = '%s %s,\n' \
                           '%s ( \n' \
                           '%s (  0\n' \
                           '%s    || %s \n' \
                           '%s    || ( %s )\n' \
                           '%s )\n' \
                           '%s ? ( (\n' \
                           '%s    %s\n' \
                           '%s || __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                           '%s ),\n' \
                           '%s %s = 1,\n' \
                           '%s (void) 0\n' \
                           '%s )\n' \
                           '%s : (  ( %s = %s ), (void)0 ) \n' \
                           '%s ),\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_1,
                              self.indentation_base,
                              self.indentation_base * 4,
                              self.indentation_base * 4, self.baV,
                              self.indentation_base * 4, '__place__',
                              self.indentation_base * 4,
                              self.indentation_base * 4,
                              self.indentation_base * 8, self.baL,
                              self.indentation_base * 8, tr_2, self.field,
                              self.indentation_base * 6,
                              self.indentation_base * 6, self.baV,
                              self.indentation_base * 6,
                              self.indentation_base * 5,
                              self.indentation_base * 4, tr_2, '__encoding__',
                              self.indentation_base,
                              self.indentation_base
                              )

                # not abstractable
                """
                    (
                        [( unary_exp , V_RW )],

                        ( baV || ( [( unary_exp, E )] ++, (void)0 ) ),

                        (void)0    
                    )
                """
                body_no_abt = "%s %s,\n" \
                              "%s ( %s || ( ++%s ), (void)0 ),\n" \
                              "%s (void)0" \
                              % (
                                  self.indentation_base, tr_1,
                                  self.indentation_base, self.baV, tr_2,
                                  self.indentation_base
                              )

                self.baV_track = None
                self.baL_track = flag_baL

            else:

                # abt case
                body_abt = '%s %s,\n' \
                           '%s ( \n' \
                           '%s ( %s ) \n' \
                           '%s ? ( (\n' \
                           '%s    %s\n' \
                           '%s || __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                           '%s ),\n' \
                           '%s ( %s = 1 ),\n' \
                           '%s (void) 0\n' \
                           '%s )\n' \
                           '%s : (  ( %s = %s ), (void)0 ) \n' \
                           '%s ),\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_1,
                              self.indentation_base,
                              self.indentation_base * 4, '__place__',
                              self.indentation_base * 4,
                              self.indentation_base * 8, self.baL,
                              self.indentation_base * 8, tr_2, self.field,
                              self.indentation_base * 6,
                              self.indentation_base * 6, self.baV,
                              self.indentation_base * 6,
                              self.indentation_base * 5,
                              self.indentation_base * 4, tr_2, '__encoding__',
                              self.indentation_base,
                              self.indentation_base
                              )

                self.baV_track = 0

                # no abt case
                body_no_abt = "%s %s,\n" \
                              "%s ( ++%s , (void)0 ) ,\n" \
                              "%s (void)0" \
                              % (
                                  self.indentation_base, tr_1,
                                  self.indentation_base, tr_2,
                                  self.indentation_base
                              )

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt, 'max_list': max_list, 'encoding': encoding_list}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['plusplus_unaryexp'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'plusplus_unaryexp': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

            ###---BODY-END----####

        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE' or t_type == 'TRANSF_RW' or t_type == 'GET_OBJECT':
            self.utility.raiseException('This operation is not allowed!!')


        elif t_type == 'GET_VALUE':

            self.macro_dict[key] = operand

            """
            #abstractable

                  [( ++unary_exp, V )] :: = DECODE( [( unary_exp, E )] )

            #no_abstractable

                  [( ++unary_exp, V )] :: = [( unary_exp, V )]  

            """

            self.cGen.operationBit = 'GET_LVALUE'
            tr_1 = self.cGen.visit(node)
            tr_1 = self.utility.beautifyString(tr_1)

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(node)
            tr_2 = self.utility.beautifyString(tr_2)

            body_abt = '%s DECODE( %s )' % (self.indentation_base, tr_1)
            body_no_abt = '%s %s' % (self.indentation_base, tr_2)

            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen
            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['plusplus_unaryexp'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'plusplus_unaryexp': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_minusminus_unaryexp(self, t_type, operand, node, getMacro):

        self.rules_counter["minusminus_unaryexp"] += 1

        if getMacro:
            self.macro_key.append(self.getMacroKey('minusminus_unaryexp', 1))
        else:
            self.macro_key.append(self.getMacroKey('minusminus_unaryexp', 0))

        body_minusminus_unaryexp_abt = self.getTR_minusminus_unaryexp_abt(t_type, operand, node, getMacro)

        if '__PLACEHOLDER__' in body_minusminus_unaryexp_abt:
            self.utility.printCustomMacro(body_minusminus_unaryexp_abt)
            return self.utility.printMacro(getMacro, body_minusminus_unaryexp_abt, 'yes')
        else:
            return self.utility.printMacro(getMacro, body_minusminus_unaryexp_abt)

    def getTR_minusminus_unaryexp_abt(self, t_type, operand, node, getMacro):

        new_transformation = Transformation('minusminus_unaryexp')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('minusminus_unaryexp')

        if getMacro:
            key = 'minusminus_unaryexp_%s' % self.utility.macro_counter
        else:
            key = 'minusminus_unaryexp_%s' % self.utility.local_macro_counter

        min_list = []
        encoding_list = []

        if t_type == 'TRANSF_READ':

            ###---BODY-START----####

            self.cGen.operationBit = 'TRANSF_RW'
            tr_1 = self.cGen.visit(node)

            flag_baL = self.baL_track

            flag_baV = self.baV_track

            self.cGen.operationBit = 'GET_VALUE'
            tr_3 = self.cGen.visit(node)

            self.cGen.operationBit = 'GET_LVALUE'
            tr_2 = self.cGen.visit(node)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)
            tr_3 = self.utility.beautifyString(tr_3)

            self.macro_dict[key] = operand

            for type in self.types:
                min_list.append("MIN_%s( ((%s)(%s)) ) " % (type, self.cast_bitvector, tr_3))
                encoding_list.append(
                    'ENCODE_%s( ( ((%s)%s) - ((%s)1) ) )' % (type, self.cast_bitvector, tr_3, self.cast_bitvector))

            if flag_baV:

                if flag_baL:

                    # abt case
                    body_abt = '%s %s,\n' \
                               '%s (void) 0\n' \
                               % (self.indentation_base, tr_1,
                                  self.indentation_base
                                  )

                    body_no_abt = body_abt

                    self.baV_track = 1
                    self.baL_track = 1


                elif (flag_baL == 0):

                    body_abt = '%s %s,\n' \
                               '%s ( __CPROVER_set_field( &(%s), "%s", 1 ) )\n' \
                               '%s (void) 0\n' \
                               % (self.indentation_base, tr_1,
                                  self.indentation_base, tr_2, self.field,
                                  self.indentation_base
                                  )

                    body_no_abt = '%s %s,\n' \
                                  '%s (void) 0\n' \
                                  % (self.indentation_base, tr_1,
                                     self.indentation_base
                                     )

                    self.baV_track = 1
                    self.baL_track = 0


                else:
                    # abt case
                    body_abt = '%s %s,\n' \
                               '%s ( \n' \
                               '%s ( %s || __CPROVER_set_field( &(%s), "%s", 1 ) )\n' \
                               '%s (void) 0\n' \
                               '%s )\n' \
                               % (self.indentation_base, tr_1,
                                  self.indentation_base * 4,
                                  self.indentation_base * 8, self.baL, tr_2, self.field,
                                  self.indentation_base * 6,
                                  self.indentation_base * 4,
                                  )

                    # no abt case
                    body_no_abt = "%s %s,\n" \
                                  "%s (void)0" \
                                  % (
                                      self.indentation_base, tr_1,
                                      self.indentation_base
                                  )

                    self.baV_track = 1
                    self.baL_track = None


            elif flag_baV is None:

                body_abt = '%s %s,\n' \
                           '%s ( \n' \
                           '%s (  0\n' \
                           '%s    || %s \n' \
                           '%s    || ( %s )\n' \
                           '%s )\n' \
                           '%s ? ( (\n' \
                           '%s    %s\n' \
                           '%s || __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                           '%s ),\n' \
                           '%s %s = 1,\n' \
                           '%s (void) 0\n' \
                           '%s )\n' \
                           '%s : (  ( %s = %s ), (void)0 ) \n' \
                           '%s ),\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_1,
                              self.indentation_base,
                              self.indentation_base * 4,
                              self.indentation_base * 4, self.baV,
                              self.indentation_base * 4, '__place__',
                              self.indentation_base * 4,
                              self.indentation_base * 4,
                              self.indentation_base * 8, self.baL,
                              self.indentation_base * 8, tr_2, self.field,
                              self.indentation_base * 6,
                              self.indentation_base * 6, self.baV,
                              self.indentation_base * 6,
                              self.indentation_base * 5,
                              self.indentation_base * 4, tr_2, '__encoding__',
                              self.indentation_base,
                              self.indentation_base
                              )

                # not abstractable
                """
                    (
                        [( unary_exp , V_RW )],

                        ( baV || ( [( unary_exp, E )] --, (void)0 ) ),

                        (void)0    
                    )
                """
                body_no_abt = "%s %s,\n" \
                              "%s ( %s || ( --%s ), (void)0 ),\n" \
                              "%s (void)0" \
                              % (
                                  self.indentation_base, tr_1,
                                  self.indentation_base, self.baV, tr_2,
                                  self.indentation_base
                              )
                self.baV_track = None
                self.baL_track = flag_baL

            else:

                # abt case
                body_abt = '%s %s,\n' \
                           '%s ( \n' \
                           '%s ( %s ) \n' \
                           '%s ? ( (\n' \
                           '%s    %s\n' \
                           '%s || __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                           '%s ),\n' \
                           '%s ( %s = 1 ),\n' \
                           '%s (void) 0\n' \
                           '%s )\n' \
                           '%s : (  ( %s = %s ), (void)0 ) \n' \
                           '%s ),\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_1,
                              self.indentation_base,
                              self.indentation_base * 4, '__place__',
                              self.indentation_base * 4,
                              self.indentation_base * 8, self.baL,
                              self.indentation_base * 8, tr_2, self.field,
                              self.indentation_base * 6,
                              self.indentation_base * 6, self.baV,
                              self.indentation_base * 6,
                              self.indentation_base * 5,
                              self.indentation_base * 4, tr_2, '__encoding__',
                              self.indentation_base,
                              self.indentation_base
                              )

                self.baV_track = None

                # no abt case
                body_no_abt = "%s %s,\n" \
                              "%s ( --%s , (void)0 ) ,\n" \
                              "%s (void)0" \
                              % (
                                  self.indentation_base, tr_1,
                                  self.indentation_base, tr_2,
                                  self.indentation_base
                              )

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt, 'min_list': min_list, 'encoding': encoding_list}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['minusminus_unaryexp'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'minusminus_unaryexp': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

            ###---BODY-END----####


        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE' or t_type == 'TRANSF_RW' or t_type == 'GET_OBJECT':
            self.utility.raiseException('This operation is not allowed!!')


        elif (t_type == 'GET_VALUE'):

            # key = 'minusminus_unaryexp_value_%s' % self.utility.macro_counter

            self.macro_dict[key] = operand

            """
            abstractable

            [( --unary_exp, V )] :: = DECODE( [( unary_exp, E )] )

            not abstractable

            [( --unary_exp, V )] :: = [( unary_exp, V )]  

            """

            self.cGen.operationBit = 'GET_LVALUE'
            tr_1 = self.cGen.visit(node)
            tr_1 = self.utility.beautifyString(tr_1)

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(node)
            tr_2 = self.utility.beautifyString(tr_2)

            body_abt = '%s DECODE( %s )' % (self.indentation_base, tr_1)
            body_no_abt = '%s %s' % (self.indentation_base, tr_2)

            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen
            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen

            body = {'abt:': body_abt, 'no_abt': body_no_abt}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['minusminus_unaryexp'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'minusminus_unaryexp': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_postfix_plusplus(self, t_type, operand, node, getMacro):

        self.rules_counter["postfix_plusplus"] += 1

        if getMacro:
            self.macro_key.append(self.getMacroKey('postfix_plusplus', 1))
        else:
            self.macro_key.append(self.getMacroKey('postfix_plusplus', 0))

        body_postfix_plusplus_abt = self.getTR_postfix_plusplus_abt(t_type, operand, node, getMacro)

        if '__PLACEHOLDER__' in body_postfix_plusplus_abt:
            self.utility.printCustomMacro(body_postfix_plusplus_abt)
            return self.utility.printMacro(getMacro, body_postfix_plusplus_abt, 'yes')
        else:
            return self.utility.printMacro(getMacro, body_postfix_plusplus_abt)

    def getTR_postfix_plusplus_abt(self, t_type, operand, n, getMacro):

        new_transformation = Transformation('postfix_plusplus')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('postfix_plusplus')

        # logging.debug('method getTR_postfix_plusplus is called with bit: %s' % t_type)

        if getMacro:
            key = 'postfix_plusplus_%s' % self.utility.macro_counter
        else:
            key = 'postfix_plusplus_%s' % self.utility.local_macro_counter

        max_list = []
        encoding_list = []

        if t_type == 'TRANSF_READ':

            ###---BODY-START----####

            self.cGen.operationBit = 'TRANSF_RW'
            tr_1 = self.cGen.visit(n)

            flag_baL = self.baL_track

            flag_baV = self.baV_track

            self.cGen.operationBit = 'GET_VALUE'
            tr_3 = self.cGen.visit(n)

            self.cGen.operationBit = 'GET_LVALUE'
            tr_2 = self.cGen.visit(n)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)
            tr_3 = self.utility.beautifyString(tr_3)

            self.macro_dict[key] = operand

            for type in self.types:
                max_list.append("MAX_%s( ((%s)%s) )" % (type,self.cast_bitvector ,tr_3))
                encoding_list.append(
                    'ENCODE_%s( ( ((%s)%s) + ((%s)1) ) )' % (type, self.cast_bitvector, tr_3, self.cast_bitvector))

            if flag_baV:

                if flag_baL:

                    # abt case
                    body_abt = '%s %s,\n' \
                               '%s (void) 0\n' \
                               % (self.indentation_base, tr_1,
                                  self.indentation_base
                                  )

                    body_no_abt = body_abt

                    self.baV_track = 1
                    self.baL_track = 1


                elif (flag_baL == 0):

                    body_abt = '%s %s,\n' \
                               '%s ( __CPROVER_set_field( &(%s), "%s", 1 ) )\n' \
                               '%s (void) 0\n' \
                               % (self.indentation_base, tr_1,
                                  self.indentation_base, tr_2, self.field,
                                  self.indentation_base
                                  )

                    body_no_abt = '%s %s,\n' \
                                  '%s (void) 0\n' \
                                  % (self.indentation_base, tr_1,
                                     self.indentation_base
                                     )

                    self.baV_track = 1
                    self.baL_track = 0


                else:
                    # abt case
                    body_abt = '%s %s,\n' \
                               '%s ( \n' \
                               '%s ( %s || __CPROVER_set_field( &(%s), "%s", 1 ) )\n' \
                               '%s (void) 0\n' \
                               '%s )\n' \
                               % (self.indentation_base, tr_1,
                                  self.indentation_base * 4,
                                  self.indentation_base * 8, self.baL, tr_2, self.field,
                                  self.indentation_base * 6,
                                  self.indentation_base * 4,
                                  )

                    # no abt case
                    body_no_abt = "%s %s,\n" \
                                  "%s (void)0" \
                                  % (
                                      self.indentation_base, tr_1,
                                      self.indentation_base
                                  )

                    self.baV_track = 1
                    self.baL_track = None


            elif flag_baV is None:

                body_abt = '%s %s,\n' \
                           '%s ( \n' \
                           '%s (  \n' \
                           '%s       %s \n' \
                           '%s    || ( %s )\n' \
                           '%s )\n' \
                           '%s ? ( (\n' \
                           '%s    %s\n' \
                           '%s || __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                           '%s ),\n' \
                           '%s %s = 1,\n' \
                           '%s (void) 0\n' \
                           '%s )\n' \
                           '%s : (  ( %s = %s ), (void)0 ) \n' \
                           '%s ),\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_1,
                              self.indentation_base,
                              self.indentation_base * 4,
                              self.indentation_base * 4, self.baV,
                              self.indentation_base * 4, '__place__',
                              self.indentation_base * 4,
                              self.indentation_base * 4,
                              self.indentation_base * 8, self.baL,
                              self.indentation_base * 8, tr_2, self.field,
                              self.indentation_base * 6,
                              self.indentation_base * 6, self.baV,
                              self.indentation_base * 6,
                              self.indentation_base * 5,
                              self.indentation_base * 4, tr_2, '__encoding__',
                              self.indentation_base,
                              self.indentation_base
                              )

                # not abstractable
                """
                    (
                        [( postfix_exp , V_RW )],

                        ( baV || ( [( postfix_exp, E )] ++, (void)0 ) ),

                        (void)0    
                    )
                """
                body_no_abt = "%s %s,\n" \
                              "%s ( %s || ( %s++ ), (void)0 ),\n" \
                              "%s (void)0" \
                              % (
                                  self.indentation_base, tr_1,
                                  self.indentation_base, self.baV, tr_2,
                                  self.indentation_base
                              )

                self.baV_track = None
                self.baL_track = flag_baL

            else:
                # abt case
                body_abt = '%s %s,\n' \
                           '%s ( \n' \
                           '%s ( %s ) \n' \
                           '%s ? ( (\n' \
                           '%s    %s\n' \
                           '%s || __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                           '%s ),\n' \
                           '%s ( %s = 1 ),\n' \
                           '%s (void) 0\n' \
                           '%s )\n' \
                           '%s : (  ( %s = %s ), (void)0 ) \n' \
                           '%s ),\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_1,
                              self.indentation_base,
                              self.indentation_base * 4, '__place__',
                              self.indentation_base * 4,
                              self.indentation_base * 8, flag_baL,
                              self.indentation_base * 8, tr_2, self.field,
                              self.indentation_base * 6,
                              self.indentation_base * 6, self.baV,
                              self.indentation_base * 6,
                              self.indentation_base * 5,
                              self.indentation_base * 4, tr_2, '__encoding__',
                              self.indentation_base,
                              self.indentation_base
                              )

                self.baV_track = None

                # no abt case
                body_no_abt = "%s %s,\n" \
                              "%s ( %s++ , (void)0 ) ,\n" \
                              "%s (void)0" \
                              % (
                                  self.indentation_base, tr_1,
                                  self.indentation_base, tr_2,
                                  self.indentation_base
                              )

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt, 'max_list': max_list, 'encoding': encoding_list}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfix_plusplus'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'postfix_plusplus': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

            ###---BODY-END----####


        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE' or t_type == 'TRANSF_RW' or t_type == 'GET_OBJECT':
            self.utility.raiseException('This operation is not allowed!!')


        elif (t_type == 'GET_VALUE'):

            self.macro_dict[key] = operand

            """
            abstractable

            [(postfix_exp + +, V)]:: = DECODE([(postfix_exp, E)]) - 1 )

            not abstractable

            [( postfix_exp++, V )] :: = ( [( postfix_exp, V )] - 1 )

            """

            self.cGen.operationBit = 'GET_LVALUE'
            tr_1 = self.cGen.visit(n)
            tr_1 = self.utility.beautifyString(tr_1)

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(n)
            tr_2 = self.utility.beautifyString(tr_2)

            body_abt = '%s DECODE( %s - 1)' % (
            self.indentation_base, tr_1)
            body_no_abt = '%s (%s - 1) ' % (self.indentation_base, tr_2)

            # body_abt = '%s DECODE( (%s) -1 )' % (self.indentation_base, tr_1)
            # body_no_abt = '%s (%s) -1' % (self.indentation_base, tr_2)

            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen
            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen

            body = {'abt:': body_abt, 'no_abt': body_no_abt}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfix_plusplus'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'postfix_plusplus': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_postfix_minusminus(self, t_type, operand, node, original_exp, getMacro):

        self.rules_counter["postfix_minusminus"] += 1

        if getMacro:
            self.macro_key.append(self.getMacroKey('postfix_minusminus', 1))
        else:
            self.macro_key.append(self.getMacroKey('postfix_minusminus', 0))

        body_postfix_minusminus_abt = self.getTR_postfix_minusminus_abt(t_type, operand, node, getMacro)

        if '__PLACEHOLDER__' in body_postfix_minusminus_abt:
            self.utility.printCustomMacro(body_postfix_minusminus_abt)
            return self.utility.printMacro(getMacro, body_postfix_minusminus_abt, 'yes')
        else:
            return self.utility.printMacro(getMacro, body_postfix_minusminus_abt)

    def getTR_postfix_minusminus_abt(self, t_type, operand, n, getMacro):

        new_transformation = Transformation('postfix_minusminus')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('postfix_minusminus')

        if getMacro:
            key = 'postfix_minusminus_%s' % self.utility.macro_counter
        else:
            key = 'postfix_minusminus_%s' % self.utility.local_macro_counter

        min_list = []
        encoding_list = []

        if t_type == 'TRANSF_READ':

            ###---BODY-START----####

            self.cGen.operationBit = 'TRANSF_RW'
            tr_1 = self.cGen.visit(n)

            flag_baL = self.baL_track

            flag_baV = self.baV_track

            self.cGen.operationBit = 'GET_VALUE'
            tr_3 = self.cGen.visit(n)

            self.cGen.operationBit = 'GET_LVALUE'
            tr_2 = self.cGen.visit(n)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)
            tr_3 = self.utility.beautifyString(tr_3)

            self.macro_dict[key] = operand

            for type in self.types:
                min_list.append("MIN_%s( ((%s)%s) ) " % (type, self.cast_bitvector, tr_3))
                encoding_list.append(
                    'ENCODE_%s( ( ((%s)%s) - ((%s)1) ) )' % (type, self.cast_bitvector, tr_3, self.cast_bitvector))

            if flag_baV:

                if flag_baL:

                    # abt case
                    body_abt = '%s %s,\n' \
                               '%s (void) 0\n' \
                               % (self.indentation_base, tr_1,
                                  self.indentation_base
                                  )

                    body_no_abt = body_abt

                    self.baV_track = 1


                elif (flag_baL == 0):

                    body_abt = '%s %s,\n' \
                               '%s ( __CPROVER_set_field( &(%s), "%s", 1 ) )\n' \
                               '%s (void) 0\n' \
                               % (self.indentation_base, tr_1,
                                  self.indentation_base, tr_2, self.field,
                                  self.indentation_base
                                  )

                    body_no_abt = '%s %s,\n' \
                                  '%s (void) 0\n' \
                                  % (self.indentation_base, tr_1,
                                     self.indentation_base
                                     )

                    self.baV_track = 1



                else:
                    # abt case
                    body_abt = '%s %s,\n' \
                               '%s ( \n' \
                               '%s ( %s || __CPROVER_set_field( &(%s), "%s", 1 ) )\n' \
                               '%s (void) 0\n' \
                               '%s )\n' \
                               % (self.indentation_base, tr_1,
                                  self.indentation_base * 4,
                                  self.indentation_base * 8, self.baL, tr_2, self.field,
                                  self.indentation_base * 6,
                                  self.indentation_base * 4,
                                  )

                    # no abt case
                    body_no_abt = "%s %s,\n" \
                                  "%s (void)0" \
                                  % (
                                      self.indentation_base, tr_1,
                                      self.indentation_base
                                  )

                    self.baV_track = 1
                    self.baL_track = None


            elif flag_baV is None:

                body_abt = '%s %s,\n' \
                           '%s ( \n' \
                           '%s (  0\n' \
                           '%s    || %s \n' \
                           '%s    || ( %s )\n' \
                           '%s )\n' \
                           '%s ? ( (\n' \
                           '%s    %s\n' \
                           '%s || __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                           '%s ),\n' \
                           '%s %s = 1,\n' \
                           '%s (void) 0\n' \
                           '%s )\n' \
                           '%s : (  ( %s = %s ), (void)0 ) \n' \
                           '%s ),\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_1,
                              self.indentation_base,
                              self.indentation_base * 4,
                              self.indentation_base * 4, self.baV,
                              self.indentation_base * 4, '__place__',
                              self.indentation_base * 4,
                              self.indentation_base * 4,
                              self.indentation_base * 8, self.baL,
                              self.indentation_base * 8, tr_2, self.field,
                              self.indentation_base * 6,
                              self.indentation_base * 6, self.baV,
                              self.indentation_base * 6,
                              self.indentation_base * 5,
                              self.indentation_base * 4, tr_2, '__encoding__',
                              self.indentation_base,
                              self.indentation_base
                              )

                # not abstractable
                """
                    (
                        [( postfix_exp , V_RW )],

                        ( baV || ( [( postfix_exp, E )] --, (void)0 ) ),

                        (void)0    
                    )
                """
                body_no_abt = "%s %s,\n" \
                              "%s ( %s || ( %s-- ), (void)0 ),\n" \
                              "%s (void)0" \
                              % (
                                  self.indentation_base, tr_1,
                                  self.indentation_base, self.baV, tr_2,
                                  self.indentation_base
                              )

                self.baV_track = None
                self.baL_track = flag_baL

            else:

                # abt case
                body_abt = '%s %s,\n' \
                           '%s ( \n' \
                           '%s ( %s ) \n' \
                           '%s ? ( (\n' \
                           '%s    %s\n' \
                           '%s || __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                           '%s ),\n' \
                           '%s ( %s = 1 ),\n' \
                           '%s (void) 0\n' \
                           '%s )\n' \
                           '%s : (  ( %s = %s ), (void)0 ) \n' \
                           '%s ),\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_1,
                              self.indentation_base,
                              self.indentation_base * 4, '__place__',
                              self.indentation_base * 4,
                              self.indentation_base * 8, self.baL_track,
                              self.indentation_base * 8, tr_2, self.field,
                              self.indentation_base * 6,
                              self.indentation_base * 6, self.baV,
                              self.indentation_base * 6,
                              self.indentation_base * 5,
                              self.indentation_base * 4, tr_2, '__encoding__',
                              self.indentation_base,
                              self.indentation_base
                              )

                self.baV_track = None

                # no abt case
                body_no_abt = "%s %s,\n" \
                              "%s ( %s-- , (void)0 ) ,\n" \
                              "%s (void)0" \
                              % (
                                  self.indentation_base, tr_1,
                                  self.indentation_base, tr_2,
                                  self.indentation_base
                              )

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt, 'min_list': min_list, 'encoding': encoding_list}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfix_minusminus'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'postfix_minusminus': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

            ###---BODY-END----####


        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE' or t_type == 'TRANSF_RW' or t_type == 'GET_OBJECT':
            self.utility.raiseException('This operation is not allowed!!')


        elif (t_type == 'GET_VALUE'):

            # key = 'postfix_minusminus_value_%s' % self.utility.macro_counter

            self.macro_dict[key] = operand

            """
            abstractable

            [(postfix_exp --, V)]:: = DECODE([(postfix_exp, E)]) + 1 )

            not abstractable

            [( postfix_exp--, V )] :: = ( [( postfix_exp, V )] + 1 )

            """

            self.cGen.operationBit = 'GET_LVALUE'
            tr_1 = self.cGen.visit(n)
            tr_1 = self.utility.beautifyString(tr_1)

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(n)
            tr_2 = self.utility.beautifyString(tr_2)

            body_abt = '%s DECODE( (%s) + 1)  )' % ( self.indentation_base, tr_1)
            body_no_abt = '%s %s + 1' % (self.indentation_base, tr_2)

            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen
            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen

            body = {'abt:': body_abt, 'no_abt': body_no_abt}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfix_minusminus'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'postfix_minusminus': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_postfix_array(self, t_type, subscript, postfix_exp, arref, getMacro):

        self.rules_counter["postfix_array"] += 1

        body_postfix_array_abt = self.getTR_postfix_array_abt(t_type, subscript, postfix_exp, arref, getMacro)

        if '__PLACEHOLDER__' in body_postfix_array_abt:

            if getMacro:
                self.macro_key.append(self.getMacroKey('postfix_array', 1))
            else:
                self.macro_key.append(self.getMacroKey('postfix_array', 0))

            self.utility.printCustomMacro(body_postfix_array_abt) if getMacro else self.utility.printCustomMacro(
                body_postfix_array_abt)
            return self.utility.printMacro(getMacro, body_postfix_array_abt, 'yes')
        else:
            return self.utility.printMacro(getMacro, body_postfix_array_abt)

    def getTR_postfix_array_abt(self, t_type, subscript, postfix_exp, arref, getMacro):

        new_transformation = Transformation('postfix_array')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('postfix_array')

        if t_type == 'TRANSF_READ':

            self.cGen.operationBit = 'TRANSF_READ'
            tr_2 = self.cGen.visit(postfix_exp)

            flag_base_baV = self.baV_track

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(subscript)

            flag_subscript_baV = self.baV_track

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)

            ###---BODY-START----####

            """
                    (


                       [( postfix_exp, V_R )], 

                       (
                         true
                         &&   (     baV 
                                 || (  [( exp, V_R )],  
                                       0
                                     ) 
                              )     
                         &&  ( [( exp, V_R )] , baV = 1 )
                       ),

                       (void) 0
                    )   


            """
            if flag_base_baV:

                body = '%s %s,\n' \
                       '%s %s,\n' \
                       '%s (void) 0' \
                       % (
                           self.indentation_base, tr_2,
                           self.indentation_base, tr_1,
                           self.indentation_base
                       )
                self.baV_track = 1


            # baV cannot be determined
            elif flag_base_baV is None:

                body = '%s %s,\n' \
                       '%s (\n' \
                       '%s      ( %s || ( %s, 0) )\n' \
                       '%s ) && ( %s, ( %s = 1 ) ), \n' \
                       '%s (void) 0' \
                       % (
                           self.indentation_base, tr_2,
                           self.indentation_base,
                           self.indentation_base * 2, self.baV, tr_1,
                           self.indentation_base, tr_1, self.baV,
                           self.indentation_base
                       )

                self.baV_track = None

            else:

                """

                        [( postfix_exp, V_R )], 

                       (
                         true
                         &&   (     baV 
                                 || (  [( exp, V_R )],  
                                       0
                                     ) 
                              )     
                         &&  ( [( exp, V_R )] , baV = 1 )
                       ),

                       (void) 0
                    )   


                """

                if flag_subscript_baV:

                    body = '%s %s,\n' \
                           '%s %s,\n' \
                           '%s (void) 0' \
                           % (
                               self.indentation_base, tr_2,
                               self.indentation_base, tr_1,
                               self.indentation_base
                           )

                    self.baV_track = 1

                elif (flag_subscript_baV == 0):

                    body = '%s %s,\n' \
                           '%s %s,\n' \
                           '%s (void) 0' \
                           % (
                               self.indentation_base, tr_2,
                               self.indentation_base, tr_1,
                               self.indentation_base
                           )

                    self.baV_track = 0

                else:

                    body = '%s %s,\n' \
                           '%s %s,\n' \
                           '%s (void) 0' \
                           % (
                               self.indentation_base, tr_2,
                               self.indentation_base, tr_1,
                               self.indentation_base
                           )

                    self.baV_track = None

            ###---BODY-END----####

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfix_array'] = obj_list

            return self.lparen + '\n' + body + '\n' + self.rparen


        elif t_type == 'TRANSF_WRITE':

            self.cGen.operationBit = 'TRANSF_READ'
            tr_2 = self.cGen.visit(postfix_exp)

            flag_base_baV = self.baV_track

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(subscript)

            flag_subscript_baV = self.baV_track

            self.cGen.operationBit = 'GET_LVALUE'
            tr_3 = self.cGen.visit(postfix_exp)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)
            tr_3 = self.utility.beautifyString(tr_3)

            ###---BODY-START----####

            """

           (

               [( postfix_exp, V_R )], 

               (
                 true
                 &&   (     baV 
                         || (  [( exp, V_R )],  
                               ( (baL=baV) && (  set_field( [(postfix_exp, E)] , 1 ), 0 ) )
                            )
                      )     
                 &&  ( [( exp, V_R )], ( baL = 1 )  ) 
               ),

               (void) 0
            )

            """

            if flag_base_baV:

                body = '%s %s,\n' \
                       '%s %s,\n' \
                       '%s (void) 0' \
                       % (
                           self.indentation_base, tr_2,
                           self.indentation_base, tr_1,
                           self.indentation_base
                       )

                self.baL_track = 1



            elif flag_base_baV is None:

                ###---BODY-START----####

                body = '%s %s,\n' \
                       '%s (\n' \
                       '%s (\n' \
                       '%s    %s\n' \
                       '%s || (\n' \
                       '%s %s,\n' \
                       '%s ( ( %s = %s  ) && ( __CPROVER_set_field( %s, "%s", 1 ), 0 ) )\n' \
                       '%s  )\n' \
                       '%s  )\n' \
                       '%s && ( %s , 0 )\n' \
                       '%s ),\n' \
                       '%s (void) 0' \
                       % (
                           self.indentation_base, tr_2,
                           self.indentation_base,
                           self.indentation_base * 4,
                           self.indentation_base * 6, self.baV,
                           self.indentation_base * 6,
                           self.indentation_base * 10, tr_1,
                           self.indentation_base * 10, self.baL, self.baV, tr_3, self.field,
                           self.indentation_base * 7,
                           self.indentation_base * 4,
                           self.indentation_base * 4, tr_1,
                           self.indentation_base,
                           self.indentation_base
                       )

                self.baL_track = None
                self.baV_track = None


            else:

                if flag_subscript_baV is None:

                    body = '%s %s,\n' \
                           '%s (\n' \
                           '%s %s,\n' \
                           '%s ( ( %s = %s  ) && ( __CPROVER_set_field( %s, "%s", 1 ), 0 ) )\n' \
                           '%s ),\n' \
                           '%s (void) 0' \
                           % (
                               self.indentation_base, tr_2,
                               self.indentation_base * 6,
                               self.indentation_base * 10, tr_1,
                               self.indentation_base * 10, self.baL, self.baV, tr_3, self.field,
                               self.indentation_base * 6,
                               self.indentation_base
                           )

                    self.baL_track = None
                    self.baV_track = None


                elif (flag_subscript_baV == 0):

                    body = '%s %s,\n' \
                           '%s %s,\n' \
                           '%s (void) 0' \
                           % (
                               self.indentation_base, tr_2,
                               self.indentation_base, tr_1,
                               self.indentation_base
                           )

                    self.baL_track = 0
                    self.baV_track = 0

                else:

                    body = '%s %s,\n' \
                           '%s %s,\n' \
                           '%s __CPROVER_set_field( %s, "%s", 1 ),\n' \
                           '%s (void) 0' \
                           % (
                               self.indentation_base, tr_2,
                               self.indentation_base, tr_1,
                               self.indentation_base, tr_3, self.field,
                               self.indentation_base
                           )

                    self.baL_track = 1
                    self.baV_track = 1

            ###---BODY-END----####

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfix_array'] = obj_list

            return self.lparen + '\n' + body + '\n' + self.rparen

        elif t_type == 'TRANSF_RW':

            self.cGen.operationBit = 'TRANSF_READ'
            tr_2 = self.cGen.visit(postfix_exp)

            flag_base_baV = self.baV_track

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(subscript)

            flag_subscript_baV = self.baV_track

            self.cGen.operationBit = 'GET_LVALUE'
            tr_3 = self.cGen.visit(postfix_exp)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)
            tr_3 = self.utility.beautifyString(tr_3)

            ###---BODY-START----####

            """

                (

                   [( postfix_exp, V_R )], 

                   (
                     true
                     &&   (     baV 
                             || (  [( exp, V_R )],  
                                   (     (baL=baV) 
                                      && (  set_field( [(postfix_exp, E)] , 1 ), 
                                            (_Bool) 0

                                 )
                           )
                                )
                          )     
                     &&   ( [( exp, V_R )], ( baL=baV=1 ) ) 
                   ),

                   (void) 0
                )   

            """
            if flag_base_baV:

                body = '%s %s,\n' \
                       '%s %s,\n' \
                       '%s (void) 0' \
                       % (
                           self.indentation_base, tr_2,
                           self.indentation_base, tr_1,
                           self.indentation_base
                       )

                self.baL_track = 1
                self.baV_track = 1

            elif (flag_base_baV == 0):

                if flag_subscript_baV:

                    body = '%s %s,\n' \
                           '%s %s,\n' \
                           '%s __CPROVER_set_field( %s, "%s", 1 ),\n' \
                           '%s (void) 0' \
                           % (
                               self.indentation_base, tr_2,
                               self.indentation_base, tr_1,
                               self.indentation_base, tr_3, self.field,
                               self.indentation_base
                           )

                    self.baL_track = 1
                    self.baV_track = 1

                elif (flag_subscript_baV == 0):

                    body = '%s %s,\n' \
                           '%s %s,\n' \
                           '%s (void) 0' \
                           % (
                               self.indentation_base, tr_2,
                               self.indentation_base, tr_1,
                               self.indentation_base
                           )

                    self.baV_track = 0
                    self.baL_track = 0

                else:

                    body = '%s %s,\n' \
                           '%s (\n' \
                           '%s %s,\n' \
                           '%s ( %s = %s  )\n' \
                           '%s && ( __CPROVER_set_field( %s, "%s", 1 ), (_Bool)0 ),' \
                           '%s ( %s = %s = 1 )\n' \
                           '%s && ( %s , ( %s = %s = 1 ) )\n' \
                           '%s (void) 0' \
                           % (
                               self.indentation_base, tr_2,
                               self.indentation_base * 4,
                               self.indentation_base * 10, tr_1,
                               self.indentation_base * 10, self.baL, self.baV,
                               self.indentation_base * 11, tr_3, self.field,
                               self.indentation_base * 12, self.baL, self.baV,
                               self.indentation_base * 4, tr_1, self.baL, self.baV,
                               self.indentation_base
                           )

                    self.baL_track = None
                    self.baV_track = None

            # baV cannot be determined
            else:
                body = '%s %s,\n' \
                       '%s (\n' \
                       '%s 1\n' \
                       '%s && (\n' \
                       '%s    %s\n' \
                       '%s || (\n' \
                       '%s %s,\n' \
                       '%s ( %s = %s  )\n' \
                       '%s && ( __CPROVER_set_field( %s, "%s", 1 ), 0 ),' \
                       '%s ( %s = %s = 1 )\n' \
                       '%s )\n' \
                       '%s )\n' \
                       '%s && ( %s , ( %s = %s = 1 ) )\n' \
                       '%s (void) 0' \
                       % (
                           self.indentation_base, tr_2,
                           self.indentation_base,
                           self.indentation_base * 4,
                           self.indentation_base * 4,
                           self.indentation_base * 6, self.baV,
                           self.indentation_base * 6,
                           self.indentation_base * 10, tr_1,
                           self.indentation_base * 10, self.baL, self.baV,
                           self.indentation_base * 11, tr_3, self.field,
                           self.indentation_base * 12, self.baL, self.baV,
                           self.indentation_base * 7,
                           self.indentation_base * 5,
                           self.indentation_base * 4, tr_1, self.baL, self.baV,
                           self.indentation_base
                       )

                self.baV_track = None
                self.baL_track = None

            ###---BODY-END----####

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfix_array'] = obj_list

            return self.lparen + '\n' + body + '\n' + self.rparen

        elif t_type == 'GET_OBJECT':

            ###---BODY-START----####

            self.cGen.operationBit = 'TRANSF_READ'
            tr_2 = self.cGen.visit(postfix_exp)

            flag_base_baV = self.baV_track

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(subscript)

            flag_subscript_baV = self.baV_track

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)

            """
                  (

                       [( postfix_exp, V_R )], 

                       (
                         true
                         &&   ( baV || (  [( exp, V_R )],  ( baL=baV ), (_Bool)0 ) )

                         &&  ( [( exp, V_R )], ( baL = 1 ) ) 
                       ),

                       (void) 0
                    )
            """

            if flag_base_baV:

                if flag_subscript_baV is None:
                    body = '%s %s,\n' \
                           '%s %s,\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_2,
                              self.indentation_base, tr_1,
                              self.indentation_base
                              )

                    self.baL_track = 1
                    self.baV_track = None

                elif flag_subscript_baV:
                    body = '%s %s,\n' \
                           '%s %s,\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_2,
                              self.indentation_base, tr_1,
                              self.indentation_base
                              )

                    self.baL_track = 1
                    self.baV_track = 1

                else:

                    body = '%s %s,\n' \
                           '%s %s,\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_2,
                              self.indentation_base, tr_1,
                              self.indentation_base
                              )

                    self.baL_track = 1
                    self.baV_track = 0

            elif flag_base_baV is None:

                body = '%s %s,\n' \
                       '%s (\n' \
                       '%s 1\n' \
                       '%s    && ( %s || ( %s, ( %s = %s ), (_Bool)0 ) )\n' \
                       '%s    && ( %s, ( %s = 1 ) )\n' \
                       '%s),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_2,
                          self.indentation_base,
                          self.indentation_base * 2,
                          self.indentation_base * 2, self.baL, tr_1, self.baL, self.baV,
                          self.indentation_base * 2, tr_1, self.baL,
                          self.indentation_base,
                          self.indentation_base
                          )

                self.baL_track = None
                self.baV_track = None


            else:

                """
                                 (

                                      [( postfix_exp, V_R )], 

                                      (
                                        true
                                        &&   ( baV || (  [( exp, V_R )],  ( baL=baV ), (_Bool)0 ) )

                                        &&  ( [( exp, V_R )], ( baL = 1 ) ) 
                                      ),

                                      (void) 0
                                   )
                           """

                if flag_subscript_baV is None:

                    body = '%s %s,\n' \
                           '%s (\n' \
                           '%s    ( %s, ( %s = %s ), (_Bool)0 )\n' \
                           '%s && ( %s, ( %s = 1 ) )\n' \
                           '%s),\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_2,
                              self.indentation_base,
                              self.indentation_base * 2, tr_1, self.baL, self.baV,
                              self.indentation_base * 2, tr_1, self.baL,
                              self.indentation_base,
                              self.indentation_base
                              )

                    self.baL_track = None
                    self.baV_track = None

                elif flag_subscript_baV:

                    body = '%s %s,\n' \
                           '%s %s,\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_2,
                              self.indentation_base, tr_1,
                              self.indentation_base
                              )

                    self.baL_track = 1
                    self.baV_track = 1

                else:

                    body = '%s %s,\n' \
                           '%s %s,\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_2,
                              self.indentation_base, tr_1,
                              self.indentation_base
                              )
                    self.baL_track = 0
                    self.baV_track = 0

            ###---BODY-END----####

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfix_array'] = obj_list

            return self.lparen + '\n' + body + '\n' + self.rparen


        elif t_type == 'GET_VALUE':

            """
                abstractable

                [( postfix_exp[exp], V )]  ::= DECODE( [( postfix_exp, V )] \[ [( exp, V)] \]


                not_abstractable

                [( postfix_exp[exp], V )]  ::= [( postfix_exp, V )] \[ [( exp, V)] \]
            """

            self.cGen.operationBit = 'GET_VALUE'
            tr_1 = self.cGen.visit(postfix_exp)
            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(subscript)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)

            key = 'postfix_array_%s' % (self.utility.macro_counter) if getMacro else 'postfix_array_%s' % (
                self.utility.local_macro_counter)

            self.macro_dict[key] = arref

            body_abt = '%s ((%s)DECODE ( %s[ %s ] ))' % (self.indentation_base, self.cast_bitvector, tr_1, tr_2)
            body_no_abt = '%s  %s[ %s ]' % (self.indentation_base, tr_1, tr_2)

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfix_array'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'postfix_array': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

            # return self.lparen + '\n' + body + '\n' + self.rparen

        elif t_type == 'GET_LVALUE':

            """
            [( postfix_exp[exp], E )]  ::= [( postfix_exp, V )] \[ [( exp, V )] \]
            """

            self.cGen.operationBit = 'GET_VALUE'
            tr_1 = self.cGen.visit(postfix_exp)

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(subscript)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)

            body = '( %s[%s] )' % (tr_1, tr_2)
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfix_array'] = obj_list

            return body

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_FuncCall(self, t_type, call, getMacro):

        self.rules_counter["func_call"] += 1

        new_transformation = Transformation('func_call')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('func_call')

        if t_type == 'TRANSF_READ':

            ###---DECLARATION-START----####

            func_val = self.func_val.format(self.prefix, str(self.GENERIC_VAL))

            self.valphi_map['func_call'].append(func_val)

            func_call_definition = '__typeof__(%s) %s;\n' % (call, func_val)

            declaration = func_call_definition

            new_transformation.declaration = declaration

            new_transformation.declaration_index_generic_1 = self.GENERIC_VAL

            self.GENERIC_VAL += 1

            ###---DECLARATION-END----####

            ###---BODY---###

            """(func_val = postfix_exp LPAREN RPAREN)"""

            body = "( %s = %s )" % (func_val, call)

            ris = self.utility.printMacro(getMacro, body, "")

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['func_call'] = obj_list

            return ris

        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE':
            self.utility.raiseException('This operation is not allowed!!')

        elif t_type == 'GET_VALUE':

            body = self.valphi_map['func_call'].pop()
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['func_call'] = obj_list
            return body

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_generic_assignment(self, t_type, unary_exp, ass_exp, ass_op, getMacro):

        self.rules_counter["generic_assignment"] += 1

        if getMacro:
            self.macro_key.append(self.getMacroKey('generic_assignment', 1))
        else:
            self.macro_key.append(self.getMacroKey('generic_assignment', 0))

        body_assignment_abt = self.getTR_generic_assignment_abt(t_type, unary_exp, ass_exp, ass_op, getMacro)

        if '__PLACEHOLDER__' in body_assignment_abt:
            self.utility.printCustomMacro(body_assignment_abt)
            return self.utility.printMacro(getMacro, body_assignment_abt, 'yes')
        else:
            return self.utility.printMacro(getMacro, body_assignment_abt)

    def getTR_generic_assignment_abt(self, t_type, unary_exp, ass_exp, ass_op, getMacro):

        new_transformation = Transformation('generic_assignment')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('generic_assignment')

        # Let's get the orginal ass_exp
        cGen_orignal = CGenerator()
        unary_exp_str = cGen_orignal.visit(unary_exp)

        if getMacro:
            key = 'generic_assignment_%s' % (self.utility.macro_counter)
        else:
            key = 'generic_assignment_%s' % (self.utility.local_macro_counter)

        bounds_failure_signed_list = []
        bounds_failure_unsigned_list = []
        encoding_list = []

        # Aggiungere check se baL_track e baV_track sono diversi da None allora posso determiniare e propagare!!
        # Non stampare il baV quando siamo capaci di determinarlo

        if t_type == 'TRANSF_READ':

            ###---BODY-START----####

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(ass_exp)

            flag_exp1_baV = self.baV_track

            self.cGen.operationBit = 'GET_VALUE'
            tr_4 = self.cGen.visit(ass_exp)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_4 = self.utility.beautifyString(tr_4)

            if ass_op != '=':

                self.cGen.operationBit = 'TRANSF_RW'
                tr_2 = self.cGen.visit(unary_exp)
                tr_2 = self.utility.beautifyString(tr_2)

                flag_exp2_baL = self.baL_track
                flag_exp2_baV = self.baV_track

                self.cGen.operationBit = 'GET_VALUE'
                tr_5 = self.cGen.visit(unary_exp)
                tr_5 = self.utility.beautifyString(tr_5)

            else:

                self.cGen.operationBit = 'TRANSF_WRITE'
                tr_2 = self.cGen.visit(unary_exp)
                tr_2 = self.utility.beautifyString(tr_2)

                flag_exp2_baL = self.baL_track
                flag_exp2_baV = self.baV_track

            self.cGen.operationBit = 'GET_LVALUE'
            tr_3 = self.cGen.visit(unary_exp)
            tr_3 = self.utility.beautifyString(tr_3)

            """
                    (
                            [( ass_expr, V_R )], baV_rhs=baV,

                            [( unary_exp, * )], // where \* is equal to V_W if ass_op is '=' otherwise it's V_RW

                            ( (!baL)  &&
                                         (   
                                               (     false
                                                     || baV_rhs
                                                     || ( OP && baV )
                                                     || BOUNDS_FAILURE_XXSIGNED_TYPE( ( [( unary_exp, V )] op [( ass_expr, V )]) )  
                                               )

                                               ?  (  baV = 1, 
                                                     set_field( &[( unary_exp , E )], 1), 
                                                     (_Bool) 1 
                                                  )

                                               :  ( 
                                                     ( !OP  &&  set_field( & [( unary_exp , E )] , 0 ) ) , 
                                                     ( [( unary_exp, E )] = 
                                                                            ENCODE( (typeof(unary_exp)) ( [( unary_exp, V )] op [( ass_expr, V )] ), unary_exp )

                                                     ),
                                                     (_Bool)1      

                                                  )
                                         )
                            ),             

                            (void) 0
                         )


            """

            if ass_op != '=':

                # here OP is equal to 1

                operator = ass_op[0]

                self.macro_dict[key] = unary_exp_str

                for type in self.types:
                    bounds_failure_signed_list.append(
                        "BOUNDS_FAILURE_SIGNED_%s( ( ((%s)%s) %s ((%s)%s) ) ) " % (type, self.cast_bitvector,tr_5, operator, self.cast_bitvector, tr_4))
                    bounds_failure_unsigned_list.append(
                        "BOUNDS_FAILURE_UNSIGNED_%s( ( ((%s)%s) %s ((%s)%s) ) ) " % (type, self.cast_bitvector,tr_5, operator, self.cast_bitvector, tr_4))
                    encoding_list.append("( ENCODE_%s( ((%s)%s) %s ((%s)%s)  ) " % (type, self.cast_bitvector,tr_5, operator, self.cast_bitvector, tr_4))

                if flag_exp2_baL:

                    body_abt = '%s %s,\n' \
                               '%s %s,\n' \
                               '%s (void)0' \
                               % (
                                   self.indentation_base, tr_1,
                                   self.indentation_base, tr_2,
                                   self.indentation_base
                               )
                    body_no_abt = body_abt

                elif (flag_exp2_baL == 0):

                    # or ( flag_exp1_baV is None and flag_exp2_baV) or ( flag_exp2_baV is None and flag_exp1_baV)
                    # the following if captures the cases above as well

                    if (flag_exp1_baV or flag_exp2_baV):

                        body_abt = '%s %s,\n' \
                                   '%s %s,\n' \
                                   '%s __CPROVER_set_field( &(%s), "%s", 1 ),\n' \
                                   '%s (void)0' \
                                   % (
                                       self.indentation_base, tr_1,
                                       self.indentation_base, tr_2,
                                       self.indentation_base, tr_3, self.field,
                                       self.indentation_base
                                   )

                        body_no_abt = body_abt

                        self.baV_track = 1
                        self.baL_track = 0

                    elif ((flag_exp1_baV == 0) and (flag_exp2_baV == 0)):

                        # abstractable
                        body_abt = '%s %s,\n' \
                                   '%s %s,\n' \
                                   '%s (\n' \
                                   '%s %s \n' \
                                   '%s ? (\n' \
                                   '%s  ( %s = 1 ),\n' \
                                   '%s  __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                                   '%s )\n' \
                                   '%s : (\n' \
                                   '%s  ( %s = %s )\n' \
                                   '%s  )\n' \
                                   '%s ),\n' \
                                   '%s (void)0' \
                                   % (
                                       self.indentation_base, tr_1,
                                       self.indentation_base, tr_2,
                                       self.indentation_base,
                                       self.indentation_base * 8, '__place__',
                                       self.indentation_base * 11,
                                       self.indentation_base * 16, self.baV,
                                       self.indentation_base * 16, tr_3, self.field,
                                       self.indentation_base * 12,
                                       self.indentation_base * 11,
                                       self.indentation_base * 16, tr_3, '__encoding__',
                                       self.indentation_base * 11,
                                       self.indentation_base,
                                       self.indentation_base
                                   )

                        body_no_abt = \
                            '%s %s,\n' \
                            '%s %s,\n' \
                            '%s __CPROVER_set_field( &(%s) , "%s", 0),\n' \
                            '%s( %s %s %s ),\n' \
                            '%s (void)0' \
                            % (
                                self.indentation_base, tr_1,
                                self.indentation_base, tr_2,
                                self.indentation_base, tr_3, self.field,
                                self.indentation_base, tr_3, ass_op, tr_4,
                                self.indentation_base
                            )

                        # self.baV_track = None
                        self.baL_track = 0

                    elif ((flag_exp1_baV is None) and (flag_exp2_baV == 0)):

                        baV_rhs = self.baV_rhs.format(self.prefix, str(self.GENERIC_BA))

                        baV_rhs_definition = '_Bool %s=0;\n' % baV_rhs

                        declaration = baV_rhs_definition

                        new_transformation.declaration = declaration

                        new_transformation.declaration_index_generic_1 = self.GENERIC_BA

                        self.GENERIC_BA += 1

                        body_abt = '%s %s,\n' \
                                   '%s %s,\n' \
                                   '%s ( %s = %s ),\n' \
                                   '%s (   \n' \
                                   '%s       ( %s )\n' \
                                   '%s    || ( %s )\n' \
                                   '%s  )\n' \
                                   '%s ? (\n' \
                                   '%s  ( %s = 1 ),\n' \
                                   '%s  __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                                   '%s )\n' \
                                   '%s : (\n' \
                                   '%s  ( %s = %s )\n' \
                                   '%s  ),\n' \
                                   '%s  ),\n' \
                                   '%s (void)0' \
                                   % (
                                       self.indentation_base, tr_1,
                                       self.indentation_base, tr_2,
                                       self.indentation_base, baV_rhs, self.baV,
                                       self.indentation_base * 12,
                                       self.indentation_base * 12, baV_rhs,
                                       self.indentation_base * 12, '__place__',
                                       self.indentation_base * 12,
                                       self.indentation_base * 11,
                                       self.indentation_base * 16, self.baV,
                                       self.indentation_base * 16, tr_3, self.field,
                                       self.indentation_base * 12,
                                       self.indentation_base * 11,
                                       self.indentation_base * 16, tr_3, '__encoding__',
                                       self.indentation_base * 11,
                                       self.indentation_base,
                                       self.indentation_base
                                   )

                        body_no_abt = '%s %s,\n' \
                                      '%s %s,\n' \
                                      '%s ( %s = %s ),' \
                                      '%s (\n' \
                                      '%s ( %s ) \n' \
                                      '%s ? (\n' \
                                      '%s ( %s = 1 ),\n' \
                                      '%s  __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                                      '%s )\n' \
                                      '%s : (\n' \
                                      '%s  ( %s %s %s )\n' \
                                      '%s  )\n' \
                                      '%s  ),\n' \
                                      '%s (void)0' \
                                      % (
                                          self.indentation_base, tr_1,
                                          self.indentation_base, tr_2,
                                          self.indentation_base, baV_rhs, self.baV,
                                          self.indentation_base,
                                          self.indentation_base * 12, baV_rhs,
                                          self.indentation_base * 11,
                                          self.indentation_base * 16, self.baV,
                                          self.indentation_base * 16, tr_3, self.field,
                                          self.indentation_base * 12,
                                          self.indentation_base * 11,
                                          self.indentation_base * 16, tr_3, ass_op, tr_4,
                                          self.indentation_base * 11,
                                          self.indentation_base,
                                          self.indentation_base
                                      )

                        self.baV_track = None
                        self.baL_track = 0

                    elif (flag_exp1_baV == 0) and (flag_exp2_baV is None):

                        body_abt = '%s %s,\n' \
                                   '%s %s,\n' \
                                   '%s (\n' \
                                   '%s (   \n' \
                                   '%s       ( %s )\n' \
                                   '%s    || ( %s )\n' \
                                   '%s )\n' \
                                   '%s ? (\n' \
                                   '%s  ( %s = 1 ),\n' \
                                   '%s  __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                                   '%s )\n' \
                                   '%s : (\n' \
                                   '%s  ( %s = %s ) )\n' \
                                   '%s )\n' \
                                   '%s  ),\n' \
                                   '%s (void)0' \
                                   % (
                                       self.indentation_base, tr_1,
                                       self.indentation_base, tr_2,
                                       self.indentation_base,
                                       self.indentation_base * 12,
                                       self.indentation_base * 12, self.baV,
                                       self.indentation_base * 12, '__place__',
                                       self.indentation_base * 12,
                                       self.indentation_base * 11,
                                       self.indentation_base * 16, self.baV,
                                       self.indentation_base * 16, tr_3, self.field,
                                       self.indentation_base * 12,
                                       self.indentation_base * 11,
                                       self.indentation_base * 16, tr_3, '__encoding__',
                                       self.indentation_base * 12,
                                       self.indentation_base,
                                       self.indentation_base
                                   )

                        body_no_abt = '%s %s,\n' \
                                      '%s %s,\n' \
                                      '%s ( %s ) \n' \
                                      '%s ? (\n' \
                                      '%s  %s = 1,\n' \
                                      '%s  __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                                      '%s )\n' \
                                      '%s : (\n' \
                                      '%s  ( %s %s %s )\n' \
                                      '%s  )\n' \
                                      '%s  ),\n' \
                                      '%s (void)0' \
                                      % (
                                          self.indentation_base, tr_1,
                                          self.indentation_base, tr_2,
                                          self.indentation_base * 12, self.baV,
                                          self.indentation_base * 11,
                                          self.indentation_base * 16, self.baV,
                                          self.indentation_base * 16, tr_3, self.field,
                                          self.indentation_base * 12,
                                          self.indentation_base * 11,
                                          self.indentation_base * 16, tr_3, ass_op, tr_4,
                                          self.indentation_base * 11,
                                          self.indentation_base,
                                          self.indentation_base
                                      )

                        self.baV_track = None
                        self.baL_track = 0

                    else:

                        ###---DECLARATION-START----####

                        baV_rhs = self.baV_rhs.format(self.prefix, str(self.GENERIC_BA))

                        baV_rhs_definition = '_Bool %s=0;\n' % baV_rhs

                        declaration = baV_rhs_definition

                        new_transformation.declaration = declaration

                        new_transformation.declaration_index_generic_1 = self.GENERIC_BA

                        self.GENERIC_BA += 1

                        ###---DECLARATION-END----####

                        body_abt = '%s %s,\n' \
                                   '%s ( %s = %s ),\n' \
                                   '%s %s,\n' \
                                   '%s (\n' \
                                   '%s (   0\n' \
                                   '%s    || ( %s )\n' \
                                   '%s    || ( %s )\n' \
                                   '%s    || ( %s )\n' \
                                   '%s )\n' \
                                   '%s ? (\n' \
                                   '%s  ( %s = 1 ),\n' \
                                   '%s  __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                                   '%s )\n' \
                                   '%s : (\n' \
                                   '%s  ( %s = %s ) )\n' \
                                   '%s )\n' \
                                   '%s  ),\n' \
                                   '%s (void)0' \
                                   % (
                                       self.indentation_base, tr_1,
                                       self.indentation_base, baV_rhs, self.baV,
                                       self.indentation_base, tr_2,
                                       self.indentation_base,
                                       self.indentation_base * 12,
                                       self.indentation_base * 12, baV_rhs,
                                       self.indentation_base * 12, self.baV,
                                       self.indentation_base * 12, '__place__',
                                       self.indentation_base * 12,
                                       self.indentation_base * 11,
                                       self.indentation_base * 16, self.baV,
                                       self.indentation_base * 16, tr_3, self.field,
                                       self.indentation_base * 12,
                                       self.indentation_base * 11,
                                       self.indentation_base * 16, tr_3, '__encoding__',
                                       self.indentation_base * 12,
                                       self.indentation_base,
                                       self.indentation_base
                                   )

                        body_no_abt = '%s %s,\n' \
                                      '%s ( %s = %s ),\n' \
                                      '%s %s,\n' \
                                      '%s (\n' \
                                      '%s (   0\n' \
                                      '%s    || %s\n' \
                                      '%s    || ( %s )\n' \
                                      '%s )\n' \
                                      '%s ? (\n' \
                                      '%s  ( %s = 1 ),\n' \
                                      '%s  __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                                      '%s )\n' \
                                      '%s : (\n' \
                                      '%s  ( %s %s %s )\n' \
                                      '%s  )\n' \
                                      '%s  ),\n' \
                                      '%s (void)0' \
                                      % (
                                          self.indentation_base, tr_1,
                                          self.indentation_base, baV_rhs, self.baV,
                                          self.indentation_base, tr_2,
                                          self.indentation_base,
                                          self.indentation_base * 12,
                                          self.indentation_base * 12, baV_rhs,
                                          self.indentation_base * 12, self.baV,
                                          self.indentation_base * 12,
                                          self.indentation_base * 11,
                                          self.indentation_base * 16, self.baV,
                                          self.indentation_base * 16, tr_3, self.field,
                                          self.indentation_base * 12,
                                          self.indentation_base * 11,
                                          self.indentation_base * 16, tr_3, ass_op, tr_4,
                                          self.indentation_base * 11,
                                          self.indentation_base,
                                          self.indentation_base
                                      )

                        self.baV_track = None
                        self.baL_track = 0
                else:

                    ###---DECLARATION-START----####

                    baV_rhs = self.baV_rhs.format(self.prefix, str(self.GENERIC_BA))

                    baV_rhs_definition = '_Bool %s=0;\n' % baV_rhs

                    declaration = baV_rhs_definition

                    new_transformation.declaration = declaration

                    new_transformation.declaration_index_generic_1 = self.GENERIC_BA

                    self.GENERIC_BA += 1

                    ###---DECLARATION-END----####

                    body_abt = '%s %s,\n' \
                               '%s %s = %s,\n' \
                               '%s %s,\n' \
                               '%s ( (!%s) && (\n' \
                               '%s (   0\n' \
                               '%s    || %s\n' \
                               '%s    || ( %s )\n' \
                               '%s    || ( %s )\n' \
                               '%s  )\n' \
                               '%s ? (\n' \
                               '%s  %s = 1,\n' \
                               '%s  __CPROVER_set_field( &(%s), "abstraction", 1 ),\n' \
                               '%s  (_Bool) 1\n' \
                               '%s )\n' \
                               '%s : (\n' \
                               '%s  ( %s = %s )\n' \
                               '%s  ),\n' \
                               '%s  (_Bool)1\n' \
                               '%s )\n' \
                               '%s ),\n' \
                               '%s (void)0' \
                               % (
                                   self.indentation_base, tr_1,
                                   self.indentation_base, baV_rhs, self.baV,
                                   self.indentation_base, tr_2,
                                   self.indentation_base, self.baL,
                                   self.indentation_base * 12,
                                   self.indentation_base * 12, baV_rhs,
                                   self.indentation_base * 12, self.baV,
                                   self.indentation_base * 12, '__place__',
                                   self.indentation_base * 12,
                                   self.indentation_base * 11,
                                   self.indentation_base * 16, self.baV,
                                   self.indentation_base * 16, tr_3,
                                   self.indentation_base * 16,
                                   self.indentation_base * 12,
                                   self.indentation_base * 11,
                                   self.indentation_base * 16, tr_3, '__encoding__',
                                   self.indentation_base * 11,
                                   self.indentation_base * 11,
                                   self.indentation_base * 9,
                                   self.indentation_base,
                                   self.indentation_base
                               )

                    body_no_abt = '%s %s,\n' \
                                  '%s %s = %s,\n' \
                                  '%s %s,\n' \
                                  '%s ( (!%s) && (\n' \
                                  '%s (   0\n' \
                                  '%s    || %s\n' \
                                  '%s    || ( %s )\n' \
                                  '%s )\n' \
                                  '%s ? (\n' \
                                  '%s  %s = 1,\n' \
                                  '%s  __CPROVER_set_field( &(%s), "abstraction", 1 ),\n' \
                                  '%s  (_Bool) 1\n' \
                                  '%s )\n' \
                                  '%s : (\n' \
                                  '%s  ( %s %s %s )\n' \
                                  '%s  ),\n' \
                                  '%s  (_Bool)1\n' \
                                  '%s )\n' \
                                  '%s ),\n' \
                                  '%s (void)0' \
                                  % (
                                      self.indentation_base, tr_1,
                                      self.indentation_base, baV_rhs, self.baV,
                                      self.indentation_base, tr_2,
                                      self.indentation_base, self.baL,
                                      self.indentation_base * 12,
                                      self.indentation_base * 12, baV_rhs,
                                      self.indentation_base * 12, self.baV,
                                      self.indentation_base * 12,
                                      self.indentation_base * 11,
                                      self.indentation_base * 16, self.baV,
                                      self.indentation_base * 16, tr_3,
                                      self.indentation_base * 16,
                                      self.indentation_base * 12,
                                      self.indentation_base * 11,
                                      self.indentation_base * 16, tr_3, ass_op, tr_4,
                                      self.indentation_base * 11,
                                      self.indentation_base * 11,
                                      self.indentation_base * 9,
                                      self.indentation_base,
                                      self.indentation_base
                                  )
                    self.baV_track = None
                    self.baL_track = None

            else:

                # here OP = 0
                # Direct assignment

                self.macro_dict[key] = unary_exp_str

                for type in self.types:
                    bounds_failure_signed_list.append(
                        "BOUNDS_FAILURE_SIGNED_%s( ( %s ) ) " % (type, tr_4))
                    bounds_failure_unsigned_list.append(
                        "BOUNDS_FAILURE_UNSIGNED_%s( ( %s ) ) " % (type, tr_4))
                    encoding_list.append('ENCODE_%s( %s )' % (type, tr_4))

                if flag_exp2_baL:

                    body_abt = '%s %s,\n' \
                               '%s %s,\n' \
                               '%s (void)0' \
                               % (
                                   self.indentation_base, tr_1,
                                   self.indentation_base, tr_2,
                                   self.indentation_base
                               )
                    body_no_abt = body_abt
                    self.baL_track = 0

                elif (flag_exp2_baL == 0):

                    if flag_exp1_baV:

                        # abstractable
                        body_abt = '%s %s,\n' \
                                   '%s %s,\n' \
                                   '%s __CPROVER_set_field( &(%s), "%s", 1 ),\n' \
                                   '%s (void)0' \
                                   % (
                                       self.indentation_base, tr_1,
                                       self.indentation_base, tr_2,
                                       self.indentation_base, tr_3, self.field,
                                       self.indentation_base
                                   )

                        body_no_abt = body_abt

                        self.baV_track = 1
                        self.baL_track = 0


                    elif (flag_exp1_baV == 0):

                        body_abt = '%s %s,\n' \
                                   '%s %s,\n' \
                                   '%s (\n' \
                                   '%s %s \n' \
                                   '%s ? (\n' \
                                   '%s  (%s = 1 ),\n' \
                                   '%s  __CPROVER_set_field( &(%s), "%s", 1 )\n' \
                                   '%s   )\n' \
                                   '%s : (\n' \
                                   '%s __CPROVER_set_field( &(%s), "%s", 0 ),\n' \
                                   '%s  ( %s = %s )\n' \
                                   '%s   )\n' \
                                   '%s ),\n' \
                                   '%s (void)0' \
                                   % (
                                       self.indentation_base, tr_1,
                                       self.indentation_base, tr_2,
                                       self.indentation_base,
                                       self.indentation_base * 4, '__place__',
                                       self.indentation_base * 12,
                                       self.indentation_base * 16, self.baV,
                                       self.indentation_base * 16, tr_3, self.field,
                                       self.indentation_base * 12,
                                       self.indentation_base * 12,
                                       self.indentation_base * 16, tr_3, self.field,
                                       self.indentation_base * 16, tr_3, '__encoding__',
                                       self.indentation_base * 12,
                                       self.indentation_base,
                                       self.indentation_base
                                   )

                        body_no_abt = \
                            '%s %s,\n' \
                            '%s %s,\n' \
                            '%s __CPROVER_set_field( &(%s) , "%s", 0),\n' \
                            '%s( %s %s %s ),\n' \
                            '%s (void)0' \
                            % (
                                self.indentation_base, tr_1,
                                self.indentation_base, tr_2,
                                self.indentation_base, tr_3, self.field,
                                self.indentation_base, tr_3, ass_op, tr_4,
                                self.indentation_base
                            )

                        self.baV_track = None
                        self.baL_track = 0

                    else:

                        # if flag_exp2_baV is None i don't care since OP = 0 then whatever the value of baV is we always fail

                        ###---DECLARATION-START----####

                        baV_rhs = self.baV_rhs.format(self.prefix, str(self.GENERIC_BA))

                        baV_rhs_definition = '_Bool %s=0;\n' % baV_rhs

                        declaration = baV_rhs_definition

                        new_transformation.declaration = declaration

                        new_transformation.declaration_index_generic_1 = self.GENERIC_BA

                        self.GENERIC_BA += 1
                        ###---DECLARATION-END----####

                        body_abt = '%s %s,\n' \
                                   '%s %s,\n' \
                                   '%s ( %s = %s ),\n' \
                                   '%s (   \n' \
                                   '%s    %s\n' \
                                   '%s || %s\n' \
                                   '%s ? (\n' \
                                   '%s  ( %s = 1 ),\n' \
                                   '%s  __CPROVER_set_field( &(%s), "%s", 1 ),\n' \
                                   '%s  (_Bool) 1\n' \
                                   '%s   )\n' \
                                   '%s : (\n' \
                                   '%s  __CPROVER_set_field( &(%s), "%s", 0 ),\n' \
                                   '%s  ( %s = %s ),\n' \
                                   '%s  (_Bool)1\n' \
                                   '%s   )\n' \
                                   '%s  ),\n' \
                                   '%s (void)0' \
                                   % (
                                       self.indentation_base, tr_1,
                                       self.indentation_base, tr_2,
                                       self.indentation_base, baV_rhs, self.baV,
                                       self.indentation_base,
                                       self.indentation_base * 6, baV_rhs,
                                       self.indentation_base * 6, '__place__',
                                       self.indentation_base * 12,
                                       self.indentation_base * 16, self.baV,
                                       self.indentation_base * 16, tr_3, self.field,
                                       self.indentation_base * 16,
                                       self.indentation_base * 12,
                                       self.indentation_base * 12,
                                       self.indentation_base * 16, tr_3, self.field,
                                       self.indentation_base * 16, tr_3, '__encoding__',
                                       self.indentation_base * 16,
                                       self.indentation_base * 12,
                                       self.indentation_base,
                                       self.indentation_base
                                   )

                        body_no_abt = '%s %s,\n' \
                                      '%s %s,\n' \
                                      '%s ( %s = %s ),\n' \
                                      '%s (\n' \
                                      '%s ( %s )\n' \
                                      '%s ? (\n' \
                                      '%s  %s = 1,\n' \
                                      '%s  __CPROVER_set_field( &(%s), "abstraction", 1 )\n' \
                                      '%s )\n' \
                                      '%s : (\n' \
                                      '%s  __CPROVER_set_field( &(%s), "%s", 0 ),\n' \
                                      '%s  ( %s %s %s )\n' \
                                      '%s )\n' \
                                      '%s ),\n' \
                                      '%s (void)0' \
                                      % (
                                          self.indentation_base, tr_1,
                                          self.indentation_base, tr_2,
                                          self.indentation_base, baV_rhs, self.baV,
                                          self.indentation_base * 9,
                                          self.indentation_base * 12, baV_rhs,
                                          self.indentation_base * 11,
                                          self.indentation_base * 16, self.baV,
                                          self.indentation_base * 16, tr_3,
                                          self.indentation_base * 12,
                                          self.indentation_base * 11,
                                          self.indentation_base * 16, tr_3, self.field,
                                          self.indentation_base * 16, tr_3, ass_op, tr_4,
                                          self.indentation_base * 12,
                                          self.indentation_base * 9,
                                          self.indentation_base
                                      )

                        self.baV_track = None
                        self.baL_track = 0

                else:

                    ###---DECLARATION-START----####

                    baV_rhs = self.baV_rhs.format(self.prefix, str(self.GENERIC_BA))

                    baV_rhs_definition = '_Bool %s=0;\n' % baV_rhs

                    declaration = baV_rhs_definition

                    new_transformation.declaration = declaration

                    new_transformation.declaration_index_generic_1 = self.GENERIC_BA

                    self.GENERIC_BA += 1
                    ###---DECLARATION-END----####

                    body_abt = '%s %s,\n' \
                               '%s %s = %s,\n' \
                               '%s %s,\n' \
                               '%s ( (!%s) && (\n' \
                               '%s (   0\n' \
                               '%s    || %s\n' \
                               '%s    || ( %s )\n' \
                               '%s    || ( %s )\n' \
                               '%s )\n' \
                               '%s ? (\n' \
                               '%s  %s = 1,\n' \
                               '%s  __CPROVER_set_field( &(%s), "abstraction", 1 ),\n' \
                               '%s  (_Bool) 1\n' \
                               '%s )\n' \
                               '%s : (\n' \
                               '%s  ( %s = %s ),\n' \
                               '%s  (_Bool)1\n' \
                               '%s )\n' \
                               '%s  )\n' \
                               '%s ),\n' \
                               '%s (void)0' \
                               % (
                                   self.indentation_base, tr_1,
                                   self.indentation_base, baV_rhs, self.baV,
                                   self.indentation_base, tr_2,
                                   self.indentation_base, self.baL,
                                   self.indentation_base * 12,
                                   self.indentation_base * 12, baV_rhs,
                                   self.indentation_base * 12, self.baV,
                                   self.indentation_base * 12, '__place__',
                                   self.indentation_base * 12,
                                   self.indentation_base * 11,
                                   self.indentation_base * 16, self.baV,
                                   self.indentation_base * 16, tr_3,
                                   self.indentation_base * 16,
                                   self.indentation_base * 12,
                                   self.indentation_base * 11,
                                   self.indentation_base * 16, tr_3, '__encoding__',
                                   self.indentation_base * 16,
                                   self.indentation_base * 12,
                                   self.indentation_base * 9,
                                   self.indentation_base,
                                   self.indentation_base
                               )

                    body_no_abt = '%s %s,\n' \
                                  '%s %s = %s,\n' \
                                  '%s %s,\n' \
                                  '%s ( (!%s) && (\n' \
                                  '%s (   0\n' \
                                  '%s    || %s\n' \
                                  '%s    || ( %s )\n' \
                                  '%s )\n' \
                                  '%s ? (\n' \
                                  '%s  %s = 1,\n' \
                                  '%s  __CPROVER_set_field( &(%s), "abstraction", 1 ),\n' \
                                  '%s  (_Bool) 1\n' \
                                  '%s )\n' \
                                  '%s : (\n' \
                                  '%s  ( %s %s %s ),\n' \
                                  '%s  (_Bool)1\n' \
                                  '%s )\n' \
                                  '%s )\n' \
                                  '%s ),\n' \
                                  '%s (void)0' \
                                  % (
                                      self.indentation_base, tr_1,
                                      self.indentation_base, baV_rhs, self.baV,
                                      self.indentation_base, tr_2,
                                      self.indentation_base, self.baL,
                                      self.indentation_base * 12,
                                      self.indentation_base * 12, baV_rhs,
                                      self.indentation_base * 12, self.baV,
                                      self.indentation_base * 12,
                                      self.indentation_base * 11,
                                      self.indentation_base * 16, self.baV,
                                      self.indentation_base * 16, tr_3,
                                      self.indentation_base * 16,
                                      self.indentation_base * 12,
                                      self.indentation_base * 11,
                                      self.indentation_base * 16, tr_3, ass_op, tr_4,
                                      self.indentation_base * 11,
                                      self.indentation_base * 12,
                                      self.indentation_base * 9,
                                      self.indentation_base,
                                      self.indentation_base
                                  )

                    self.baV_track = None
                    self.baL_track = None

            ###---BODY-END----####

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt, 'bounds_signed_list': bounds_failure_signed_list,
                    'bounds_unsigned_list': bounds_failure_unsigned_list, 'encoding': encoding_list}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['generic_assignment'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'generic_assignment': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key


        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE' or t_type == 'TRANSF_RW' or t_type == 'GET_OBJECT':
            self.utility.raiseException('This operation is not allowed!!')

        elif (t_type == 'GET_VALUE'):

            """
                    abstractable

                    [(unary_exp ass_op ass_expr, V )] ::= DECODE( [( unary_exp, E )]  )


                    not abstractable

                    [(unary_exp ass_op ass_expr, V )] ::= [( unary_exp, V )] )

            """

            self.cGen.operationBit = 'GET_LVALUE'
            tr_1 = self.cGen.visit(unary_exp)
            tr_1 = self.utility.beautifyString(tr_1)

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(unary_exp)
            tr_2 = self.utility.beautifyString(tr_2)

            body_abt = '%s ( (%s)DECODE( %s ) )' % (self.indentation_base, self.cast_bitvector, tr_1)
            body_no_abt = '%s %s' % (self.indentation_base, tr_2)

            self.macro_dict[key] = unary_exp_str

            body = {'abt': body_abt, 'no_abt': body_no_abt}
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['generic_assignment'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'generic_assignment': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_assignment(self, t_type, unary_exp, ass_exp, ass_op, getMacro):

        self.rules_counter["assignment"] += 1

        if getMacro:
            self.macro_key.append(self.getMacroKey('assignment', 1))
        else:
            self.macro_key.append(self.getMacroKey('assignment', 0))

        body_assignment_abt = self.getTR_assignment_abt(t_type, unary_exp, ass_exp, ass_op, getMacro)

        if '__PLACEHOLDER__' in body_assignment_abt:
            self.utility.printCustomMacro(body_assignment_abt)

            return self.utility.printMacro(getMacro, body_assignment_abt, 'yes')
        else:
            return self.utility.printMacro(getMacro, body_assignment_abt)

    def getTR_assignment_abt(self, t_type, unary_exp, ass_exp, ass_op, getMacro):

        new_transformation = Transformation('assignment')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('assignment')

        # Let's get the orginal ass_exp
        cGen_orignal = CGenerator()
        unary_exp_str = cGen_orignal.visit(unary_exp)

        if getMacro:
            key = 'assignment_%s' % self.utility.macro_counter
        else:
            key = 'assignment_%s' % self.utility.local_macro_counter

        if t_type == 'TRANSF_READ':

            ###---BODY-START----####

            self.cGen.operationBit = 'GET_LVALUE'
            tr_3 = self.cGen.visit(unary_exp)

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(ass_exp)

            flag_baV = self.baV_track

            self.cGen.operationBit = 'GET_VALUE'
            tr_4 = self.cGen.visit(ass_exp)

            self.cGen.operationBit = 'GET_VALUE'
            tr_5 = self.cGen.visit(unary_exp)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_3 = self.utility.beautifyString(tr_3)
            tr_4 = self.utility.beautifyString(tr_4)
            tr_5 = self.utility.beautifyString(tr_5)

            # abstractable
            """
                  [( unary_exp, E )] = (
                              [( ass_expr, V_R )], 

                              (
					                        (
                      					        (   false
                          				 	        || baV
                          					        || BOUNDS_FAILURE_XXSIGNED_TYPE( [( ass_expr, V )]  )     
                                            )

                                        ?    (   
                                                 set_field(& [( unary_exp , E )] , 1),   
                                                 (void)0    
                                             )

                                        :    ENCODE([( ass_expr, V )], [( unary_exp, V )])
                                  )

                              )     
                         )
            """
            self.macro_dict[key] = unary_exp_str

            bounds_failure_signed_list = []
            bounds_failure_unsigned_list = []
            encoding_list = []

            for type in self.types:
                bounds_failure_signed_list.append(
                    "BOUNDS_FAILURE_SIGNED_%s( ( %s ) ) " % (type, tr_4))
                bounds_failure_unsigned_list.append(
                    "BOUNDS_FAILURE_UNSIGNED_%s( ( %s ) ) " % (type, tr_4))
                encoding_list.append('ENCODE_%s( %s )' % (type, tr_4))

            if flag_baV:

                body_abt = "%s %s = (\n" \
                           "%s %s,\n" \
                           "%s  __CPROVER_set_field( &(%s), \"%s\", 1 ),\n" \
                           "%s  (typeof(%s))0 \n" \
                           "%s )" % (self.indentation_base, tr_3,
                                     self.indentation_base * 10, tr_1,
                                     self.indentation_base * 10, tr_3, self.field,
                                     self.indentation_base * 10, unary_exp_str,
                                     self.indentation_base * 8
                                     )

                body_no_abt = body_abt

                self.baV_track = 1


            elif (flag_baV == 0):

                body_abt = "%s %s = (\n" \
                           "%s %s,\n" \
                           "%s (\n" \
                           "%s ( \n" \
                           "%s    ( %s )\n" \
                           "%s )\n" \
                           "%s ?  ( \n" \
                           "%s  __CPROVER_set_field( &(%s), \"%s\", 1 ),\n" \
                           "%s  (typeof(%s))0 \n" \
                           "%s)\n" \
                           "%s : %s\n" \
                           "%s )\n" \
                           "%s )" % (self.indentation_base, tr_3,
                                     self.indentation_base * 10, tr_1,
                                     self.indentation_base * 14,
                                     self.indentation_base * 16,
                                     self.indentation_base * 16, '__place__',
                                     self.indentation_base * 16,
                                     self.indentation_base * 16,
                                     self.indentation_base * 18, tr_3, self.field,
                                     self.indentation_base * 18, unary_exp_str,
                                     self.indentation_base * 18,
                                     self.indentation_base * 16, '__encoding__',
                                     self.indentation_base * 14,
                                     self.indentation_base * 8
                                     )

                body_no_abt = "%s %s = (\n" \
                              "%s %s,\n" \
                              "%s %s \n" \
                              "%s )" % (self.indentation_base, tr_3,
                                        self.indentation_base * 10, tr_1,
                                        self.indentation_base * 10, tr_5,
                                        self.indentation_base * 8
                                        )
                self.baV_track = 0

            else:
                body_abt = "%s %s = (\n" \
                           "%s %s,\n" \
                           "%s (\n" \
                           "%s (    0\n" \
                           "%s   || %s\n" \
                           "%s )\n" \
                           "%s ?  ( \n" \
                           "%s  __CPROVER_set_field( &(%s), \"%s\", 1 ),\n" \
                           "%s  (typeof(%s))0\n" \
                           "%s)\n" \
                           "%s : %s\n" \
                           "%s )\n" \
                           "%s )" % (self.indentation_base, tr_3,
                                     self.indentation_base * 10, tr_1,
                                     self.indentation_base * 14,
                                     self.indentation_base * 16,
                                     self.indentation_base * 16, self.baV,
                                     self.indentation_base * 16,
                                     self.indentation_base * 16,
                                     self.indentation_base * 18, tr_3, self.field,
                                     self.indentation_base * 18, unary_exp_str,
                                     self.indentation_base * 18,
                                     self.indentation_base * 16, '__encoding__',
                                     self.indentation_base * 14,
                                     self.indentation_base * 8
                                     )

                body_no_abt = "%s %s = (\n" \
                              "%s %s,\n" \
                              "%s (\n" \
                              "%s (    \n" \
                              "%s    %s\n" \
                              "%s ?  ( \n" \
                              "%s  __CPROVER_set_field( &(%s), \"%s\", 1 ),\n" \
                              "%s  (typeof(%s))0 \n" \
                              "%s)\n" \
                              "%s : ( %s )\n" \
                              "%s )\n" \
                              "%s )\n" \
                              "%s )" % (self.indentation_base, tr_3,
                                        self.indentation_base * 10, tr_1,
                                        self.indentation_base * 14,
                                        self.indentation_base * 16,
                                        self.indentation_base * 16, self.baV,
                                        self.indentation_base * 16,
                                        self.indentation_base * 18, tr_3, self.field,
                                        self.indentation_base * 18, unary_exp_str,
                                        self.indentation_base * 18,
                                        self.indentation_base * 21, tr_4,
                                        self.indentation_base * 18,
                                        self.indentation_base * 14,
                                        self.indentation_base * 8
                                        )

                self.baV_track = None

            ###---BODY-END----####

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt, 'bounds_signed_list': bounds_failure_signed_list,
                    'bounds_unsigned_list': bounds_failure_unsigned_list, 'encoding': encoding_list}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['assignment'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'assignment': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE' or t_type == 'TRANSF_RW' or t_type == 'GET_OBJECT':
            self.utility.raiseException('This operation is not allowed!!')

        elif t_type == 'GET_VALUE':

            """
                                abstractable

                                [(unary_exp ass_op ass_expr, V )] ::= DECODE( [( unary_exp, E )]  )


                                not abstractable

                                [(unary_exp ass_op ass_expr, V )] ::= [( unary_exp, V )] )

                        """

            self.cGen.operationBit = 'GET_LVALUE'
            tr_1 = self.cGen.visit(unary_exp)
            tr_1 = self.utility.beautifyString(tr_1)

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(unary_exp)
            tr_2 = self.utility.beautifyString(tr_2)

            body_abt = '%s DECODE( %s )' % (self.indentation_base, tr_1)
            body_no_abt = '%s %s' % (self.indentation_base, tr_2)

            self.macro_dict[key] = unary_exp_str

            body = {'abt': body_abt, 'no_abt': body_no_abt}
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)

            self.object_list['assignment'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'assignment': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        else:
            self.utility.raiseException('This operation is not allowed!!')

    # Here i decide to use the following method as an end-point in order to not change the interface
    def getTR_postfixReference(self, t_type, id, postfix_exp, reference_type, sref, getMacro):

        if reference_type == '.':

            self.rules_counter["postfixReference_dot"] += 1
            body_postfix_reference_abt_dot = self.getTR_postfixReference_dot_abt(t_type, id, postfix_exp, sref,
                                                                                 getMacro)

            if '__PLACEHOLDER__' in body_postfix_reference_abt_dot:

                if getMacro:
                    self.macro_key.append(self.getMacroKey('postfixReference_dot', 1))
                else:
                    self.macro_key.append(self.getMacroKey('postfixReference_dot', 0))

                self.utility.printCustomMacro(body_postfix_reference_abt_dot)

                return self.utility.printMacro(getMacro, body_postfix_reference_abt_dot, 'yes')
            else:
                return self.utility.printMacro(getMacro, body_postfix_reference_abt_dot)

        else:

            self.rules_counter["postfixReference_arrow"] += 1
            body_postfix_reference_abt_arrow = self.getTR_postfixReference_arrow_abt(t_type, id, postfix_exp, sref,
                                                                                     getMacro)

            if '__PLACEHOLDER__' in body_postfix_reference_abt_arrow:

                if getMacro:
                    self.macro_key.append(self.getMacroKey('postfixReference_arrow', 1))
                else:
                    self.macro_key.append(self.getMacroKey('postfixReference_arrow', 0))

                self.utility.printCustomMacro(body_postfix_reference_abt_arrow)

                return self.utility.printMacro(getMacro, body_postfix_reference_abt_arrow, 'yes')
            else:
                return self.utility.printMacro(getMacro, body_postfix_reference_abt_arrow)

    def getTR_postfixReference_arrow_abt(self, t_type, id, postfix_exp, sref, getMacro):

        new_transformation = Transformation('postfixReference_arrow')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('postfixReference_arrow')

        if t_type == 'TRANSF_READ' or t_type == 'TRANSF_RW':

            ###---BODY-START----####

            self.cGen.operationBit = 'GET_OBJECT'
            tr_1 = self.cGen.visit(postfix_exp)

            flag_baL = self.baL_track

            self.cGen.operationBit = 'GET_LVALUE'
            tr_2 = self.cGen.visit(postfix_exp)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)

            """
                (
                                [( postfix_exp, V_O )],

                                (  false
                                   || baL
                                   || get_field( & ( [( postfix_exp, E )]->ID ) )
                                )
                                && (baV=1),

                                (void)0
               ) 
            """

            if flag_baL:

                body = '%s %s,\n' \
                       '%s (void)0' \
                       % (
                           self.indentation_base, tr_1,
                           self.indentation_base
                       )

                self.baV_track = 1
                self.baL_track = 1

            elif (flag_baL == 0):

                body = '%s %s,\n' \
                       '%s ( __CPROVER_get_field( &(%s->%s), "%s" ) && ( %s=1 ) )\n' \
                       '%s (void)0' \
                       % (
                           self.indentation_base, tr_1,
                           self.indentation_base, tr_2, id, self.field, self.baV,
                           self.indentation_base,
                       )
                self.baV_track = None
                self.baL_track = 1

            else:
                body = '%s %s,\n' \
                       '%s ( \n' \
                       '%s  || __CPROVER_get_field( &(%s->%s), "%s" )\n' \
                       '%s )\n' \
                       '%s && ( %s=1 ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base,
                          self.indentation_base * 2, tr_2, id, self.field,
                          self.indentation_base,
                          self.indentation_base, self.baV,
                          self.indentation_base)

                self.baL_track = None
                self.baV_track = None

            ###---BODY-END----####

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfixReference_arrow'] = obj_list

            return self.lparen + '\n' + body + '\n' + self.rparen


        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_OBJECT':

            ###---BODY-START----####

            self.cGen.operationBit = 'GET_OBJECT'
            tr_1 = self.cGen.visit(postfix_exp)

            tr_1 = self.utility.beautifyString(tr_1)

            """
             [( postfix_exp -> ID, V_W / V_O )] ::= [( postfix_exp, V_O )] 
            """

            body = '%s' % tr_1

            ###---BODY-END----####

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfixReference_arrow'] = obj_list

            return self.lparen + '\n' + body + '\n' + self.rparen

        elif t_type == 'TRANSF_RW':

            ###---BODY-START----####

            self.cGen.operationBit = 'GET_OBJECT'
            tr_1 = self.cGen.visit(postfix_exp)

            flag_baL = self.baL_track

            self.cGen.operationBit = 'GET_LVALUE'
            tr_2 = self.cGen.visit(postfix_exp)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)

            """

               (
                [( postfix_exp, V_O )], 
                baV = 0,

                (
                    (  false
                       || baL
                       || get_field( & ( [( postfix_exp, E )]->ID ) )
                    )
                    && (baV=1)
                ),
                (void)0
            ) 


            """

            if flag_baL:
                body = '%s %s,\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base
                          )

                self.baV_track = 1
                self.baL_track = 1

            elif (flag_baL == 0):

                body = '%s %s,\n' \
                       '%s %s = 0' \
                       '%s ( \n' \
                       '%s   __CPROVER_get_field( &(%s->%s), "%s" )\n' \
                       '%s )\n' \
                       '%s && ( %s=1 ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, self.baV,
                          self.indentation_base,
                          self.indentation_base * 2, tr_2, id, self.field,
                          self.indentation_base,
                          self.indentation_base, self.baV,
                          self.indentation_base)

                self.baV_track = None
                self.baL_track = 0

            else:

                body = '%s %s,\n' \
                       '%s %s = 0' \
                       '%s ( \n' \
                       '%s   0\n' \
                       '%s  || %s\n' \
                       '%s  || __CPROVER_get_field( &(%s->%s), "%s" )\n' \
                       '%s )\n' \
                       '%s && ( %s=1 ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, self.baV,
                          self.indentation_base,
                          self.indentation_base * 2,
                          self.indentation_base * 2, self.baL,
                          self.indentation_base * 2, tr_2, id, self.field,
                          self.indentation_base,
                          self.indentation_base, self.baV,
                          self.indentation_base)

                self.baV_track = None
                self.baL_track = None

            ###---BODY-END----####

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfixReference_arrow'] = obj_list

            return self.lparen + '\n' + body + '\n' + self.rparen


        elif t_type == 'GET_VALUE':

            """
            abstractable

            [( postfix_exp->ID, V )]   ::=  DECODE( [( postfix_exp, E )] -> ID )


            not abstractable

            [( postfix_exp->ID, V )]   ::=  [( postfix_exp, E )] -> ID ) 
            """

            self.cGen.operationBit = 'GET_LVALUE'
            tr_1 = self.cGen.visit(postfix_exp)

            key = 'postfixReference_arrow_%s' % (
                self.utility.macro_counter) if getMacro else 'postfixReference_arrow_%s' % (
                self.utility.local_macro_counter)

            self.macro_dict[key] = '%s->%s' % (sref, id)

            body_abt = '%s ((%s)DECODE( %s->%s ))' % (self.indentation_base, self.cast_bitvector, tr_1, id)
            body_no_abt = '%s %s->%s ' % (self.indentation_base, tr_1, id)

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfixReference_arrow'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'postfixReference_arrow': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        elif t_type == 'GET_LVALUE':

            """[(postfix_exp->ID, E)]: := [(postfix_exp, E)]->ID """

            self.cGen.operationBit = 'GET_LVALUE'
            tr_1 = self.cGen.visit(postfix_exp)

            body = '(%s->%s)' % (tr_1, id)
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfixReference_arrow'] = obj_list

            return body

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_postfixReference_dot_abt(self, t_type, id, postfix_exp, sref, getMacro):

        new_transformation = Transformation('postfixReference_dot')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('postfixReference_dot')

        if t_type == 'TRANSF_READ' or t_type == 'TRANSF_RW':

            ###---BODY-START----####

            self.cGen.operationBit = 'GET_OBJECT'
            tr_1 = self.cGen.visit(postfix_exp)

            flag_baL = self.baL_track

            self.cGen.operationBit = 'GET_LVALUE'
            tr_2 = self.cGen.visit(postfix_exp)



            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)

            """
                (
                                [( postfix_exp, V_O )],

                                (  false
                                   || baL
                                   || get_field( & ( [( postfix_exp, E )].ID ) )
                                )
                                && (baV=1),

                                (void)0
               ) 
            """

            if flag_baL:

                body = '%s %s,\n' \
                       '%s (void)0' \
                       % (
                           self.indentation_base, tr_1,
                           self.indentation_base
                       )
                self.baV_track = 1

            elif (flag_baL == 0):
                body = '%s %s,\n' \
                       '%s ( \n' \
                       '%s  __CPROVER_get_field( &(%s.%s), "%s" )\n' \
                       '%s )\n' \
                       '%s && ( %s=1 ),\n' \
                       '%s (void)0' \
                       % (
                           self.indentation_base, tr_1,
                           self.indentation_base,
                           self.indentation_base * 2, tr_2, id, self.field,
                           self.indentation_base,
                           self.indentation_base, self.baV,
                           self.indentation_base

                       )
                self.baV_track = None

            else:
                body = '%s %s,\n' \
                       '%s ( \n' \
                       '%s   0\n' \
                       '%s  || %s\n' \
                       '%s  || __CPROVER_get_field( &(%s.%s), "%s" )\n' \
                       '%s )\n' \
                       '%s && ( %s=1 ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base,
                          self.indentation_base * 2,
                          self.indentation_base * 2, self.baL,
                          self.indentation_base * 2, tr_2, id, self.field,
                          self.indentation_base,
                          self.indentation_base, self.baV,
                          self.indentation_base)

                self.baL_track = None
                self.baV_track = None

            ###---BODY-END----####

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfixReference_dot'] = obj_list

            return self.lparen + '\n' + body + '\n' + self.rparen


        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_OBJECT':

            ###---BODY-START----####

            self.cGen.operationBit = 'GET_OBJECT'
            tr_1 = self.cGen.visit(postfix_exp)

            tr_1 = self.utility.beautifyString(tr_1)

            """
             [( postfix_exp . ID, V_W / V_O )] ::= [( postfix_exp, V_O )] 
            """

            body = '%s' % tr_1

            ###---BODY-END----####

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfixReference_dot'] = obj_list

            return self.lparen + '\n' + body + '\n' + self.rparen

        elif t_type == 'TRANSF_RW':

            ###---BODY-START----####

            self.cGen.operationBit = 'GET_OBJECT'
            tr_1 = self.cGen.visit(postfix_exp)

            flag_baL = self.baL_track

            self.cGen.operationBit = 'GET_LVALUE'
            tr_2 = self.cGen.visit(postfix_exp)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)

            """

               (
                [( postfix_exp, V_O )], 
                baV = 0,

                (
                    (  false
                       || baL
                       || get_field( & ( [( postfix_exp, E )] . ID ) )
                    )
                    && (baV=1)
                ),
                (void)0
            ) 


            """

            if flag_baL:
                body = '%s %s,\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base
                          )

                self.baV_track = 1
                self.baL_track = 1

            elif (flag_baL == 0):

                body = '%s %s,\n' \
                       '%s %s = 0' \
                       '%s ( \n' \
                       '%s  || __CPROVER_get_field( &(%s.%s), "%s" )\n' \
                       '%s )\n' \
                       '%s && ( %s=1 ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, self.baV,
                          self.indentation_base,
                          self.indentation_base * 2, tr_2, id, self.field,
                          self.indentation_base,
                          self.indentation_base, self.baV,
                          self.indentation_base)

                self.baV_track = None
                self.baL_track = 0

            else:

                body = '%s %s,\n' \
                       '%s %s = 0' \
                       '%s ( \n' \
                       '%s   0\n' \
                       '%s  || %s\n' \
                       '%s  || __CPROVER_get_field( &(%s.%s), "%s" )\n' \
                       '%s )\n' \
                       '%s && ( %s=1 ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, self.baV,
                          self.indentation_base,
                          self.indentation_base * 2,
                          self.indentation_base * 2, self.baL,
                          self.indentation_base * 2, tr_2, id, self.field,
                          self.indentation_base,
                          self.indentation_base, self.baV,
                          self.indentation_base)

                self.baV_track = None
                self.baL_track = None

            ###---BODY-END----####

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfixReference_dot'] = obj_list

            return self.lparen + '\n' + body + '\n' + self.rparen


        elif t_type == 'GET_VALUE':

            """
            abstractable

            [( postfix_exp.ID, V )]   ::=  DECODE( [( postfix_exp, E )].ID )


            not abstractable

            [( postfix_exp.ID, V )]   ::=  [( postfix_exp, E )].ID ) 
            """

            self.cGen.operationBit = 'GET_LVALUE'
            tr_1 = self.cGen.visit(postfix_exp)


            key = 'postfixReference_dot_%s' % (
                self.utility.macro_counter) if getMacro else 'postfixReference_dot_%s' % (
                self.utility.local_macro_counter)

            self.macro_dict[key] = '%s.%s' % (sref, id)

            body_abt = '%s ( (%s)DECODE( %s.%s ) )' % (self.indentation_base, self.cast_bitvector, tr_1, id)
            body_no_abt = '%s %s.%s ' % (self.indentation_base, tr_1, id)

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfixReference_dot'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'postfixReference_dot': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        elif t_type == 'GET_LVALUE':

            """[(postfix_exp . ID, E)]: := [(postfix_exp, E)] . ID """

            self.cGen.operationBit = 'GET_LVALUE'
            tr_1 = self.cGen.visit(postfix_exp)

            body = '(%s.%s)' % (tr_1, id)
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['postfixReference_dot'] = obj_list

            return body

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_binary_exp_shortcut(self, t_type, binary_exp1, binary_exp2, binary_op, getMacro):

        if binary_op == '||':
            self.rules_counter["binary_exp_shortcut_or"] += 1
            return self.getTR_binary_exp_shortcut_or(t_type, binary_exp1, binary_exp2, getMacro)
        else:
            self.rules_counter["binary_exp_shortcut_and"] += 1
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

            ###---BODY-START----####

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(binary_exp1)

            flag_exp1 = self.baV_track

            self.cGen.operationBit = 'GET_VALUE'
            tr_3 = self.cGen.visit(binary_exp1)
            tr_3 = self.utility.beautifyString(tr_3)

            self.cGen.operationBit = 'TRANSF_READ'
            tr_2 = self.cGen.visit(binary_exp2)

            flag_exp2 = self.baV_track

            self.cGen.operationBit = 'GET_VALUE'
            tr_4 = self.cGen.visit(binary_exp2)
            tr_4 = self.utility.beautifyString(tr_4)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)

            """
            (
              [( binary_expression_1, V_R )],
              (val_phi = (
                               ( baV  ? nondetbool() 
                                      : [( binary_expression_1, V )] 
                               )
                            ||
                               (    ( [( binary_expression_2, V_R )], baV )
                                            ? (  nondetbool() )
                                            : ( [( binary_expression_2, V )] )
                               )
                         )
               ),

               baV=0,

               (void) 0
            )
            """

            if (flag_exp1 == 0) and (flag_exp2 == 0):

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s %s \n' \
                       '%s ||\n' \
                       '%s ( %s, %s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, tr_3,
                          self.indentation_base * 13,
                          self.indentation_base * 14, tr_2, tr_4,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )


            elif (flag_exp1) and (flag_exp2):

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s %s \n' \
                       '%s ||\n' \
                       '%s ( %s, %s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, self.nondetbool,
                          self.indentation_base * 13,
                          self.indentation_base * 14, tr_2, self.nondetbool,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )


            elif (flag_exp1 == 0) and flag_exp2:

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s %s \n' \
                       '%s ||\n' \
                       '%s ( %s, %s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, tr_3,
                          self.indentation_base * 13,
                          self.indentation_base * 14, tr_2, self.nondetbool,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )


            elif (flag_exp1) and (flag_exp2 == 0):

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s %s \n' \
                       '%s ||\n' \
                       '%s ( %s, %s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, self.nondetbool,
                          self.indentation_base * 13,
                          self.indentation_base * 14, tr_2, tr_4,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )


            elif flag_exp1 and (flag_exp2 is None):

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s %s\n' \
                       '%s ||\n' \
                       '%s (\n' \
                       '%s ( %s, %s )\n' \
                       '%s ? ( %s )\n' \
                       '%s : ( %s )\n' \
                       '%s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, self.nondetbool,
                          self.indentation_base * 13,
                          self.indentation_base * 14,
                          self.indentation_base * 16, tr_2, self.baV,
                          self.indentation_base * 18, self.nondetbool,
                          self.indentation_base * 18, tr_4,
                          self.indentation_base * 14,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )

            elif (flag_exp1 == 0) and (flag_exp2 is None):

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s %s\n' \
                       '%s ||\n' \
                       '%s (\n' \
                       '%s ( %s, %s )\n' \
                       '%s ? ( %s )\n' \
                       '%s : ( %s )\n' \
                       '%s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, tr_3,
                          self.indentation_base * 13,
                          self.indentation_base * 14,
                          self.indentation_base * 16, tr_2, self.baV,
                          self.indentation_base * 18, self.nondetbool,
                          self.indentation_base * 18, tr_4,
                          self.indentation_base * 14,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )

                """      
                elif ( flag_exp1 is None) and flag_exp2:

                self.cGen.operationBit = 'GET_VALUE'
                tr_3 = self.cGen.visit(binary_exp1)
                tr_3 = self.utility.beautifyString(tr_3)



                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s ( %s ? %s : %s )\n' \
                       '%s ||\n' \
                       '%s (\n' \
                       '%s ( %s, %s )\n' \
                       '%s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, self.baV, self.nondetbool, tr_3,
                          self.indentation_base * 13,
                          self.indentation_base * 14,
                          self.indentation_base * 16, tr_2, self.nondetbool,
                          self.indentation_base * 14,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )

            elif (flag_exp1 is None) and ( flag_exp2 == 0 ):

                self.cGen.operationBit = 'GET_VALUE'
                tr_3 = self.cGen.visit(binary_exp1)
                tr_3 = self.utility.beautifyString(tr_3)

                self.cGen.operationBit = 'GET_VALUE'
                tr_4 = self.cGen.visit(binary_exp2)
                tr_4 = self.utility.beautifyString(tr_4)

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s ( %s ? %s : %s )\n' \
                       '%s ||\n' \
                       '%s (\n' \
                       '%s ( %s, %s )\n' \
                       '%s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, self.baV, self.nondetbool, tr_3,
                          self.indentation_base * 13,
                          self.indentation_base * 14,
                          self.indentation_base * 16, tr_2, tr_4,
                          self.indentation_base * 14,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )
                          """

            else:

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s ( %s ? %s : %s )\n' \
                       '%s ||\n' \
                       '%s (\n' \
                       '%s ( %s, %s )\n' \
                       '%s ? ( %s )\n' \
                       '%s : ( %s )\n' \
                       '%s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, self.baV, self.nondetbool, tr_3,
                          self.indentation_base * 13,
                          self.indentation_base * 14,
                          self.indentation_base * 16, tr_2, self.baV,
                          self.indentation_base * 18, self.nondetbool,
                          self.indentation_base * 18, tr_4,
                          self.indentation_base * 14,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )

            self.baV_track = 0

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['binary_exp_shortcut_or'] = obj_list

            ###---BODY-END----####

            s = self.lparen + '\n' + body + '\n' + self.rparen
            return self.utility.printMacro(getMacro, s, b_exp1 + '||' + b_exp2)


        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE' or t_type == 'TRANSF_RW' or t_type == 'GET_OBJECT':
            self.utility.raiseException('This operation is not allowed!!')

        elif (t_type == 'GET_VALUE'):

            body = self.valphi_map['binary_exp_shortcut_or'].pop()
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['binary_exp_shortcut_or'] = obj_list
            return body

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_binary_exp_shortcut_and(self, t_type, binary_exp1, binary_exp2, getMacro):

        new_transformation = Transformation('binary_exp_shortcut_and')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('binary_exp_shortcut_and')

        cGen_orignal = CGenerator()
        b_exp1 = cGen_orignal.visit(binary_exp1)
        b_exp2 = cGen_orignal.visit(binary_exp2)

        if t_type == 'TRANSF_READ':

            ###---DECLARATION-START----####

            val_phi = self.val_phi.format(self.prefix, str(self.VAL_PHI))

            val_phi_definition = '_Bool %s=0;\n' % (val_phi)
            self.valphi_map['binary_exp_shortcut_and'].append(val_phi)

            declaration = val_phi_definition

            new_transformation.declaration = declaration
            new_transformation.declaration_index_val_phi = self.VAL_PHI

            self.VAL_PHI += 1

            ###---DECLARATION-END----####

            ###---BODY-START----####

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(binary_exp1)

            flag_exp1 = self.baV_track

            self.cGen.operationBit = 'GET_VALUE'
            tr_3 = self.cGen.visit(binary_exp1)
            tr_3 = self.utility.beautifyString(tr_3)

            self.cGen.operationBit = 'TRANSF_READ'
            tr_2 = self.cGen.visit(binary_exp2)

            flag_exp2 = self.baV_track

            self.cGen.operationBit = 'GET_VALUE'
            tr_4 = self.cGen.visit(binary_exp2)
            tr_4 = self.utility.beautifyString(tr_4)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)

            """

               (
                  [( binary_expression_1, V_R )],
                  ( val_phi = (
                                   ( baV  ? nondetbool() 
                                          : [( binary_expression_1, V )] 
                                   )
                                &&
                                   (    ( [( binary_expression_2, V_R )], baV )
                                                ? (  nondetbool() )
                                                : ( [( binary_expression_2, V )] )
                                   )
                             )
                   ),

                   baV=0,

                   (void) 0
                )
            )
            """

            if (flag_exp1 == 0) and (flag_exp2 == 0):

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s %s \n' \
                       '%s &&\n' \
                       '%s ( %s, %s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, tr_3,
                          self.indentation_base * 13,
                          self.indentation_base * 14, tr_2, tr_4,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )


            elif (flag_exp1) and (flag_exp2):

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s %s \n' \
                       '%s &&\n' \
                       '%s ( %s, %s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, self.nondetbool,
                          self.indentation_base * 13,
                          self.indentation_base * 14, tr_2, self.nondetbool,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )
            elif (flag_exp1 == 0) and flag_exp2:

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s %s \n' \
                       '%s &&\n' \
                       '%s ( %s, %s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, tr_3,
                          self.indentation_base * 13,
                          self.indentation_base * 14, tr_2, self.nondetbool,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )


            elif (flag_exp1) and (flag_exp2 == 0):

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s %s \n' \
                       '%s &&\n' \
                       '%s ( %s, %s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, self.nondetbool,
                          self.indentation_base * 13,
                          self.indentation_base * 14, tr_2, tr_4,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )


            elif flag_exp1 and (flag_exp2 is None):

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s %s\n' \
                       '%s &&\n' \
                       '%s (\n' \
                       '%s ( %s, %s )\n' \
                       '%s ? ( %s )\n' \
                       '%s : ( %s )\n' \
                       '%s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, self.nondetbool,
                          self.indentation_base * 13,
                          self.indentation_base * 14,
                          self.indentation_base * 16, tr_2, self.baV,
                          self.indentation_base * 18, self.nondetbool,
                          self.indentation_base * 18, tr_4,
                          self.indentation_base * 14,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )

            elif (flag_exp1 == 0) and (flag_exp2 is None):

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s %s\n' \
                       '%s &&\n' \
                       '%s (\n' \
                       '%s ( %s, %s )\n' \
                       '%s ? ( %s )\n' \
                       '%s : ( %s )\n' \
                       '%s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, tr_3,
                          self.indentation_base * 13,
                          self.indentation_base * 14,
                          self.indentation_base * 16, tr_2, self.baV,
                          self.indentation_base * 18, self.nondetbool,
                          self.indentation_base * 18, tr_4,
                          self.indentation_base * 14,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )

            else:

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s ( %s ? %s : %s )\n' \
                       '%s &&\n' \
                       '%s (\n' \
                       '%s ( %s, %s )\n' \
                       '%s ? ( %s )\n' \
                       '%s : ( %s )\n' \
                       '%s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s ( %s = 0 ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, self.baV, self.nondetbool, tr_3,
                          self.indentation_base * 13,
                          self.indentation_base * 14,
                          self.indentation_base * 16, tr_2, self.baV,
                          self.indentation_base * 18, self.nondetbool,
                          self.indentation_base * 18, tr_4,
                          self.indentation_base * 14,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base, self.baV,
                          self.indentation_base
                          )

            self.baV_track = 0

            """elif (flag_exp1 is None) and flag_exp2:

                self.cGen.operationBit = 'GET_VALUE'
                tr_3 = self.cGen.visit(binary_exp1)
                tr_3 = self.utility.beautifyString(tr_3)

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s ( %s ? %s : %s )\n' \
                       '%s &&\n' \
                       '%s (\n' \
                       '%s ( %s, %s )\n' \
                       '%s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, self.baV, self.nondetbool, tr_3,
                          self.indentation_base * 13,
                          self.indentation_base * 14,
                          self.indentation_base * 16, tr_2, self.nondetbool,
                          self.indentation_base * 14,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )

            elif (flag_exp1 is None) and ( flag_exp2 == 0):

                self.cGen.operationBit = 'GET_VALUE'
                tr_3 = self.cGen.visit(binary_exp1)
                tr_3 = self.utility.beautifyString(tr_3)

                self.cGen.operationBit = 'GET_VALUE'
                tr_4 = self.cGen.visit(binary_exp2)
                tr_4 = self.utility.beautifyString(tr_4)

                body = '%s %s,\n' \
                       '%s ( %s = (\n' \
                       '%s ( %s ? %s : %s )\n' \
                       '%s &&\n' \
                       '%s (\n' \
                       '%s ( %s, %s )\n' \
                       '%s )\n' \
                       '%s)\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi,
                          self.indentation_base * 14, self.baV, self.nondetbool, tr_3,
                          self.indentation_base * 13,
                          self.indentation_base * 14,
                          self.indentation_base * 16, tr_2, tr_4,
                          self.indentation_base * 14,
                          self.indentation_base * 13,
                          self.indentation_base,
                          self.indentation_base
                          )
            """

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['binary_exp_shortcut_and'] = obj_list

            ###---BODY-END----####

            s = self.lparen + '\n' + body + '\n' + self.rparen
            return self.utility.printMacro(getMacro, s, b_exp1 + '&&' + b_exp2)

        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE' or t_type == 'TRANSF_RW' or t_type == 'GET_OBJECT':
            self.utility.raiseException('This operation is not allowed!!')


        elif (t_type == 'GET_VALUE'):

            body = self.valphi_map['binary_exp_shortcut_and'].pop()
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['binary_exp_shortcut_and'] = obj_list

            return body

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_binary_exp_no_shortcut(self, t_type, binary_exp1, binary_exp2, binary_op, getMacro):

        self.rules_counter["binary_exp_no_shortcut"] += 1

        if t_type == 'TRANSF_READ':

            body_abt = self.getTR_binary_exp_no_shortcut_abt(t_type, binary_exp1, binary_exp2, binary_op, getMacro)

            if '__PLACEHOLDER__' in body_abt:

                if getMacro:
                    self.macro_key.append(self.getMacroKey('binary_exp_no_shortcut', 1))
                else:
                    self.macro_key.append(self.getMacroKey('binary_exp_no_shortcut', 0))

                self.utility.printCustomMacro(body_abt)
                return self.utility.printMacro(getMacro, body_abt, 'yes')
            else:
                return self.utility.printMacro(getMacro, body_abt)

        else:
            return self.getTR_binary_exp_no_shortcut_abt(t_type, binary_exp1, binary_exp2, binary_op, getMacro)


    def getTR_binary_exp_no_shortcut_abt(self, t_type, binary_exp1, binary_exp2, binary_op, getMacro):

        new_transformation = Transformation('binary_exp_no_shortcut')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('binary_exp_no_shortcut')

        cGen_orignal = CGenerator()
        b_exp1 = cGen_orignal.visit(binary_exp1)
        b_exp2 = cGen_orignal.visit(binary_exp2)


        if t_type == 'TRANSF_READ':

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(binary_exp1)

            flag_exp1 = self.baV_track

            self.cGen.operationBit = 'TRANSF_READ'
            tr_2 = self.cGen.visit(binary_exp2)

            flag_exp2 = self.baV_track

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)

            self.cGen.operationBit = 'GET_VALUE'
            tr_3 = self.cGen.visit(binary_exp1)
            self.cGen.operationBit = 'GET_VALUE'
            tr_4 = self.cGen.visit(binary_exp2)

            tr_3 = self.utility.beautifyString(tr_3)
            tr_4 = self.utility.beautifyString(tr_4)


            value = '%s %s %s' % (tr_3, binary_op, tr_4)
            self.valphi_map['binary_exp_no_shortcut'].append(value)

            bounds_failure_signed_list = []
            bounds_failure_unsigned_list = []

            for type in self.types:
                bounds_failure_signed_list.append(
                    "BOUNDS_FAILURE_SIGNED_%s( ( ((%s)%s) %s ((%s)%s) ) ) " % (
                    type, self.cast_bitvector, tr_3, binary_op, self.cast_bitvector, tr_4))
                bounds_failure_unsigned_list.append(
                    "BOUNDS_FAILURE_UNSIGNED_%s( ( ((%s)%s) %s ((%s)%s) ) ) " % (
                    type, self.cast_bitvector, tr_3, binary_op, self.cast_bitvector, tr_4))

            """
            [NO-ABT]
            (
                    [( binary_expression_1, V_R )], baV_1 = baV,

                    [( binary_expression_2, V_R )],

                    baV = ( baV || baV_1 ),

                    (void) 0
            )
            
            
            [ABT]
            (
                        [( binary_expression_1, V_R )], baV_1 = baV,
                
                        [( binary_expression_2, V_R )], 
                
                        baV = ( 
                                  ( baV || baV_1 ) 
                               || BOUNDS_FAILURE_TYPE(  
                                                        ( (BITVECTOR)[( binary_expression_1, V )] )
                                                              BINARY_OP 
                                                        ( (BITVECTOR)[( binary_expression_2, V )] )
                
                                                     ),
                
                        (void) 0
                )

            """

            if (flag_exp1 is None) and flag_exp2:

                body_no_abt = "%s %s,\n" \
                       "%s %s,\n" \
                       "%s (void) 0" % (
                           self.indentation_base, tr_1,
                           self.indentation_base, tr_2,
                           self.indentation_base
                       )

                body_abt = body_no_abt

                self.baV_track = 1

            elif (flag_exp1 is None) and (flag_exp2 == 0):

                # DECL

                bav_1 = self.bav_1.format(self.prefix, str(self.GENERIC_BA))

                bav_1_definition = '_Bool %s=0;\n' % (bav_1)

                declaration = bav_1_definition

                new_transformation.declaration = declaration
                new_transformation.declaration_index_generic_1 = self.GENERIC_BA

                self.GENERIC_BA += 1

                # END DECL

                body_no_abt = "%s %s,\n" \
                       "%s %s,\n" \
                       "%s ( %s = %s ),\n" \
                       "%s (void) 0" % (
                           self.indentation_base, tr_1,
                           self.indentation_base, tr_2,
                           self.indentation_base, self.baV, bav_1,
                           self.indentation_base
                       )

                self.baV_track = None

                body_abt = "%s %s,\n" \
                              "%s %s,\n" \
                              "%s ( %s = ( %s || %s  ) ),\n" \
                              "%s (void) 0" % (
                                  self.indentation_base, tr_1,
                                  self.indentation_base, tr_2,
                                  self.indentation_base, self.baV, bav_1, '__place__',
                                  self.indentation_base
                              )

            elif flag_exp1:

                body_no_abt = "%s %s,\n" \
                       "%s %s,\n" \
                       "%s (void) 0" % (
                           self.indentation_base, tr_1,
                           self.indentation_base, tr_2,
                           self.indentation_base
                       )
                self.baV_track = 1

                body_abt = body_no_abt

            elif (flag_exp1 == 0) and (flag_exp2):

                body_no_abt = "%s %s,\n" \
                       "%s %s,\n" \
                       "%s (void) 0" % (
                           self.indentation_base, tr_1,
                           self.indentation_base, tr_2,
                           self.indentation_base
                       )
                self.baV_track = 1

                body_abt = body_no_abt

            elif (flag_exp1 == 0) and (flag_exp2 is None):

                # DECL

                bav_1 = self.bav_1.format(self.prefix, str(self.GENERIC_BA))

                bav_1_definition = '_Bool %s=0;\n' % (bav_1)

                declaration = bav_1_definition

                new_transformation.declaration = declaration
                new_transformation.declaration_index_generic_1 = self.GENERIC_BA

                self.GENERIC_BA += 1

                # END DECL

                body_no_abt = "%s %s,\n" \
                       "%s %s,\n" \
                       "%s ( %s = %s ),\n" \
                       "%s (void) 0" % (
                           self.indentation_base, tr_1,
                           self.indentation_base, tr_2,
                           self.indentation_base, self.baV, bav_1,
                           self.indentation_base
                       )

                self.baV_track = None

                body_abt = "%s %s,\n" \
                              "%s %s,\n" \
                              "%s ( %s = ( %s || %s) ),\n" \
                              "%s (void) 0" % (
                                  self.indentation_base, tr_1,
                                  self.indentation_base, tr_2,
                                  self.indentation_base, self.baV, bav_1, '__place__',
                                  self.indentation_base
                              )


            else:

                # DECL

                bav_1 = self.bav_1.format(self.prefix, str(self.GENERIC_BA))

                bav_1_definition = '_Bool %s=0;\n' % (bav_1)

                declaration = bav_1_definition

                new_transformation.declaration = declaration
                new_transformation.declaration_index_generic_1 = self.GENERIC_BA

                self.GENERIC_BA += 1

                # END DECL

                body_abt = "%s %s,\n" \
                       "%s ( %s = %s ),\n" \
                       "%s %s,\n" \
                       "%s ( %s = ( %s || %s) || %s ) ,\n" \
                       "%s (void) 0" % (
                           self.indentation_base, tr_1,
                           self.indentation_base, bav_1, self.baV,
                           self.indentation_base, tr_2,
                           self.indentation_base, self.baV, self.baV, bav_1, '__place__',
                           self.indentation_base
                       )

                body_no_abt = "%s %s,\n" \
                              "%s %s,\n" \
                              "%s ( %s = %s ),\n" \
                              "%s (void) 0" % (
                                  self.indentation_base, tr_1,
                                  self.indentation_base, tr_2,
                                  self.indentation_base, self.baV, bav_1,
                                  self.indentation_base
                              )

                self.baV_track = None

            key = 'binary_exp_no_shortcut_%s' % (
                self.utility.macro_counter) if getMacro else 'binary_exp_no_shortcut_%s' % (
                self.utility.local_macro_counter)

            self.macro_dict[key] = '( %s ) %s ( %s ) ' % (b_exp1, binary_op, b_exp2)

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt, 'bounds_signed_list': bounds_failure_signed_list,
                    'bounds_unsigned_list': bounds_failure_unsigned_list}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['binary_exp_no_shortcut'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'binary_exp_no_shortcut': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE' or t_type == 'TRANSF_RW' or t_type == 'GET_OBJECT':
            self.utility.raiseException('This operation is not allowed!!')


        elif (t_type == 'GET_VALUE'):

            """
                [( binary_expression_1 BINARY_OP binary_expression_2, V )] ::= ( [( binary_expression_1, V )] BINARY_OP [( binary_expression_2, V )] )
            """

            #value_exp =  self.valphi_map['binary_exp_no_shortcut'].pop()

            try:
                self.cGen.operationBit = 'GET_VALUE'
                tr_3 = self.cGen.visit(binary_exp1)

                self.cGen.operationBit = 'GET_VALUE'
                tr_4 = self.cGen.visit(binary_exp2)

                tr_3 = self.utility.beautifyString(tr_3)
                tr_4 = self.utility.beautifyString(tr_4)

                body = '%s ( (%s) %s (%s) )' % (self.indentation_base, tr_3, binary_op, tr_4)

            except IndexError:
                value = self.valphi_map['binary_exp_no_shortcut'].pop()

                body = '%s %s' % (self.indentation_base, value)



            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['binary_exp_no_shortcut'] = obj_list

            #s = self.lparen + '\n' + body + '\n' + self.rparen
            return body

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_cond_exp(self, t_type, condition, branch_true, branch_false, getMacro):

        self.rules_counter["cond_exp"] += 1

        body_abt = self.getTR_cond_exp_abt(t_type, condition, branch_true, branch_false, getMacro)

        if '__PLACEHOLDER__' in body_abt:

            if getMacro:
                self.macro_key.append(self.getMacroKey('cond_exp', 1))
            else:
                self.macro_key.append(self.getMacroKey('cond_exp', 0))

            self.utility.printCustomMacro(body_abt)
            return self.utility.printMacro(getMacro, body_abt, 'yes')

        else:
            return self.utility.printMacro(getMacro, body_abt)

    def getTR_cond_exp_abt(self, t_type, condition, branch_true, branch_false, getMacro):

        self.rules_counter["cond_exp"] += 1

        new_transformation = Transformation('cond_exp')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('cond_exp')

        if t_type == 'TRANSF_READ':

            ###---DECLARATION-START----####

            val_cond = self.val_cond.format(self.prefix, str(self.GENERIC_VAL))
            valcond_definition = '_Bool %s=0;\n' % val_cond

            self.valphi_map['cond_exp'].append(val_cond)

            declaration = valcond_definition

            new_transformation.declaration = declaration
            new_transformation.declaration_index_generic_1 = self.GENERIC_VAL

            self.GENERIC_VAL += 1

            ###---DECLARATION-END----####

            ###---BODY-START----####

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(condition)

            flag_baV = self.baV_track

            self.cGen.operationBit = 'GET_VALUE'
            tr_4 = self.cGen.visit(condition)

            tr_4 = self.utility.beautifyString(tr_4)

            self.cGen.operationBit = 'TRANSF_READ'
            tr_2 = self.cGen.visit(branch_true)

            self.cGen.operationBit = 'TRANSF_READ'
            tr_3 = self.cGen.visit(branch_false)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)
            tr_3 = self.utility.beautifyString(tr_3)

            """

                (   
                    [(binary_exp, V_R)],

                    cond = ( baV ? nondetbool()  : ( [( binary_exp, V )] ) ),
                    ( cond
                          ?  [( expression, V_R )]
                          :  [( cond_exp,   V_R )] 
                    ),
                    (void)0
                )


            """

            if flag_baV:

                body = '%s %s,\n' \
                       '%s ( %s = %s ),\n' \
                       '%s ( %s\n' \
                       '%s ? ( %s, (void)0 )\n' \
                       '%s : ( %s, (void)0 )\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_cond, self.nondetbool,
                          self.indentation_base, val_cond,
                          self.indentation_base * 4, tr_2,
                          self.indentation_base * 4, tr_3,
                          self.indentation_base,
                          self.indentation_base)

                self.baV_track = 1


            elif flag_baV is None:

                body = '%s %s,\n' \
                       '%s %s = ( %s ? %s : %s ),\n' \
                       '%s ( %s\n' \
                       '%s ? ( %s, (void)0 )\n' \
                       '%s : ( %s, (void)0 )\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_cond, self.baV, self.nondetbool, tr_4,
                          self.indentation_base, val_cond,
                          self.indentation_base * 4, tr_2,
                          self.indentation_base * 4, tr_3,
                          self.indentation_base,
                          self.indentation_base)

                self.baV_track = None

            else:

                body = '%s %s,\n' \
                       '%s ( %s = %s ),\n' \
                       '%s ( %s\n' \
                       '%s ? ( %s, (void)0 )\n' \
                       '%s : ( %s, (void)0 )\n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_cond, tr_4,
                          self.indentation_base, val_cond,
                          self.indentation_base * 4, tr_2,
                          self.indentation_base * 4, tr_3,
                          self.indentation_base,
                          self.indentation_base)

                self.baV_track = 0

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['cond_exp'] = obj_list

            ###---BODY-END----####

            s = self.lparen + '\n' + body + '\n' + self.rparen
            return self.utility.printMacro(getMacro, s)

        elif t_type == 'GET_LVALUE' or t_type == 'TRANSF_WRITE':
            self.utility.raiseException('This operation is not allowed!!')

        elif t_type == 'GET_VALUE':

            """

           [+] ABT // if binary_exp is abstractable

            [( binary_exp ? expression : cond_exp, V )] ::= ( cond
                                                                   ?   ((BITVECTOR)[( expression, V )])
                                                                   :   ((BITVECTOR)[( cond_exp,   V )])
                                                            )
            
            [+] NO_ABT
            
             [( binary_exp ? expression : cond_exp, V )] ::= ( cond
                                                                   ?   [( expression, V )]
                                                                   :   [( cond_exp,   V )]
                                                             )                                              

            """

            self.cGen.operationBit = 'GET_VALUE'
            tr_1 = self.cGen.visit(branch_true)

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(branch_false)

            val_cond = self.valphi_map['cond_exp'].pop()

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)


            key = 'cond_exp_%s' % (
                self.utility.macro_counter) if getMacro else 'cond_exp_%s' % (
                self.utility.local_macro_counter)


            cGen_orignal = CGenerator()
            original_condition = cGen_orignal.visit(condition)
            self.macro_dict[key] = '%s' % (original_condition)

            body_abt = '%s ( %s ? ( ((%s)%s) ) : ( ((%s)%s) ) )' % (self.indentation_base, val_cond, self.cast_bitvector, tr_1, self.cast_bitvector, tr_2)
            body_no_abt = '%s ( %s ? ( %s ) : ( %s ) )' % (self.indentation_base, val_cond, tr_1 , tr_2)

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['cond_exp'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'cond_exp': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_if_statement(self, condition, original_exp):

        self.rules_counter["if_statement"] += 1

        new_transformation = Transformation('if_statement')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('if_statement')

        # logging.debug('method get_TR_if_statement is called')

        ###---BODY-START----####

        """
           if (
                 ( (    ( [( expression, V_R )] ) , 
                          baV 
                        )
                        ? nondetbool()
                        : [( expression, V )]
                 ) 
               ) 
                  [( pragmacomp_or_statement )];
        """

        self.cGen.operationBit = 'TRANSF_READ'
        tr_1 = self.cGen.visit(condition)
        tr_1 = self.utility.beautifyString(tr_1)

        flag_baV = self.baV_track

        if flag_baV is None:

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(condition)
            tr_2 = self.utility.beautifyString(tr_2)

            body = '( ( %s, %s ) ? %s : %s )' % (tr_1, self.baV, self.nondetbool, tr_2)

            self.baV_track = None

        elif flag_baV:

            body = '(  %s, %s  )' % (tr_1, self.nondetbool)

            self.baV_track = 1

        else:

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(condition)
            tr_2 = self.utility.beautifyString(tr_2)

            body = '(  %s, %s  )' % (tr_1, tr_2)

            self.baV_track = 0

        ###---BODY-END----####

        new_transformation.body = body
        new_transformation.t_type = ''
        obj_list.append(new_transformation)
        self.object_list['if_statement'] = obj_list

        s = body + '\n'

        return self.utility.printMacro(1, s, original_exp)

    def __getTR_unaryOP_ampersand_castExp(self, t_type, cast_exp, new_transformation, getMacro):

        obj_list = self.object_list.get('&_castExp')

        if t_type == 'TRANSF_READ':

            ###---BODY-START----####

            """

                  (
                        [( cast_exp, V_O )], 
                        baV = baL,           
                        (void) 0
                    )


            """

            self.cGen.operationBit = 'GET_OBJECT'

            flag_baL = self.baV_track

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(cast_exp)
            tr_1 = self.utility.beautifyString(tr_1)

            if flag_baL:

                body = '%s %s,\n' \
                       '%s (void)0' % \
                       (
                           self.indentation_base, tr_1,
                           self.indentation_base

                       )

                self.baL_track = 1
                self.baV_track = 1


            elif (flag_baL == 0):

                body = '%s %s,\n' \
                       '%s (void)0' % \
                       (
                           self.indentation_base, tr_1,
                           self.indentation_base
                       )

                self.baV_track = 0
                self.baL_track = 0

            else:
                body = '%s %s,\n' \
                       '%s ( %s = %s ),\n' \
                       '%s (void)0' % \
                       (
                           self.indentation_base, tr_1,
                           self.indentation_base, self.baV, self.baL,
                           self.indentation_base
                       )

                self.baV_track = None
                self.baL_track = None

            ###---BODY-END----####

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['&_castExp'] = obj_list

            s = self.lparen + '\n' + body + '\n' + self.rparen
            return self.utility.printMacro(getMacro, s)

        elif t_type == 'GET_LVALUE' or t_type == 'TRANSF_WRITE' or t_type == 'GET_OBJECT' or t_type == 'TRANSF_RW':

            self.utility.raiseException('This operation is not allowed!!')

        elif t_type == 'GET_VALUE':

            # [( & cast_exp, V )]  ::= & [( cast_exp, E )]

            self.cGen.operationBit = 'GET_LVALUE'
            tr_1 = self.cGen.visit(cast_exp)
            tr_1 = self.utility.beautifyString(tr_1)

            body = " &(%s)" % (tr_1)
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['&_castExp'] = obj_list

            return body

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_plus_minus_tilde_castExp(self, t_type, cast_exp, unary_op, getMacro):

        operation = "%s_castExp" % unary_op
        self.rules_counter[operation] += 1

        if t_type == 'TRANSF_READ' and unary_op == '-':

            body_abt = self.getTR_plus_minus_tilde_castExp_abt(t_type, cast_exp, unary_op, getMacro)

            if '__PLACEHOLDER__' in body_abt:

                if getMacro:
                    self.macro_key.append(self.getMacroKey(operation, 1))
                else:
                    self.macro_key.append(self.getMacroKey(operation, 0))


                self.utility.printCustomMacro(body_abt)
                return self.utility.printMacro(getMacro, body_abt, 'yes')
            else:
                return self.utility.printMacro(getMacro, body_abt)

        else:
            return self.getTR_plus_minus_tilde_castExp_abt(t_type, cast_exp, unary_op, getMacro)


    def getTR_plus_minus_tilde_castExp_abt(self, t_type, cast_exp, unary_op, getMacro):

        operation_type = '%s_castExp' % (unary_op)

        self.rules_counter[operation_type] += 1

        new_transformation = Transformation(operation_type)
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get(operation_type)

        if t_type == 'TRANSF_READ':

            ###---BODY-START----####

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(cast_exp)
            tr_1 = self.utility.beautifyString(tr_1)

            """
                    Only when [( cast_exp, V )] is abstractable and signed

                    [( -cast_exp, V_R )] ::=   ( 
                                                  [( cast_exp, V_R)], 
                                                  ( MIN_TYPE( [( cast_exp, V )] ) && ( baV = 1) )  
                                               )
            
            """
            if unary_op == '-':

                self.cGen.operationBit = 'GET_VALUE'
                tr_2 = self.cGen.visit(cast_exp)
                tr_2 = self.utility.beautifyString(tr_2)

                min_list = []

                for type in self.types:
                    min_list.append("MIN_%s( (%s) ) " % (type, tr_2))

                body_abt = '%s ( %s, ( %s && ( %s = 1) ) )' % (self.indentation_base * 2, tr_1, '__place__',self.baV)
                body_no_abt = '%s ( %s, (void)0 ) ' % (self.indentation_base * 2, tr_1)

                body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
                body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen



                body = {'abt': body_abt, 'no_abt': body_no_abt, 'min_list': min_list}
                new_transformation.body = body
                new_transformation.t_type = t_type
                obj_list.append(new_transformation)
                self.object_list[operation_type] = obj_list

                key = '%s_%s' % ( operation_type,
                    self.utility.macro_counter) if getMacro else '%s_%s' % ( operation_type,
                    self.utility.local_macro_counter)

                original_visitor = CGenerator()
                original_castExp = original_visitor.visit(cast_exp)
                self.macro_dict[key] = original_castExp

                if getMacro:
                    placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
                else:
                    placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

                new_object = {operation_type: new_transformation}
                self.placeholder_object[placeholder_key]=new_object

                return placeholder_key


            else:
                # [( unary_OP cast_exp, V_R )] ::=   ( [( cast_exp, V_R)],  (void) 0 )

                body = '%s ( %s, (void)0 ) ' % (self.indentation_base * 2, tr_1)

                new_transformation.body = body
                new_transformation.t_type = t_type
                obj_list.append(new_transformation)
                self.object_list[operation_type] = obj_list

                ###---BODY-END----####

                s = self.lparen + '\n' + body + '\n' + self.rparen
                return self.utility.printMacro(getMacro, s)

        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE' or t_type == 'GET_OBJECT' or t_type == 'TRANSF_RW':
            self.utility.raiseException('This operation is not allowed!!')

        elif (t_type == 'GET_VALUE'):

            # unary_OP [(cast_exp, V)]

            self.cGen.operationBit = 'GET_VALUE'
            tr_1 = self.cGen.visit(cast_exp)
            tr_1 = self.utility.beautifyString(tr_1)

            body = '( %s %s %s )' % (self.indentation_base * 2, unary_op, tr_1)
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list[operation_type] = obj_list

            return body

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_not_castExp(self, t_type, cast_exp, getMacro):

        body_abt = self.getTR_not_castExp_abt(t_type, cast_exp, getMacro)

        if '__PLACEHOLDER__' in body_abt:

            if getMacro:
                self.macro_key.append(self.getMacroKey('not_castExp', 1))
            else:
                self.macro_key.append(self.getMacroKey('not_castExp', 0))

            self.utility.printCustomMacro(body_abt)
            return self.utility.printMacro(getMacro, body_abt, 'yes')

        else:
            return self.utility.printMacro(getMacro, body_abt)

    def getTR_not_castExp_abt(self, t_type, cast_exp, getMacro):

        new_transformation = Transformation('not_castExp')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('not_castExp')

        self.rules_counter['not_castExp'] += 1

        if t_type == 'TRANSF_READ':

            ###---DECLARATION-START----####

            val_phi = self.val_phi.format(self.prefix, str(self.VAL_PHI))

            val_phi_definition = '_Bool %s=0;\n' % (val_phi)

            self.valphi_map['not_castExp'].append(val_phi)

            declaration = val_phi_definition

            new_transformation.declaration = declaration
            new_transformation.declaration_index_val_phi = self.VAL_PHI

            self.VAL_PHI += 1

            ###---DECLARATION-END----####

            ###---BODY-START----####

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(cast_exp)
            tr_1 = self.utility.beautifyString(tr_1)

            flag_baV = self.baV_track

            """
            [+] ABT

                            (
                                [( cast_exp, V_R )], 
                            
                                val_phi = ( baV
                                               ?  ( baV=0, nondetbool() )            
                                               
                                               :  ! ((BITVECTOR)[( cast_exp, V)])
                                          ),
                                (void)0
                            )
                            
                            ---------------------------
                            
                            [+] NO_ABT
                            
                            
                            (
                                [( cast_exp, V_R )], 
                            
                                val_phi = ( baV
                                               ?  ( baV=0, nondetbool() )            
                                               
                                               :  ! [( cast_exp, V)]
                                          ),
                                (void)0
                            )
            )
            """

            if flag_baV is None:

                self.cGen.operationBit = 'GET_VALUE'
                tr_2 = self.cGen.visit(cast_exp)
                tr_2 = self.utility.beautifyString(tr_2)

                body_abt = '%s %s,\n' \
                       '%s %s = ( ( %s )\n' \
                       '%s ? ( %s = 0, %s)\n' \
                       '%s : !((%s)(%s)) \n' \
                       '%s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi, self.baV,
                          self.indentation_base * 16, self.baV, self.nondetbool,
                          self.indentation_base * 16, self.cast_bitvector, tr_2,
                          self.indentation_base * 12,
                          self.indentation_base
                          )

                self.baV_track = None

                body_no_abt = '%s %s,\n' \
                           '%s %s = ( ( %s )\n' \
                           '%s ? ( %s = 0, %s)\n' \
                           '%s : !(%s) \n' \
                           '%s ),\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_1,
                              self.indentation_base, val_phi, self.baV,
                              self.indentation_base * 16, self.baV, self.nondetbool,
                              self.indentation_base * 16, tr_2,
                              self.indentation_base * 12,
                              self.indentation_base
                              )

            elif flag_baV:

                body_abt = '%s %s,\n' \
                       '%s ( %s = %s ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi, self.nondetbool,
                          self.indentation_base
                          )
                self.baV_track = 0
                body_no_abt = body_abt

            else:

                self.cGen.operationBit = 'GET_VALUE'
                tr_2 = self.cGen.visit(cast_exp)
                tr_2 = self.utility.beautifyString(tr_2)

                body_abt = '%s %s,\n' \
                       '%s ( %s = !((%s)(%s)) ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, val_phi, self.cast_bitvector, tr_2,
                          self.indentation_base
                          )
                self.baV_track = 0

                body_no_abt = '%s %s,\n' \
                           '%s ( %s = (!%s) ),\n' \
                           '%s (void)0' \
                           % (self.indentation_base, tr_1,
                              self.indentation_base, val_phi, tr_2,
                              self.indentation_base
                              )


            key = 'not_castExp_%s' % (
                self.utility.macro_counter) if getMacro else 'not_castExp_%s' % (
                self.utility.local_macro_counter)

            original_vistor = CGenerator()
            original_castExp = original_vistor.visit(cast_exp)
            self.macro_dict[key] = original_castExp

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt}
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['not_castExp'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'not_castExp': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE' or t_type == 'GET_OBJECT' or t_type == 'TRANSF_RW':
            self.utility.raiseException('This operation is not allowed!!')


        elif (t_type == 'GET_VALUE'):

            body = self.valphi_map['not_castExp'].pop()
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['not_castExp'] = obj_list

            return body

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_sizeofUnaryexp(self, t_type, unaryExp, original_exp, getMacro):

        self.rules_counter['sizeof_unaryExp'] += 1

        new_transformation = Transformation('sizeof_unaryExp')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('sizeof_unaryExp')

        if t_type == 'TRANSF_READ':

            ###---BODY-START----####

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(unaryExp)

            tr_1 = self.utility.beautifyString(tr_1)

            """
            [( size_of(unary_exp), V_R )] ::= [( unary_exp, V_R)]

            """

            body = '( %s %s )' % (self.indentation_base, tr_1)

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['sizeof_unaryExp'] = obj_list

            ###---BODY-END----####

            s = self.lparen + '\n' + body + '\n' + self.rparen

            return self.utility.printMacro(getMacro, s, original_exp)

        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE' or t_type == 'TRANSF_RW' or t_type == 'GET_OBJECT':
            self.utility.raiseException('This operation is not allowed!!')

        elif (t_type == 'GET_VALUE'):

            # [( size_of(unary_exp), V )] ::= size_of( [( unary_exp, V)] )

            self.cGen.operationBit = 'GET_VALUE'
            tr_1 = self.cGen.visit(unaryExp)

            tr_1 = self.utility.beautifyString(tr_1)

            body = 'size_of( %s )' % tr_1
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['sizeof_unaryExp'] = obj_list

            s = self.lparen + '\n' + body + '\n' + self.rparen

            return self.utility.printMacro(getMacro, s, original_exp)

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_constant(self, t_type, constant, getMacro):

        new_transformation = Transformation('constant')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('constant')

        if t_type == 'TRANSF_READ':

            ###---BODY-START----####

            """
               [( CONSTANT, V_R )] ::=  ( (baV = 0), (void)0 )

            """

            self.baV_track = 0

            body = '%s (void)0 ' % (self.indentation_base)

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['constant'] = obj_list

            self.constant_number += 1

            ###---BODY-END----####

            s = self.lparen + '\n' + body + '\n' + self.rparen
            return self.utility.printMacro(getMacro, s, constant)

        elif t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE' or t_type == 'GET_OBJECT' or t_type == 'TRANSF_RW':

            self.utility.raiseException('This operation is not allowed!!')

        elif (t_type == 'GET_VALUE'):

            # [(CONSTANT, V)]: := CONSTANT

            body = '%s' % (str(constant))
            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['constant'] = obj_list

            return body

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_typename_castExp(self, t_type, typename, castExp, getMacro):

        self.rules_counter['typename_castExp'] += 1

        new_transformation = Transformation('typename_castExp')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('typename_castExp')

        if t_type == 'TRANSF_READ':

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(castExp)
            tr_1 = self.utility.beautifyString(tr_1)

            """
            [( (Type_name) cast_exp, V_R )] ::= [(cast_exp, V_R )]

            """
            body = '%s ( %s )' % (self.indentation_base, tr_1)

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['typename_castExp'] = obj_list

            ###---BODY-END----####

            s = self.lparen + '\n' + body + '\n' + self.rparen
            return self.utility.printMacro(getMacro, s)

        elif (t_type == 'GET_VALUE'):

            # [( (Type_name) cast_exp, V)] ::= (Type_name)[( cast_exp, V)]

            self.cGen.operationBit = 'GET_VALUE'
            tr_1 = self.cGen.visit(castExp)
            tr_1 = self.utility.beautifyString(tr_1)

            body = '%s ( %s %s  )' % (self.indentation_base, typename, tr_1)

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['typename_castExp'] = obj_list

            s = self.lparen + '\n' + body + '\n' + self.rparen
            return self.utility.printMacro(getMacro, s)

        # t_type == 'TRANSF_WRITE' or t_type == 'GET_LVALUE':
        else:
            self.utility.raiseException('This operation is not allowed!!')

    def __getTR_unaryOP_star_castExp_abt(self, t_type, cast_exp, new_transformation, getMacro):

        # Let's get the orginal exp
        cGen_orignal = CGenerator()
        cast_exp_string = cGen_orignal.visit(cast_exp)
        obj_list = self.object_list.get('*_castExp')

        unary_op = '*'

        if t_type == 'TRANSF_READ':

            ###---BODY-START----####

            """

                (
                    [( cast_exp, V_R )], baL=baV,

                    ( baV ||   ( baV = getfield( [( cast_exp, V )]) ) ),

                    (void) 0

                )

            """
            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(cast_exp)

            flag_baV = self.baV_track

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(cast_exp)

            tr_1 = self.utility.beautifyString(tr_1)
            tr_2 = self.utility.beautifyString(tr_2)

            if flag_baV:

                body = '%s %s,\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base)

                self.baV_track = 1

            elif (flag_baV == 0):

                body = '%s %s,\n' \
                       '%s ( %s = __CPROVER_get_field( (%s), "%s" ) ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, self.baV, tr_2, self.field,
                          self.indentation_base)

                self.baV_track = None
                self.baL_track = 0

            else:

                body = '%s %s,\n' \
                       '%s ( %s = __CPROVER_get_field( (%s), "%s" ) ),\n' \
                       '%s (void)0' \
                       % (self.indentation_base, tr_1,
                          self.indentation_base, self.baV, tr_2, self.field,
                          self.indentation_base)

                self.baV_track = None

            ###---BODY-END----####

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['*_castExp'] = obj_list

            s = self.lparen + '\n' + body + '\n' + self.rparen
            return s

        elif t_type == 'TRANSF_WRITE':

            ###---BODY-START----####

            """
            (
                [( cast_exp, V_R )], baL=baV,

                __CPROVER_assert(! baV, "ERROR: WRITING INTO A LOCATION BY DEREFERENCING AN ABSTRACTED ADDRESS"),

                (void) 0
            )
            """

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(cast_exp)
            tr_1 = self.utility.beautifyString(tr_1)

            if self.baV_track:
                body = '%s %s,\n' \
                       '%s __CPROVER_assert(0, "ERROR: WRITING INTO A LOCATION BY DEREFERENCING AN ABSTRACTED ADDRESS"),\n' \
                       '%s (void)0' % \
                       (
                           self.indentation_base, tr_1,
                           self.indentation_base,
                           self.indentation_base
                       )
                self.baL_track = 1
                self.baV_track = 1

            elif self.baV_track == None:

                body = '%s %s,\n' \
                       '%s __CPROVER_assert(! %s, "ERROR: WRITING INTO A LOCATION BY DEREFERENCING AN ABSTRACTED ADDRESS"),\n' \
                       '%s (void)0' % \
                       (
                           self.indentation_base, tr_1,
                           self.indentation_base, self.baV,
                           self.indentation_base
                       )
                self.baL_track = 0
                self.baV_track = 0

            else:
                body = '%s %s,\n' \
                       '%s (void)0' % \
                       (
                           self.indentation_base, tr_1,
                           self.indentation_base
                       )
                self.baL_track = 0
                self.baV_track = 0

            ###---BODY-END----####

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['*_castExp'] = obj_list
            s = self.lparen + '\n' + body + '\n' + self.rparen
            return s

        elif t_type == 'TRANSF_RW':

            """
                (
                    [( cast_exp, V_R )], baL=baV,

                    __CPROVER_assert(! baV, "ERROR: WRITING INTO A LOCATION BY DEREFERENCING AN ABSTRACTED ADDRESS"),

                    baV = getfield( [( cast_exp, V )]),

                    (void) 0

                )
            """

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(cast_exp)

            flag_baV = self.baV_track

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(cast_exp)

            tr_2 = self.utility.beautifyString(tr_2)

            if flag_baV:

                body = '%s %s,\n' \
                       '%s __CPROVER_assert(0, "ERROR: WRITING INTO A LOCATION BY DEREFERENCING AN ABSTRACTED ADDRESS"),\n' \
                       '%s (void)0' % \
                       (
                           self.indentation_base, tr_1,
                           self.indentation_base,
                           self.indentation_base
                       )
                self.baL_track = 1
                self.baV_track = 1

            elif flag_baV == None:

                body = '%s %s,\n' \
                       '%s ( %s = %s ),\n' \
                       '%s __CPROVER_assert(! %s, "ERROR: WRITING INTO A LOCATION BY DEREFERENCING AN ABSTRACTED ADDRESS"),\n' \
                       '%s ( %s = __CPROVER_get_field( %s, %s) ),\n' \
                       '%s (void)0' % \
                       (
                           self.indentation_base, tr_1,
                           self.indentation_base, self.baL, self.baV,
                           self.indentation_base, self.baV,
                           self.indentation_base, self.baV, tr_2, self.field,
                           self.indentation_base
                       )

                self.baV_track = None

            else:

                body = '%s %s,\n' \
                       '%s ( %s = __CPROVER_get_field( %s, %s) ),\n' \
                       '%s (void)0' % \
                       (
                           self.indentation_base, tr_1,
                           self.indentation_base, self.baV, tr_2, self.field,
                           self.indentation_base
                       )

                self.baL_track = 0
                self.baV_track = None

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['*_castExp'] = obj_list
            s = self.lparen + '\n' + body + '\n' + self.rparen
            return s


        elif t_type == 'GET_OBJECT':
            """
            (
                [( cast_exp, V_R )], baL=baV,

                (void) 0
            )
            """

            self.cGen.operationBit = 'TRANSF_READ'
            tr_1 = self.cGen.visit(cast_exp)

            flag_baV = self.baV_track

            tr_1 = self.utility.beautifyString(tr_1)

            if flag_baV is None:

                body = '%s %s,\n' \
                       '%s ( %s = %s ),\n' \
                       '%s (void)0' % \
                       (
                           self.indentation_base, tr_1,
                           self.indentation_base, self.baL, self.baV,
                           self.indentation_base
                       )
                self.baV_track = None
                self.baL_track = None

            else:

                if flag_baV:
                    self.baV_track = 1
                    self.baL_track = 1
                else:
                    self.baV_track = 0
                    self.baL_track = 0

                body = '%s %s,\n' \
                       '%s (void)0' % \
                       (
                           self.indentation_base, tr_1,
                           self.indentation_base
                       )

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['*_castExp'] = obj_list
            s = self.lparen + '\n' + body + '\n' + self.rparen
            return s


        elif t_type == 'GET_LVALUE':

            """
              [( * cast_exp, E )]  ::= * [( cast_exp, V )]
            """

            self.cGen.operationBit = 'GET_VALUE'
            tr_1 = self.cGen.visit(cast_exp)
            tr_1 = self.utility.beautifyString(tr_1)

            body = '( %s(%s) )' % (unary_op, tr_1)

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['*_castExp'] = obj_list

            return body

        elif t_type == 'GET_VALUE':

            self.cGen.operationBit = 'GET_VALUE'
            tr_1 = self.cGen.visit(cast_exp)
            tr_1 = self.utility.beautifyString(tr_1)

            """ 
              abstractable

              [( * cast_exp, V )]  ::= DECODE( * [( cast_exp, V )] ) 


              not_abstractable

              [( * cast_exp, V )]  ::= * [( cast_exp, V )] 

            """

            key = '*_castExp_%s' % (
                self.utility.macro_counter) if getMacro else '*_castExp_%s' % (
                self.utility.local_macro_counter)

            self.macro_dict[key] = '*%s' % (cast_exp_string)

            body_abt = '%s DECODE( *%s) ' % (self.indentation_base, tr_1)
            body_no_abt = '%s *%s ' % (self.indentation_base, tr_1)

            body_abt = self.lparen + '\n' + body_abt + '\n' + self.rparen
            body_no_abt = self.lparen + '\n' + body_no_abt + '\n' + self.rparen

            body = {'abt': body_abt, 'no_abt': body_no_abt}

            new_transformation.body = body
            new_transformation.t_type = t_type
            obj_list.append(new_transformation)
            self.object_list['*_castExp'] = obj_list

            if getMacro:
                placeholder_key = '__PLACEHOLDER__EXP_%s' % self.utility.macro_counter
            else:
                placeholder_key = '__PLACEHOLDER__LOCAL_EXP_%s' % self.utility.local_macro_counter

            new_object = {'*_castExp': new_transformation}
            self.placeholder_object[placeholder_key]=new_object

            return placeholder_key

        else:
            self.utility.raiseException('This operation is not allowed!!')

    def getTR_unaryOP_castExp(self, t_type, cast_exp, unary_op, getMacro):

        operation_type = '%s_castExp' % unary_op
        self.rules_counter[operation_type] += 1
        new_transformation = Transformation(operation_type)

        # logging.debug('method getTR_unaryOP_castExp is called with bit: %s' % t_type)

        if unary_op == '*':
            return self.__getTR_unaryOP_star_castExp(t_type, cast_exp, new_transformation, getMacro)
        elif unary_op == '&':
            return self.__getTR_unaryOP_ampersand_castExp(t_type, cast_exp, new_transformation, getMacro)

        # Gestire anche gli altri unary_op

    def __getTR_unaryOP_star_castExp(self, t_type, cast_exp, new_transformation, getMacro):

        body_unaryOP_star_castExp_abt = self.__getTR_unaryOP_star_castExp_abt(t_type, cast_exp, new_transformation,
                                                                              getMacro)

        if '__PLACEHOLDER__' in body_unaryOP_star_castExp_abt:

            if getMacro:
                self.macro_key.append(self.getMacroKey('*_castExp', 1))
            else:
                self.macro_key.append(self.getMacroKey('*_castExp', 0))

            self.utility.printCustomMacro(body_unaryOP_star_castExp_abt)

            return self.utility.printMacro(getMacro, body_unaryOP_star_castExp_abt, 'yes')
        else:
            return self.utility.printMacro(getMacro, body_unaryOP_star_castExp_abt)

    def getTR_assert_call(self, exp):

        self.rules_counter['assert_statement'] += 1

        new_transformation = Transformation('assert_statement')
        new_transformation.body = ''
        new_transformation.declaration = ''
        obj_list = self.object_list.get('assert_statement')

        """
            [(EXP, V_R)],
            ba_assert = ( baV ? 0: [( EXP, V)] ),
            assert (ba_assert)
        """

        self.cGen.operationBit = 'TRANSF_READ'
        tr_1 = self.cGen.visit(exp)
        tr_1 = self.utility.beautifyString(tr_1)

        flag_baV = self.baV_track



        if flag_baV == 1:
            body = '%s %s,\n' \
                   '%s assert(0)' % \
                   (
                       self.indentation_base, tr_1,
                       self.indentation_base,
                   )


        elif flag_baV == 0:

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(exp)
            tr_2 = self.utility.beautifyString(tr_2)

            body = '%s %s,\n' \
                   '%s assert(%s)' % \
                   (
                       self.indentation_base, tr_1,
                       self.indentation_base, tr_2
                   )
            self.baV_track = 0

        else:

            self.cGen.operationBit = 'GET_VALUE'
            tr_2 = self.cGen.visit(exp)
            tr_2 = self.utility.beautifyString(tr_2)

            body = '%s %s,\n' \
                   '%s ( %s = ( %s ? 0 : %s ) ),\n' \
                   '%s assert(%s)' % \
                   (
                       self.indentation_base, tr_1,
                       self.indentation_base, self.ba_assert, self.baV, tr_2,
                       self.indentation_base, self.ba_assert
                   )

            self.baV_track = None

        new_transformation.body = body
        new_transformation.t_type = ''
        obj_list.append(new_transformation)
        self.object_list['assert_statement'] = obj_list
        s = self.lparen + '\n' + body + '\n' + self.rparen
        return self.utility.printMacro(1, s)

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

            s = self.lparen + '\n' + body + '\n' + self.rparen
            return self.utility.printMacro(getMacro, s)


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
            # return self.utility.no_declaration
        else:
            decl_string = self.utility.declaration_type % self.utility.counter_declaration
            return self.utility.printDeclaration(decl_string, declaration)

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

    def getLocal(self, key):
        return self.macro_dict[key]

    def getMacroKey(self, exp, bit):
        if bit:
            return exp + '_%s' % self.utility.macro_counter
        else:
            return exp + '_%s' % self.utility.local_macro_counter

    # follow the order of max and min list when returning values

    # ['MAX_INT( ( LOCAL_EXP_5 ) ) ', 'MAX_CHAR( ( LOCAL_EXP_5 ) ) ', 'MAX_LONG_INT( ( LOCAL_EXP_5 ) ) ', 'MAX_SHORT( ( LOCAL_EXP_5 ) ) ', 'MAX_LONG_LONG( ( LOCAL_EXP_5 ) ) ']

    def getTypeMatch(self, type):

        if type == 'unsigned char':
            return 6
        elif type == 'char':
            return 1
        elif type == 'short':
            return 3
        if type == 'unsigned short':
            return 8
        elif type == 'int':
            return 0
        elif type == 'unsigned int':
            return 5
        elif type == 'long int':
            return 2
        elif type == 'unsigned long int':
            return 7
        elif type == 'long long':
            return 4
        elif type == 'unsigned long long':
            return 9
        else:
            return 10
