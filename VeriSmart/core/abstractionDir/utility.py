import logging
import os
import string
from os import path
from os import remove


class Utility(object):

    def __init__(self, encoding, bit_size, writeMacroFile=0, macroFileName='macro_plain.h'):

        self.macro_key = ''

        self.encoding_type = encoding
        self.bit_size = bit_size
        self.bitvector = '__CPROVER_bitvector[%s]' % self.bit_size
        self.indentation_base = self.make_indent(2)
        self.macro_counter = 0
        self.faked_typedef = []
        self.counter_declaration = 0
        self.local_macro_counter = 0
        self.macro_file = None

        if macroFileName == 'macro_plain.h':
            self.macro_file = os.path.abspath(os.getcwd()) + '/output/' +  macroFileName
        else:
            self.macro_file = macroFileName

        if writeMacroFile:
            if os.path.exists(self.macro_file): 
               os.remove(self.macro_file)
            self.macro_file = open( self.macro_file, 'a')


        self.macro_type_ext = ''
        self.macro_type_int = ''


        self.macro_type_ext = 'EXP_%s()'
        self.macro_type_int = 'LOCAL_EXP_%s'
        self.declaration_type = 'DECL_%s'

        # Dynamic macros

        self.types = ['INT', 'CHAR', 'LONG', 'SHORT', 'LONG_LONG']
        self.dynamic_translation_list = ['generic_assignment', 'plusplus_unaryexp', 'minusminus_unaryexp',
                                         'postfix_plusplus', 'postfix_minusminus', 'assignment', 'postfixReference_arrow', 'postfixReference_dot', '*_castExp', 'generic_assignment']

        self.signed_bound_exp_list = []
        self.unsigned_bound_exp_list = []

        for type in self.types:

            if type.lower() == 'long_long':
                type_legit = 'long long'
            else:
                type_legit = type.lower()
                type = type_legit.upper()

            self.signed_bound_exp_list.append("#define BOUNDS_FAILURE_SIGNED_%s( EXP ) ( ( ( ((%s)EXP) & (~(__cs_%s_mask)) ) != (~(__cs_%s_mask)) ) && ( ((%s)EXP) & (~(__cs_%s_mask)) ) )" % (type, type_legit, type.lower(), type.lower(), type.lower(), type.lower() ) )
            self.unsigned_bound_exp_list.append("#define BOUNDS_FAILURE_UNSIGNED_%s( EXP ) ( ( ((unsigned %s)EXP) & (~(__cs_%s_mask)) )  )" % (type, type_legit, type.lower() ) )



    def make_indent(self, level):
        return ' ' * level

    def printMacro(self, bit, body_abt, custom_macro=None):

        if bit:

            macro_name = self.macro_type_ext % (self.macro_counter)
            self.macro_counter += 1

            if custom_macro == 'yes': return macro_name

            macro_definition = "#define " + macro_name + '\n' + body_abt
            macro_definition = self.prepareMacro(macro_definition)

            self.macro_file.write(macro_definition)
            # macro_name = self.macro_type_ext % (self.macro_counter)

            faked = 'void %s{;}' % macro_name
            self.faked_typedef.append(faked)

            return macro_name


        else:

            macro_name = self.macro_type_int % (self.local_macro_counter)
            self.local_macro_counter += 1

            if custom_macro == 'yes': return macro_name

            macro_definition = "#define " + macro_name + '\n' + body_abt

            macro_definition = self.prepareMacro(macro_definition)

            self.macro_file.write(macro_definition)
            return macro_name


    def printCustomMacro(self, macro):
        stringa = '#define %s\n' % macro
        self.macro_file.write(stringa)

    def printDeclaration(self, decl_string, declaration):
        stringa = '#define %s()\n' % decl_string
        faked = 'void %s(){;}' % decl_string
        self.faked_typedef.append(faked)
        self.counter_declaration += 1
        dec = stringa + declaration
        dec = self.prepareMacro(dec)
        self.macro_file.write(dec)
        return decl_string + '();\n'

    def getHeaderMacro(self):
        return """/*
*****************************************************
*****************************************************
******         BOUND CHECKING MACROS           ******
*****************************************************
*****************************************************
*/"""
    def getHeaderMacroEnd(self):
        return """/*
*****************************************************
*****************************************************
******                END                      ******
*****************************************************
*****************************************************
*/"""



    def getMacroBounds(self):

        signed_exps = ''
        unsigned_exps = ''

        for item in self.signed_bound_exp_list:
            signed_exps += item+'\n'

        for item in self.unsigned_bound_exp_list:
            unsigned_exps += item+'\n'


        return signed_exps +'\n'+ unsigned_exps



    def getMinMax(self):


        max_by_type = """
#define MAX_INT(E) ( ( ((BITVECTOR)E) == ((BITVECTOR)__cs_int_max)) )
#define MAX_SHORT(E) ( ( ((BITVECTOR)E) == ((BITVECTOR)__cs_short_max)) )
#define MAX_LONG(E) ( ( ((BITVECTOR)E) == ((BITVECTOR)__cs_long_max)) )
#define MAX_LONG_LONG(E) ( ( ((BITVECTOR)E) == ((BITVECTOR)__cs_long_long_max)) )
#define MAX_CHAR(E) ( ( ((BITVECTOR)E) == ((BITVECTOR)__cs_char_max)) )
"""
        min_by_type = """
#define MIN_INT(E) ( ( ((BITVECTOR)E) == ((BITVECTOR)__cs_int_min)) )
#define MIN_SHORT(E) ( ( ((BITVECTOR)E) == ((BITVECTOR)__cs_short_min)) )
#define MIN_LONG(E) ( ( ((BITVECTOR)E) == ((BITVECTOR)__cs_long_min)) )
#define MIN_LONG_LONG(E) ( ( ((BITVECTOR)E) == ((BITVECTOR)__cs_long_long_min)) )
#define MIN_CHAR(E) ( ( ((BITVECTOR)E) == ((BITVECTOR)__cs_char_min)) )
"""


        return max_by_type + '\n' + min_by_type

    def getGenericForTypeName(self):

        ##int char long int short long long

        enum = """
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
        """


        typename1 = """
#define typename(x) _Generic((x),
        char: TYPENAME_CHAR,                  
        unsigned char: TYPENAME_UNSIGNED_CHAR,                
        short: TYPENAME_SHORT,                
        unsigned short: TYPENAME_UNSIGNED_SHORT,                
        int: TYPENAME_INT,                    
        unsigned int: TYPENAME_UNSIGNED_INT,
        long int: TYPENAME_LONG_INT,               
        unsigned long int: TYPENAME_UNSIGNED_LONG_INT,
        long long : TYPENAME_LONG_LONG,      
        unsigned long long:  TYPENAME_UNSIGNED_LONG_LONG,
        default:  TYPENAME_OTHER)

"""



        prepared_macro2 = self.prepareMacro(typename1)
        return  enum + '\n' + prepared_macro2

    def prepareMacro(self, txt):
        body = ''
        num_of_lines = len(txt.splitlines())
        for index, line in enumerate(txt.splitlines()):
            line = line.replace('\t', '    ')
            body += line.ljust(300, ' ') + '\\' + '\n' if index < num_of_lines - 1 else line.ljust(300, ' ') + '\n\n'
        return body

    def beautifyString(self, txt):

        body = ''
        lenString = len(txt.splitlines())


        if '#' in txt:
            txt = txt.split()[-1]
            txt = txt.lstrip().rstrip()
            return txt

        if 'ATOMIC_FUNC_LOCAL_EXP' in txt:
            txt = txt.lstrip().rstrip()
            return txt

        txt = txt.lstrip()

        if txt[0] == '\n':
            txt = txt[1:]

        if txt.startswith('#') and 'LOCAL_EXP' in txt:
            txt = txt.split('\n')[1].replace(' ', '')

        #if txt.startswith('LOCAL_EXP'):
        #    return txt.replace('\n','').replace(N' ')

        # This is the check for the transformation identifier
        if txt.startswith('PLACEHOLDER'):
            txt = txt.replace('PLACEHOLDER', '')
            return txt

        elif lenString > 1:

            for line in txt.splitlines():
                line = self.indentation_base * 8 + line + '\n'
                body += line

            return body

        else:
            return txt.replace('\n','').replace(' ','')

    def cleanDirtyString(self,txt):
        s=''
        for line in txt.splitlines():
            if '<previous_' in line:
                pass
            else: s=s+'\n'+line
        return s

    def getEncodingDecodingMacroClean(self):


        encode_int_macro = '#define ENCODE_INT(E) ((int)E) \n'
        encode_short_macro = '#define ENCODE_SHORT(E) ((short)E) \n'
        encode_char_macro = '#define ENCODE_CHAR(E) ((char)E) \n'
        encode_long_macro = '#define ENCODE_LONG(E) ((long)E) \n'
        encode_longlong_macro = '#define ENCODE_LONGLONG(E) ((long long)E)\n'

        decode_uns = '#define DECODE_UNSIGNED(F) (unsigned %s) F\n' % self.bitvector
        decode_sign = '#define DECODE_SIGNED(F) (%s) F\n' % self.bitvector

        return encode_int_macro + '\n' + encode_short_macro + '\n' + encode_char_macro + '\n' + encode_long_macro + '\n' + encode_longlong_macro + '\n' + decode_uns + '\n' + decode_sign

    def indentBlock(self, text, level):

        result = '\n'
        for line in text.splitlines():
            result += self.indentation_base * level + line + '\n'

        return result

    def getEncodingDecodingMacroPack(self):

        """
        enum
        t_typename
        {
            TYPENAME_BOOL,
            TYPENAME_UNSIGNED_CHAR,
            TYPENAME_CHAR,
            TYPENAME_SHORT,
            TYPENAME_UNSIGNED_SHORT,
            TYPENAME_INT,
            TYPENAME_UNSIGNED_INT,
            TYPENAME_LONG_INT,
            TYPENAME_UNSIGNED_LONG_INT,
            TYPENAME_LONG_LONG,
            TYPENAME_UNSIGNED_LONG_LONG,
            TYPENAME_OTHER
        };
        """

        decode_uns = '#define DECODE_UNSIGNED(F) (unsigned %s) F' % self.bitvector
        decode_sign = '#define DECODE_SIGNED(F) (%s) F\n' % self.bitvector

        encode_int_macro = '#define ENCODE_INT(E) ( __cs_int_mask & ((int)E) )\n'
        encode_short_macro = '#define ENCODE_SHORT(E) ( __cs_short_mask & ((short)E)  )\n'
        encode_char_macro = '#define ENCODE_CHAR(E) ( __cs_char_mask & ((char)E) ) \n'
        encode_long_macro = '#define ENCODE_LONG(E) ( __cs_long_mask & ((long)E) ) \n'
        encode_longlong_macro = '#define ENCODE_LONGLONG(E) ( __cs_long_long_mask & ((long long)E) )\n'

        return encode_int_macro + encode_char_macro + encode_short_macro + encode_longlong_macro + encode_long_macro  + '\n' + decode_uns + '\n' + decode_sign

    def bitvectorMacro(self):
        bitvector_faked = '#define BITVECTOR int'
        return bitvector_faked

    def fieldDeclaration(self, type):
        return '#define FIELD_DECLARATION_%s() __CPROVER_field_decl_%s("abstraction", (_Bool)0)\n' % (type.upper(), type)


    def getHeaderShadowMemory(self):
        return """/*
*****************************************************
*****************************************************
******         SHADOW MEMORY FIELDS            ******
*****************************************************
*****************************************************        
*/"""

    def getHeaderEncode(self):
        return """/*
*****************************************************
*****************************************************
******        ENCODE AND DECODE MACROS         ******
*****************************************************
*****************************************************
*/"""

    def getHedaerPrep(self):
        return """/*
*****************************************************
*****************************************************
******         PREPROCESSING MACROS            ******
*****************************************************
*****************************************************
*/"""

    def getHeaderTranslation(self):
        return """/*
*****************************************************
*****************************************************
******             TRANSLATION                 ******
*****************************************************
*****************************************************
*/"""


    def getHeaderVariables(self):
        return """/*
*****************************************************
*****************************************************
******          VARIABLES and MASKS            ******
*****************************************************
*****************************************************
*/"""

    def printFirsMacroSet(self,variables_list):

        if self.encoding_type == 'clean':
            encoding = self.getEncodingDecodingMacroClean()
        else:
            encoding = self.getEncodingDecodingMacroPack()

        items= self.getHeaderVariables() \
               + '\n\n' \
               + self.bitvectorMacro() \
               + '\n' \
               + '\n'.join(variables_list) \
               + '\n' \
               + self.getHeaderMacroEnd() \
               + '\n' \
               + self.getGenericForTypeName() \
               + '\n' \
               + '\n' \
               + self.getHeaderMacro() \
               + '\n' \
               + self.getMacroBounds()\
               + '\n' \
               + '\n' \
               + self.getMinMax() \
               + '\n' \
               + self.getHeaderMacroEnd() \
               + '\n' \
               + self.getHeaderEncode() \
               + '\n' \
               + encoding \
               + '\n' \
               + self.getHeaderMacroEnd() \
               + '\n\n'\
               + self.getHeaderShadowMemory() \
               + '\n' \
               + self.fieldDeclaration('global') \
               + '\n' \
               + self.fieldDeclaration('local') \
               + '\n' \
               + self.getHeaderMacroEnd() + '\n\n\n\n' \
               + self.getHeaderTranslation() + '\n\n\n'

        self.macro_file.write(items)


    def raiseException(self, message):
        raise Exception('Exception Raised:  {0}'.format(message))
