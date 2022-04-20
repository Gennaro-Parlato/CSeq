class Transformation(object):

    def __init__(self, name):

        #We assume  generic_1 is used for generic val_value
        #We assume  generic_2 is used for generic ba_value
        #We assume  val_phi the result of a transformation

        self.name = name
        self.__t_type = ''
        self.__body = ''
        self.__declaration = ''
        self.__declaration_index = {
                        'val_phi': 0,
                        'generic_1': 0,
                        'generic_2': 0
                        }
    @property
    def t_type(self):
        return self.__t_type

    @t_type.setter
    def t_type(self, value):
        self.__t_type = value

    @property
    def declaration_index_val_phi(self):
        return self.__declaration_index.get('val_phi')

    @declaration_index_val_phi.setter
    def declaration_index_val_phi(self, value):
        self.__declaration_index.__setitem__('val_phi', value)

    @property
    def declaration_index_generic_1(self):
        return self.__declaration_index.get('generic_1')


    @declaration_index_generic_1.setter
    def declaration_index_generic_1(self, value):
        self.__declaration_index.__setitem__('generic_1', value)

    @property
    def declaration_index_generic_2(self):
        return self.__declaration_index.get('generic_2')

    @declaration_index_generic_2.setter
    def declaration_index_generic_2(self, value):
        self.__declaration_index.__setitem__('generic_2', value)

    @property
    def body(self):
        return self.__body

    @body.setter
    def body(self, body):
        self.__body = body

    @property
    def declaration(self):
        return self.__declaration

    @declaration.setter
    def declaration(self, declaration):
        self.__declaration = declaration