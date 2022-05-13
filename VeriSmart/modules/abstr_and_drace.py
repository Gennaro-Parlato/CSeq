from modules import drace

class abstr_and_drace(drace.drace):
    def init(self):
        super().init(abs_on=True)
