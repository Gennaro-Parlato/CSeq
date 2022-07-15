from modules import abstr_dr_common

class abstr(abstr_dr_common.abstr_dr_common):
    def init(self):
        super().init(abs_on=True, dr_on=False)
        
    #TODO those line additions should be moved to lazyseqnewschedule
    def insertFieldDecl(self, x):
        return x.replace("int main(void) {", "int main(void) {\nFIELD_DECLS();", 1)
    def __createMainKLEERoundRobinDecomposePC(self, rounds):
        return self.insertFieldDecl(super().__createMainKLEERoundRobinDecomposePC(rounds))
    def __createMainKLEERoundRobinOnePCCS(self, rounds):
        return self.insertFieldDecl(super().__createMainKLEERoundRobinOnePCCS(rounds))
    def __createMainKLEERoundRobin(self, rounds):
        return self.insertFieldDecl(super().__createMainKLEERoundRobin(rounds))
    def __createMainRoundRobinDecomposePC(self, rounds):
        return self.insertFieldDecl(super().__createMainRoundRobinDecomposePC(rounds))
    def __createMainRoundRobinOnePCCS(self, rounds):
        return self.insertFieldDecl(super().__createMainRoundRobinOnePCCS(rounds))
    def createMainRoundRobin(self, rounds):
        return self.insertFieldDecl(super().createMainRoundRobin(rounds))
    def __createMainDecomposePC(self, rounds):
        return self.insertFieldDecl(super().__createMainDecomposePC(rounds))
    def __createMainOnePCCS(self, rounds):
        return self.insertFieldDecl(super().__createMainOnePCCS(rounds))
    def __createMain(self, rounds):
        return self.insertFieldDecl(super().__createMain(rounds))
        
    def loadfromstring(self, string, env):
        super().loadfromstring(string, env)
        self.output = self.output.replace("int __cs_create(__cs_t *__cs_new_thread_id, void *__cs_attr, void *(*__cs_thread_function)(void*), void *__cs_arg, int __cs_threadID)", "int __cs_create(__cs_t *__cs_new_thread_id, void *__cs_attr, void *(*__cs_thread_function)(char*), char *__cs_arg, int __cs_threadID)")
        self.output = self.output.replace("void *__cs_threadargs[", "char *__cs_threadargs[")
