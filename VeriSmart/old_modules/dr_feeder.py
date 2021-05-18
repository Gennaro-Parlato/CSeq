import core.module, core.parser, core.utils
from modules import feeder

class dr_feeder(feeder.feeder, object):

    def loadfromstring(self, string, env):
        if env.seq_only:
            seqfile = core.utils.rreplace(env.inputfile, '/', '/'+env.prefix, 1) if '/' in env.inputfile else env.prefix + env.inputfile
            if env.outputfile is not None and env.outputfile != '':
                seqfile = env.outputfile
            newstring = string
            core.utils.saveFile(seqfile, string)
        else:
            super(self.__class__, self).loadfromstring(string, env)
        return


