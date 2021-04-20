"""
    Logging feature for CSeq

TODO:
    - Add staticstic feature for Logger

Changelog:
    2015.07.21   Change to os.path for pyinstaller
    2015.01.18   Add reporter feature
    2015.01.16   Logger class
"""
import datetime
import os
import os.path
from bin import config
import sys


class Logger():
    """
    Log every calls of CSeq
    """

    def __init__(self):
        self.logString = ""
        self.output = ""
        self.outputfile = ""

    def setInputFile(self, inputfile):
        dirname, filename = os.path.split(os.path.abspath(inputfile))
        dirname = os.path.dirname(sys.argv[0]) + "/bin"
        reportdir = dirname + "/" + config.reportpath
        if not os.path.exists(reportdir):
            os.makedirs(reportdir)
        now = datetime.datetime.now()
        # add year to reportdir
        dt = now.strftime("%Y-%b-%d-%H-%M-%S")
        reportfilename = filename + "-" + dt + ".csv"
        reportfilename = reportdir + "/" + reportfilename
        self.outputfile = reportfilename

    def record(self, string):
        self.output += string

    def savereport(self):
        return
        reportfile = ""
        if not os.path.exists(self.outputfile):
            reportfile = open(self.outputfile, "w")
        else:
            reportfile = open(self.outputfile, "a")
            reportfile.write("Appended....\n")
        reportfile.write(self.output)
        self.output = ""   # reset output
        reportfile.close()

    def logging(self, string, entryType=0):
        return
        now = datetime.datetime.now()
        entryTime = now.strftime("%H:%M:%S")
        if entryType == 0:   # Command line
            self.logString += "\nAt " + entryTime + "\nrun cmd: " + string + "\n"
        elif entryType == 1:    # Result
            self.logString += "result: " + string + "\n"
        elif entryType == 2:    # Manual configuration of Swarm
            self.logString += "configuration: " + string + "\n"

    def writelog(self):
        return
        dirname = os.path.dirname(sys.argv[0]) + "/bin"
        logdir = dirname + "/" + config.logpath
        if not os.path.exists(logdir):
            os.makedirs(logdir)
        now = datetime.datetime.now()
        # add year to logdir
        logdir += "/" + str(now.year)
        if not os.path.exists(logdir):
            os.makedirs(logdir)
        # add month to logdir
        logdir += "/" + now.strftime("%B")
        if not os.path.exists(logdir):
            os.makedirs(logdir)
        logfilename = str(now.year) + "-" + str(now.month) + "-" + str(now.day) + ".log"
        logfilename = logdir + "/" + logfilename
        logfile = ""
        if not os.path.exists(logfilename):
            logfile = open(logfilename, "w")
        else:
            logfile = open(logfilename, "a")
        logfile.write(self.logString)
        self.logString = ""    # reset
        logfile.close()
