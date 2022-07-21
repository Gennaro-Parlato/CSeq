#!/usr/bin/env python3
import os.path
import subprocess
import shlex
import os
import os.path
import sys
import getopt

from bin import config
from bin import log_handler

VERSION = "VeriSmart-1.0-2017.12.19"
VERSION = "VeriSmart-1.1-2019.02.07"
VERSION = "VeriSmart-1.2-2021.02.11"

"""

Description:
	Verification Smart, swarm verification

TODO:


Changelog:
	2021.02.11  Software Reengineering
	----------
	2018.07.09  Allow splitting the configuration file and loop on analysis (see env ["split-config"])
	2017.12.19  counterexample generation
	2017.09.06  add generate-limit option
	2016.11.16  Overhaul option help printing
	2016.11.05  Add option to use percentage for windows (swarm)
	2016.11.03  Add option for inplacer translator, now can swarm on WMM
	2016.09.15  Become a swarm launcher by default
	2016.05.23  Add option to explode pc array
	2016.05.17  Add Seahorn as a backend
	2015.11.25  Add option to keep static array
	2015.08.24  Now outputfile is the actual outputfile for normal mode
	2015.08.06  Add option to force selection of chain for backend
	2015.07.28  Add additional deadlock check
	2015.07.06  Add options for passing main function arguments
	2015.03.06  Add custom path for clang (llvm) to support llbmc and klee backends
	2015.02.16  Add SWARM strategy for separate iteration
	2015.02.03  Add SWARM strategy for incremental swarming strategy
	2015.01.20  Add SWARM strategies for SAFE and UNSAFE instance
	2015.01.16  Add logging feature, for easier experimental calls
	2015.01.14  Fix options print
	2014.12.12  Move backends handler to backend_handler.py, translator handler to translator_handler.py,
				and preprocessor handler to the corresponding file
	2014.12.02  Initial version

"""


def main(args):

    cmdlinePrefixVerismart = os.path.dirname(sys.argv[0]) + "/" + config.relpath["translator"] + " --vs"

    isDistributed = False
    isGettingProcessorsNumber = False
    numberProcess = ""

    isCluster = False
    isGettingHostfile = False
    hostfile = ""

    isDistributedSat = False
    isGettingServerAddress = False
    serverAddress = ""

    cmdlineOptions = ""

    for argument in args[1:]:
        if "-h" == argument or "--help" == argument.lower():
            os.system(cmdlinePrefixVerismart + " -h")
            sys.exit(0)
        elif "-H" == argument or "--detailedHelp" == argument.lower():
            os.system(cmdlinePrefixVerismart + " -H")
            sys.exit(0)
        elif "--master-slave-processors" == argument.lower() or "-np" == argument.lower():
            isDistributed = True
            isGettingProcessorsNumber = True
            continue
        elif isGettingProcessorsNumber:
            numberProcess = argument
            isGettingProcessorsNumber = False
            continue
        elif "-hosts" == argument.lower():
            isCluster = True
            isGettingHostfile = True
            continue
        elif isGettingHostfile:
            hostfile = argument
            isGettingHostfile = False
            continue
        elif "--ompi-server" == argument.lower() or "-server" == argument.lower():
            isDistributedSat = True
            isGettingServerAddress = True
            continue
        elif isGettingServerAddress:
            serverAddress = argument
            isGettingServerAddress = False
            continue
        cmdlineOptions += " %s" % argument

    cmdlinePrefixVerismartDistributed = "mpirun -np " + numberProcess + " --oversubscribe --quiet " + os.path.dirname(
        sys.argv[0]) + "/" + config.relpath["translatorDistributed"] + " --vs"
    cmdlinePrefixVerismartDistributedCluster = "mpirun -np " + numberProcess + " --oversubscribe -hostfile " + hostfile + " --quiet " + os.path.dirname(
        sys.argv[0]) + "/" + config.relpath["translatorDistributed"] + " --vs"
    cmdlinePrefixVerismartDistributedSat = "mpirun -np " + numberProcess + " --oversubscribe --ompi-server file:" + serverAddress + " --quiet " + os.path.dirname(
        sys.argv[0]) + "/" + config.relpath["translatorDistributed"]
    cmdlinePrefixVerismartDistributedSatCluster = "mpirun -np " + numberProcess + " --oversubscribe --ompi-server file:" + serverAddress + " -hostfile " + hostfile + " --quiet " + os.path.dirname(
        sys.argv[0]) + "/" + config.relpath["translatorDistributed"]

    if isDistributed and not isDistributedSat and not isCluster:
        os.system(cmdlinePrefixVerismartDistributed + cmdlineOptions)
        print(cmdlinePrefixVerismartDistributed + cmdlineOptions)
    elif isDistributed and not isDistributedSat and isCluster:
        os.system(cmdlinePrefixVerismartDistributedCluster + cmdlineOptions)
        print(cmdlinePrefixVerismartDistributedCluster + cmdlineOptions)
    elif isDistributed and isDistributedSat and not isCluster:
        os.system(cmdlinePrefixVerismartDistributedSat + cmdlineOptions)
        print(cmdlinePrefixVerismartDistributedSat + cmdlineOptions)
    elif isDistributed and isDistributedSat and isCluster:
        os.system(cmdlinePrefixVerismartDistributedSatCluster + cmdlineOptions)
        print(cmdlinePrefixVerismartDistributedSatCluster + cmdlineOptions)
    else:
        os.system(cmdlinePrefixVerismart + cmdlineOptions)
        # print(cmdlinePrefixVerismart + cmdlineOptions)

    sys.exit(0)


if __name__ == "__main__":
    main(sys.argv[0:])
