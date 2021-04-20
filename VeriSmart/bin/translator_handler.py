import os.path
import sys
import subprocess
import shlex
import re
import multiprocessing
import json

from bin import utils
VERSION = "2016.12.07"
"""

Objectives:
    Translators handler here

Prerequisites:

TODO:
    - Add translation for CPA checker
    - translator for cluster jobs


Changelog:
    2017.09.06  add option to limit generating file after reading configuration file
    2016.10.07  add option to stop when need only want to generate configuration files (see env["config-only"])
    2016.09.15  Make commandline compatible with lazy-cseq command line options
    2016.06.13  Add RTOS option
    2015.07.21  Change to os.path for the sack of pyinstaller
    2015.06.19  Fix some call to missing parameter (logger)
    2015.02.02  Code refactory
    2015.01.31  Add version of parallel-generator (help improving the performance)
    2015.01.20  Add calls to translator for SAFE and UNSAFE strategy of swarm
    2015.01.02  Adapt Lazy-cseq version 1.0 (supporting line mapping)
    2014.12.12  Initial version

"""


def step1SetupCMD(env, inputfile, isSwarm=False, logger=None):
    if env["verbose"]:
        print ("\ninput:  %s") % (inputfile)
    # Call indepently (doesn"t matter when it gets called)
    # Real path os this file
    cmdline = os.path.dirname(sys.argv[0]) + "/"
    if env["swarm-translator"] != "":
        cmdline += env["swarm-translator"]
    else:
        from bin import config
        if isSwarm:
            cmdline += config.relpath["swarmtranslator"]
        else:
            cmdline += config.relpath["translator"]

    cmdline += " -i %s --rounds %s --backend %s --error-label %s" % (
        str(inputfile), str(env["rounds"]),
        env["backend"], env["error-label"])
    cmdline += " --unwind " + str(env["unwind"])
    # Mind CIL feature
    if env["forunwind"] != 0:
        cmdline += "  --unwind-for " + str(env["forunwind"])
    if env["whileunwind"] != 0:
        cmdline += " --unwind-while " + str(env["whileunwind"])
    if env["soft-unwind-max"] != 0:
        cmdline += " --unwind-for-max " + str(env["soft-unwind-max"])
    if env["softunwindbound"]:
        cmdline += " --softunwindbound"
    # Enable debug
    # if env["debug"]:
    #     cmdline += " -D"
    if env["deadlock"]:
        cmdline += " --deadlock"
    if env["keepstaticarray"]:
        cmdline += " --keepstaticarray"
    if env["donotcheckvisiblepointer"]:
        cmdline += " --donotcheckvisiblepointer"
    if env["explode-pc"]:
        cmdline += " --decomposepc"
    if env["robin"]:
        cmdline += " --robin"
    else:
        cmdline += " --norobin"
    if env["chain"] != "":
        cmdline += " -l %s" % env["chain"]
    if env["suffix"] != "":
        cmdline += " --suffix %s" % env["suffix"]
    if env["wmm"]:    # for wmm generator only
        cmdline += " --wmm "
    if env["svcomp"]:
        cmdline += " --svcomp "
    if env["cex"]:
        if env["analysis-mode"] == "normal":
            cmdline += " --cex "
            if env["stop-on-fail"]:
                cmdline += " --stop-on-fail "
        else:
            cmdline += " --dump-env "
    # elif env["force-chain"]:   # If chain is not set and force-chain is applied
    #     cmdline += " --force-chain"
    # if env["main-argc"] != 1:
    #     cmdline += " --main-argc %s" % env["main-argc"]
    # if env["main-argv"] != "program":
    #     cmdline += " --main-argv %s" % env["main-argv"]

    return cmdline


def step2GetThreadLines(env, cmdline, inputfile, verbose=True):
    p = subprocess.Popen(shlex.split(cmdline + " -Y"), stdout=subprocess.PIPE)
    out, err = p.communicate()
    out = out.decode()
    cseqanswer = p.returncode
    logfile = inputfile + ".threadline"
    print(logfile)
    utils.saveFile(logfile, out)

    if env["verbose"]:
        print("cmd:    " + cmdline + " -Y")

    """ now check that the sequentialisation went fine """
    if cseqanswer != 0:   # doesn"t well
        if env["verbose"]:
            print("\n       (unable to sequentialise input file  -  see below for details)\n")
        if env["verbose"]:
            print(utils.colors.BLACK + "- " * 32)
        with open(logfile) as file:
            data = file.read()
            print(data)
        if env["verbose"]:
            print(utils.colors.BLACK + "- " * 32 + utils.colors.NO + "\n")
        if env["verbose"]:
            print(utils.colors.YELLOW + "        UNKNOWN\n" + utils.colors.NO)

        return "", False
    else:     # Sequentialization went well
        # Print thread lines of each thread
        if verbose:
            print(out)
            sys.stdout.flush()
        return out, True


def step3GenerateConfigFileNormalPercentage(env, out, configFilename, logger=None):
    # Parse configuration file
    if env["automatic"]:
        # Create a generator
        configGen = utils.ConfigGeneratorPercentage(out, env["window-percent"], env["picked-window"], env["instances-limit"], consecutive=(not env["scatter"]), double=env["shifted-window"], skiplist=env["skip-thread"])
        # Overwrite configuration file
        configGen.generatingConfigPercentage(configFilename, softLimit=env["soft-limit"], hardLimit=env["hard-limit"], randomness=(not env["no-random"]), start=env["start-sample"])
    else:
        f = open(configFilename)
        logger.logging(f.read(), 2)
        f.close()
        logger.writelog()


def step3GenerateConfigFileNormalWMM(env, out, configFilename, logger=None):
    # Parse configuration file
    if env["automatic"]:
        # Create a generator
        configGen = utils.ConfigGeneratorWMM(out, env["window-length"], env["picked-window"], env["wmm-l"], env["wmm-p"], env["instances-limit"], consecutive=(not env["scatter"]), double=env["shifted-window"], WMMdouble=env["wmm-double"], skiplist=env["skip-thread"])
        # Overwrite configuration file
        configGen.generatingConfigWMM(configFilename, softLimit=env["soft-limit"], hardLimit=env["hard-limit"])
    else:
        f = open(configFilename)
        logger.logging(f.read(), 2)
        f.close()
        logger.writelog()

def step3GenerateConfigIteratorNormal(env,out,configFilename,inputfile,percent,logger=None):
    configGen = utils.ConfigGenerator(out, percent, env["cluster-config"], env["window-length"],  env["window-percent"],  env["picked-window"],
            env["instances-limit"], env["config-only"], consecutive=(not env["scatter"]),
            double=env["shifted-window"], skiplist=env["skip-thread"])
    singleConfigFilename = configFilename + ".tmp"
    if env["automatic"]:
        # Create a generator
        # Overwrite configuration file
        return configGen.generatingConfig(configFilename, singleConfigFilename, inputfile, softLimit=env["soft-limit"],
            hardLimit=env["hard-limit"], randomness=(not env["no-random"]), start=env["start-sample"])
    else:
        #f = open(configFilename)
        #logger.logging(f.read(), 2)
        #f.close()
        #logger.writelog()
        fd = open(configFilename,"r")
        generatedData=json.load(fd) 
        #print("%s" % generatedData)
        #print("%s" % len(generatedData))
        fd.close()
        #env["instances-limit"]=len(generatedData)
         
        return configGen.generatorConfigIterator(singleConfigFilename,len(generatedData),generatedData) 




def step3GenerateConfigFileNormal(env, out, configFilename, logger=None):
    # Parse configuration file
    if env["automatic"]:
        # Create a generator
        configGen = utils.ConfigGenerator(out, env["window-length"], env["picked-window"],
            env["instances-limit"], consecutive=(not env["scatter"]),
            double=env["shifted-window"], skiplist=env["skip-thread"])
        # Overwrite configuration file
        configGen.generatingConfig(configFilename, softLimit=env["soft-limit"],
            hardLimit=env["hard-limit"], randomness=(not env["no-random"]), start=env["start-sample"])
    else:
        f = open(configFilename)
        logger.logging(f.read(), 2)
        f.close()
        logger.writelog()


def step3GenerateConfigFileSA(env, out, configFilename, logger=None):
    print("Generating configuration file...")
    sys.stdout.flush()
    configGen = utils.ConfigGenerator(out, 1, 1, env["instances-limit"])   # Only one context switch
    configGen.generatingConfig(configFilename, softLimit=env["soft-limit"], hardLimit=0)  # pick the first 100000
    print("... done.")
    sys.stdout.flush()


def step3GenerateConfigFileEX(env, out, configFilename, logger=None):
    print("Generating configuration file...")
    sys.stdout.flush()
    info = utils.threadLinesToDict(out)
    numInstance = 0
    result = True
    if env["strategy"] == "quarter":
        print("strategy 1: window size is a quarter of original thread lines")
        numInstance, result = utils.generatingConfigQuarterSizeInstance(info, configFilename)
    elif env["strategy"] == "half":
        print("strategy 2: window size is a half of original thread lines")
        numInstance, result = utils.generatingConfigHalfSizeInstance(info, configFilename, pickWindow=1)
    else:
        print("strategy 3: window size is set manually with window size %s and pick %s" % (env["window-length"], env["picked-window"]))
        configGen = utils.ConfigGenerator(out, env["window-length"], env["picked-window"], env["instances-limit"], consecutive=(not env["scatter"]), double=env["shifted-window"], skiplist=env["skip-thread"])
        numInstance, result = configGen.generatingConfig(configFilename, softLimit=env["soft-limit"], hardLimit=env["hard-limit"])
    print("... done.")
    sys.stdout.flush()
    return numInstance


def step3GenerateConfigFileEXFollowup(env, configDict, configFilename, logger=None):
    print("Generating configuration file...")
    sys.stdout.flush()
    numInstance = 0
    result = True
    if env["strategy"] == "quarter":
        numInstance, result = utils.generatingConfigHalfSizeInstance(configDict, configFilename, pickWindow=2, instancesLimit=env["instances-limit"])
    elif env["strategy"] == "half":
        numInstance, result = utils.generatingConfigHalfSizeInstance(configDict, configFilename, pickWindow=1, instancesLimit=env["instances-limit"])
    else:
        numInstance, result = utils.generatingConfigHalfSizeInstance(configDict, configFilename, env["picked-window"], instancesLimit=env["instances-limit"])
    print("... done.")
    sys.stdout.flush()
    return numInstance


def step3ABuildNewConfig(candidateList, cached):
    configDict = utils.parseConfig(cached["configFile"])
    newConfigDict = {}
    # filter candidate form candidate list
    for candidate in candidateList:
        # Get instances name:
        samplename = candidate[candidate.rfind("_")+1:]    # Strip filename and instance
        samplename = samplename[:-2]  # strip .c and find sample name
        # pick the sample
        if samplename in configDict:
            newConfigDict[samplename] = configDict[samplename]
        else:
            print("There is something wrong with the configuration file")
            sys.exit(2)
    return newConfigDict


def filterCandidates(env, entryList):
    candidateList = {}
    for l in entryList:
        entry = l.split(",")
        samplename = entry[0].strip()
        outcome = entry[1].strip()
        timeout = int(float(entry[2].strip()))
        icon = ""
        if outcome == "TRUE":
            icon = "t"
        elif outcome == "FALSE":
            icon = "f"
        elif outcome == "UNKNOWN":
            icon = "u"
        elif outcome == "TIMEOUT":
            icon = "o"
        else:
            print("The instances could not have been sequentialised.")
            sys.exit(2)
        if icon in env["pOption"]:
            lstr = "p%sl" % icon
            ustr = "p%su" % icon
            lowerBound = env["pl"] if env[lstr] == -1 else env[lstr]
            upperBound = env["pu"] if env[ustr] == -1 else env[ustr]
            if (timeout >= lowerBound and timeout <= upperBound):
                candidateList[samplename] = timeout
    return candidateList


def step3ABuildNewConfigSelective(env, candidateFile, configFile):
    configDict = utils.parseConfig(configFile)
    newConfigDict = {}
    # filter candidate form candidate list
    with open(candidateFile, "r") as inFile:
        entryList = list(inFile)

    bestTimeout = 31536000  # A year
    candidateList = filterCandidates(env, entryList)
    for candidate in candidateList:
        # Get instances name:
        samplename = candidate[candidate.rfind("_")+1:]    # Strip filename and instance
        if bestTimeout > candidateList[candidate]:
            bestTimeout = candidateList[candidate]
        samplename = samplename[:-2]  # strip .c and find sample name
        # pick the sample
        if samplename in configDict:
            newConfigDict[samplename] = configDict[samplename]
        else:
            print("There is something wrong with the configuration file")
            sys.exit(2)

    env["bestTimeout"] = bestTimeout
    return newConfigDict


def step3ABuildNewConfigMultiple(candidatesList, configFile):
    configDict = utils.parseConfig(configFile)
    newConfigDict = {}
    for file in candidatesList:
        cList = utils.parseConfig(file)
        for candidate in cList:
            # Get instances name:
            samplename = candidate[candidate.rfind("_")+1:]    # Strip filename and instance
            samplename = samplename[:-2]  # strip .c and find sample name
            # pick the sample
            if samplename in configDict:
                newConfigDict[samplename] = configDict[samplename]
            else:
                print("There is something wrong with the configuration file")
                sys.exit(2)

    return newConfigDict


def translatingWorker(cmdline):
    command = utils.Command(cmdline)
    out, err, retcode, memory = command.run(timeout=86400)


def step4GenerateInstanceIterator(env, cmdline, configIterator,listFile):
    if env["config-only"]:
        sys.exit(0)
#        if env["split-config"] and env["bag-size"] == 1:
#            # special case: give the config directly as a command-line argument
    i = 0
    for config in configIterator:
        filename,chosenInstances,b = config
        newcmdline = cmdline + " -C \"%s\"" % filename
#        else:
#            newcmdline = cmdline + " -C %s" % newConfigFilename  
        newcmdline += " -Z %s" % listFile
        if env["verbose"]:
            print(newcmdline)
    # Generating multiple instances
        #print(newcmdline)
        p = subprocess.Popen(shlex.split(newcmdline), stdout=subprocess.PIPE)
        out, err = p.communicate()
#        print "... done."
        #open(listFile)
        sys.stdout.flush()
        #os.remove(filename)
        yield i
        i+=1

def step4GenerateInstances(env, cmdline, configFilename, listfileFilename, keepFiles=False):
    newConfigFilename = configFilename
    if env["generate-limit"] != 0 and (not env["split-config"] or env["bag-size"] != 1):
        newConfigFilename = utils.preprocessConfigFile(configFilename, env["generate-limit"])

    if env["parallel-generator"]:
        configFileList = utils.distributingGenerators(newConfigFilename, env["generators"])
        listFileList = []
        jobList = []
        for i, item in enumerate(configFileList):
            newcmdline = cmdline + " -C %s" % item
            lf = listfileFilename + ".part%s" % i
            listFileList.append(lf)
            newcmdline += " -Z %s" % lf
            jobList.append(newcmdline)

        if env["config-only"]:
            print(os.path.abspath(configFilename))   # Easier to get filename and reapply them
            sys.exit(0)

        pool_size = env["generators"]
        print("in parallel with %s generators" % pool_size)
        pool = multiprocessing.Pool(processes=pool_size)
        pool.map(translatingWorker, jobList)
        pool.close()
        pool.join()
        # Merge list files to one file
        utils.combineList(listFileList, listfileFilename)
        # clean configFile list
        if not keepFiles:
            for f in configFileList:
                try:
                    os.remove(f)
                except OSError as e:
                    print(str(e))
    else:    # Normal generator
        if env["config-only"]:
            sys.exit(0)
        if env["split-config"] and env["bag-size"] == 1:
            # special case: give the config directly as a command-line argument
            newcmdline = cmdline + " -c \"%s\"" % newConfigFilename
        else:
            newcmdline = cmdline + " -C %s" % newConfigFilename  
        newcmdline += " -Z %s" % listfileFilename
        if env["verbose"]:
            print(newcmdline)
        # Generating multiple instances
        p = subprocess.Popen(shlex.split(newcmdline), stdout=subprocess.PIPE)
        out, err = p.communicate()
    print("... done.")
    sys.stdout.flush()


def step5GetFileListNormal(listFile):
    seqfileList = []
    flist = open(listFile)
    text = flist.read()
    for line in text.splitlines():
        seqfileList.append(line)
    flist.close()
    return seqfileList, True


def step5GetFileListDistributed(listFile, descDict, numInstance, workers=1, cluster=False):
    numInstancePerWorker = int(numInstance/workers+1)
    instancesList = []
    with open(listFile) as ins:
        instancesList = ins.readlines()
    jobList = utils.chunk(instancesList, numInstancePerWorker)
    descDict["currIter"]["instancesList"] = []
    descDict["currIter"]["candidatesList"] = []
    for index, job in enumerate(jobList):
        jobName = listFile + ".div%s" % index
        cList = listFile + ".div_candidatesL%s" % index
        descDict["currIter"]["instancesList"].append(jobName)  # Designated this job
        descDict["currIter"]["candidatesList"].append(cList)
        with open(jobName, "w") as out:
            for i in job:
                if i is not None:
                    out.write(i)


def callTranslatorNormal(env, inputfile, logger=None):
    cmdline = step1SetupCMD(env, inputfile, isSwarm=False, logger=logger)
    if env["verbose"]:
        print("cmd:    " + cmdline)
    # Calling feeder
    p = subprocess.Popen(shlex.split(cmdline), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = p.communicate()
    # if env["debug"]:
    #     print err
    cseqanswer = p.returncode

    # Set output file name
    dirname, filename = os.path.split(os.path.abspath(inputfile))
    outputfile = dirname + "/_cs_" + filename
    if env["outputfile"] != "":
        outputfile = env["outputfile"]

    if env["verbose"]:
        print("outputfile:    " + outputfile)

    if env["verbose"]:
        print("result:    ")

    print(out + err)


    # save sequential file to output
    # utils.saveFile(outputfile, out)

    # success = True
    # """ now check that the sequentialisation went fine """
    # if cseqanswer != 0:
    #     if env["verbose"]:
    #         print "\n       (unable to sequentialise input file  -  see below for details)\n"
    #     if env["verbose"]:
    #         print utils.colors.RED + "- " * 32
    #     with open(outputfile) as file:
    #         data = file.read()
    #         print data,
    #     if env["verbose"]:
    #         print utils.colors.RED + "- " * 32 + utils.colors.NO + "\n"
    #     if env["verbose"]:
    #         print utils.colors.YELLOW + "        UNKNOWN\n" + utils.colors.NO
    #     success = False
    # return outputfile, success


def callTranslatorSwarmPercentage(env, inputfile, logger=None):
    # setting up cmd
    cmdline = step1SetupCMD(env, inputfile, isSwarm=True, logger=logger)
    # get thread lines
    out, result = step2GetThreadLines(env, cmdline, inputfile)
    if not result:
        return out, result
    else:
        if env["showcs"]:   # Exit if this is the only job require to do
            # Extra feature, generating a configuration file for manual controlling context switch
            print("Now generating manual configuration file...")
            sys.stdout.flush()
            configFile = inputfile[:-2] + "_manual_config.json"
            configGen = utils.ConfigGenerator(out, 2, 1, 100)
            configGen.generatingManualConfig(configFile)
            print("...done")
            sys.stdout.flush()
            logger.writelog()
            sys.exit(0)
        # Generating configuration file
        if env["configFile"] == "":
            print("[Swarm by percentage settings] Auto-creating configuration file...")
            if not env["automatic"]:
                print("Please set -A option if you want to automatically generate instances")
                sys.exit(2)
            env["configFile"] = inputfile[:-2] + "_auto_config%s.json" % env["suffix"]
        configFile = env["configFile"]
        print("Generating configuration file...")
        step3GenerateConfigFileNormalPercentage(env, out, configFile, logger)
        print("... done.")
        # Generating instances
        if env["instances-limit"] == 0:
            print("Generating instances with no limit")
        else:
            print("Generating instances with limit %s" % env["instances-limit"])
        dirname, filename = os.path.split(os.path.abspath(inputfile))
        swarmdirname = dirname + "/" + filename[:-2] + ".swarm%s/" % env["suffix"]
        listFile = swarmdirname + "swarm_instances.list"
        step4GenerateInstances(env, cmdline, configFile, listFile)
        # Get file list
        return step5GetFileListNormal(listFile)


def callTranslatorSwarmWMM(env, inputfile, logger=None):
    # setting up cmd
    cmdline = step1SetupCMD(env, inputfile, isSwarm=True, logger=logger)
    # get thread lines
    out, result = step2GetThreadLines(env, cmdline, inputfile)
    if not result:
        return out, result
    else:
        if env["showcs"]:   # Exit if this is the only job require to do
            # Extra feature, generating a configuration file for manual controlling context switch
            print("Now generating manual configuration file...")
            sys.stdout.flush()
            configFile = inputfile[:-2] + "_manual_config.json"
            configGen = utils.ConfigGenerator(out, 2, 1, 100)
            configGen.generatingManualConfig(configFile)
            print("...done")
            sys.stdout.flush()
            logger.writelog()
            sys.exit(0)
        # Generating configuration file
        if env["configFile"] == "":
            print("[Swarm for WMM] Auto-creating configuration file...")
            if not env["automatic"]:
                print("Please set -A option if you want to automatically generate instances")
                sys.exit(2)
            env["configFile"] = inputfile[:-2] + "_auto_config%s.json" % env["suffix"]
        configFile = env["configFile"]
        print("Generating configuration file...")
        step3GenerateConfigFileNormalWMM(env, out, configFile, logger)
        print("... done.")
        # Generating instances
        if env["instances-limit"] == 0:
            print("Generating instances with no limit")
        else:
            print("Generating instances with limit %s" % env["instances-limit"])
        dirname, filename = os.path.split(os.path.abspath(inputfile))
        swarmdirname = dirname + "/" + filename[:-2] + ".swarm%s/" % env["suffix"]
        listFile = swarmdirname + "swarm_instances.list"
        step4GenerateInstances(env, cmdline, configFile, listFile)
        # Get file list
        return step5GetFileListNormal(listFile)

#changed to iterator
def callTranslatorSwarm(env, inputfile, percent, logger=None):
    # setting up cmd
    cmdline = step1SetupCMD(env, inputfile, isSwarm=True, logger=logger)
    # get thread lines
    out, result = step2GetThreadLines(env, cmdline, inputfile)
    if not result:
        return out, result
    else:
        if env["showcs"]:   # Exit if this is the only job require to do
            # Extra feature, generating a configuration file for manual controlling context switch
            print("Now generating manual configuration file...")
            sys.stdout.flush()
            configFile = inputfile[:-2] + "_manual_config.json"
            configGen = utils.ConfigGenerator(out, 2, 1, 100)
            configGen.generatingManualConfig(configFile)
            print("...done")
            sys.stdout.flush()
            logger.writelog()
            sys.exit(0)
        # Generating configuration file
        if env["configFile"] == "":
            print("[Swarm by normal settings] Auto-creating configurations...")
            if not env["automatic"]:
                print("Please set -A option if you want to automatically generate instances")
                sys.exit(2)
            env["configFile"] = inputfile[:-2] + "_auto_config%s.json" % env["suffix"]
        configFile = env["configFile"]
        if env["automatic"]:
              print("Generating configurations..")
        else:
              print("Loading configurations..")
           
        #step3GenerateConfigFileNormal(env, out, configFile, logger)
        configIterator = step3GenerateConfigIteratorNormal(env, out,configFile,inputfile, percent, logger)
        
        print("... done.")
        # Generating instances
        if env["automatic"]: 
           if env["instances-limit"] == 0:
              print("Generating instances with no limit")
           else:
              print("Generating instances with limit %s" % env["instances-limit"])
        else:
              print("Generating instances ..")
        dirname, filename = os.path.split(os.path.abspath(inputfile))
        swarmdirname = dirname + "/" + filename[:-2] + ".swarm%s/" % env["suffix"]
        listFile = swarmdirname + "swarm_instances.list"
        #step4GenerateInstances(env, cmdline, configFile, listFile)
        instanceIterator=step4GenerateInstanceIterator(env, cmdline, configIterator, listFile)
        # Get file list
        return listFile, instanceIterator


def callTranslatorSwarmSA(env, inputfile, logger=None):
    """
    For SWARM translation + strategy for SAFE instances
    """
    # setting up cmd
    cmdline = step1SetupCMD(env, inputfile, isSwarm=True, logger=logger)
    # get thread line
    out, result = step2GetThreadLines(env, cmdline, inputfile)
    if not result:
        return out, result
    else:
        print("SEQUENTIAL ANALYSIS:")
        sys.stdout.flush()
        # Generating configuration file
        if env["configFile"] == "":
            env["configFile"] = inputfile[:-2] + "_auto_config%s.json" % env["suffix"]
        configFile = env["configFile"]
        step3GenerateConfigFileSA(env, out, configFile, logger)
        # Generating instances
        print("Generating %s instances..." % env["instances-limit"])
        dirname, filename = os.path.split(os.path.abspath(inputfile))
        swarmdirname = dirname + "/" + filename[:-2] + ".swarm%s/" % env["suffix"]
        listFile = swarmdirname + "swarm_instances.list"
        step4GenerateInstances(env, cmdline, configFile, listFile)
        # get file list
        return step5GetFileListNormal(listFile)