import os
import os.path
import sys
import shutil
import time
from time import gmtime, strftime
import multiprocessing
import builtins
from bin import utils
from bin import translator_handler

from bin.cex_handler import CEX

VERSION = "RC-2015.07.21"

"""

Objectives:
    Backends handler for Lazy-Cseq

Prerequisites:
    - Backends dependencies

TODO:
    - Add real command line for SeaHorn (from sea not sea_svcomp)
    - Add checker for Pagai, currently not working
    - Add checker for interproc and concurrentInterproc
    - handling of memory limit for backend (important for cluster jobs)

Changelog:
    2018.07.09  Improve output for split-config analysis
    2016.05.17  Add seahorn as a backend
    2016.05.17  Fix preprocess for pagai
    2015.07.21  Change to os.path component to be compatible with pyinstaller
    2015.07.04  Add 2ls backend
    2015.05.13  Now change to reversed the logfile to find result (may be faster)
    2015.05.11  Add supported preprocess for pagai backend (http://pagai.forge.imag.fr/)
    2015.03.06  Add supported preprocess for llbmc and klee backend
    2015.02.12  Add Frama-C backend
    2015.02.03  Code refactoring
    2015.01.31  Add calling backend in Sequential or Parallel mode + swarm strategy
    2015.01.16  Add logging and fix sequential launch of SWARM
    2014.12.12  Initial version
"""


def printStats(file, result, time, memory=0, verbose=True):
    if result == "UNKNOWN":
        result = utils.colors.YELLOW + result + utils.colors.NO
    elif result == "TRUE":
        result = utils.colors.GREEN + result + utils.colors.NO
    elif result == "FALSE":
        result = utils.colors.RED + result + utils.colors.NO
    string = "%s, %s, %0.2f, %0.2fMB" % (file, result, time, memory/1024.0)
    if verbose:
        print(string)
        sys.stdout.flush()
    return string

def printNoFoundBug(totalTime):
    print("============================================================================")
    print("Cannot found bugs in this configuration")
    print("TIMEOUT, %0.2f" % totalTime)
    sys.stdout.flush()

def printAllTrue(totalTime):
    print("============================================================================")
    print("All instances are safe")
    print("TRUE, %0.2f" % totalTime)
    sys.stdout.flush()

def printInstanceStats(filename, logfilename, instanceTime, totalTime):
    print("============================================================================")
    print("Bug found in instance:", filename)
    print("With logfile:", logfilename)
    # print("And counterexample:", filename[:-1] + "cseq.log")
    print("Backend time: %0.2fs" % instanceTime)
    print("FALSE, %0.2f" % totalTime)
    sys.stdout.flush()

def backendDict():
    # Name of the executable file to run, by backend.
    backendFilename = {}
    # BMC backends
    backendFilename["cbmc"] = "cbmc"    # stable version of CBMC
    backendFilename["esbmc"] = "esbmc"
    backendFilename["llbmc"] = "llbmc"
    backendFilename["blitz"] = "blitz"
    # AI backends
    backendFilename["framac"] = "frama-c"
    backendFilename["2ls"] = "summarizer"
    backendFilename["pagai"] = "pagai"
    backendFilename["interproc"] = "concurinterproc.opt"
    backendFilename["satabs"] = "satabs"
    backendFilename["cpachecker"] = "CPAChecker/scripts/cpa.sh"  # Not working
    # Concolic testing
    backendFilename["smack"] = "smack-verify.py"
    backendFilename["klee"] = "klee"
    # Concurrent program
    backendFilename["concurinterproc"] = "concurinterproc.opt"  # New option for easy checking of result
    backendFilename["impara"] = "impara"
    backendFilename["seahorn"] = "./sea_svcomp"
    backendFilename["general"] = ""
    return backendFilename

def isBackendValid(backend=""):
    import subprocess
    if backend not in backendDict():
        print("error: the current backend %s is not supported\n" % backend)
        sys.exit(2)
    if backend != "cpachecker":
        try:
            backendpath = backendDict()[backend]
            output = subprocess.check_output("which %s" % backendpath, shell=True)
            if output != "":
                return True
        except subprocess.CalledProcessError:
            return False
    return True

def step1SetUpCMD(env):
    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
                      Options & parameters below.
    """""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
    # Name of the executable file to run, by backend.
    backendFilename = backendDict()
    # Command-line parameters, by backend.
    cmdLineOptions = {}
    # BMC backends
    #cmdLineOptions["cbmc"] = " --32 --unwind 1 --no-unwinding-assertions "
    cmdLineOptions["cbmc"] = " --unwind 1 --no-unwinding-assertions "
    cmdLineOptions["esbmc"] = " --no-slice --no-bounds-check --no-div-by-zero-check --no-pointer-check --unwind 1 --no-unwinding-assertions "
    cmdLineOptions["llbmc"] = " -no-max-function-call-depth-checks -no-memory-free-checks -no-shift-checks -no-memcpy-disjoint-checks -no-memory-access-checks -no-memory-allocation-checks --max-loop-iterations=1 --no-max-loop-iterations-checks --ignore-missing-function-bodies -no-overflow-checks -no-div-by-zero-checks "
    cmdLineOptions["blitz"] = "  --terminate-on-firstbug "

    # AI backends
    cmdLineOptions["framac"] = " -val -no-val-show-initial-state -no-val-show-progress -memexec-all -no-results-function __cs_init_scalar -no-unicode "
    cmdLineOptions["2ls"] = " "
    cmdLineOptions["pagai"] = " --no-undefined-check -t s --optimize "
    cmdLineOptions["interproc"] = " -dynamic false -compress false false true "
    cmdLineOptions["satabs"] = " "
    cmdLineOptions["cpachecker"] = " -preprocess -heap 15000M -timelimit 86400 -noout -predicateAnalysis "

    # Testing
    cmdLineOptions["klee"] = " -exit-on-error "
    cmdLineOptions["smack"] = " --unroll 1 "

    # Concurrent verififer
    cmdLineOptions["concurinterproc"] = " -sched cooperative "
    cmdLineOptions["impara"] = " -eager "
    cmdLineOptions["seahorn"] = " -m 32 --spec=ALL.prp -p "

    format = env["backend"]
    depth = env["depth"]

    # Set backend path
    exe = backendFilename[format]

    if env["backend-path"] != "":
        exe = env["backend-path"]

    cmdline = ""
    # BMC
    if format == "esbmc":
        cmdline = exe + cmdLineOptions[format]
        if depth != 0:
            cmdline += " --depth %s " % str(depth)
    elif format == "cbmc":
        cmdline = exe + cmdLineOptions[format]
        if depth != 0:
            cmdline += " --depth %s " % str(depth)
        if env["cex"] or env["stop-on-fail"]:
            cmdline += "--stop-on-fail "
#       if env["stop-on-fail"]:
#           cmdline += " --stop-on-fail "
        if env["bounds-check"]:
            cmdline += " --bounds-check "
        if env["div-by-zero-check"]:
            cmdline += " --div-by-zero-check "
        if env["pointer-check"]:
            cmdline += " --pointer-check "
        if env["memory-leak-check"]:
            cmdline += " --memory-leak-check "
        if env["signed-overflow-check"]:
            cmdline += " --signed-overflow-check "
        if env["unsigned-overflow-check"]:
            cmdline += " --unsigned-overflow-check "
        if env["float-overflow-check"]:
            cmdline += " --float-overflow-check "
        if env["nan-check"]:
            cmdline += " --nan-check "
        if env["no-simplify"]:
            cmdline += " --no-simplify "
        if env["refine-arrays"]:
            cmdline += " --refine-arrays "

    elif format == "blitz":
        cmdline = exe + cmdLineOptions[format]
        if depth != 0:
            cmdline += " --depth %s " % str(depth)
    elif format == "llbmc":
        cmdline = exe + cmdLineOptions[format]

    # AI
    elif format == "framac":
        cmdline = exe + cmdLineOptions[format]
        cmdline += " -slevel %s " % str(depth)
    elif format == "2ls":
        cmdline = exe + cmdLineOptions[format]
        if env["domain"] != "default":
            cmdline += "--%s " % env["domain"]
    elif format == "pagai":
        cmdline = exe + cmdLineOptions[format]
        if env["domain"] != "default":
            cmdline += "-d %s -i " % env["domain"]
        else:
            cmdline += "-i "
    elif format == "interproc":
        cmdline = exe + cmdLineOptions[format]
        if env["domain"] != "default":
            cmdline += "-domain %s" % env["domain"]
    elif format == "satabs":
        cmdline = exe + cmdLineOptions[format]
    elif format == "cpachecker":
        cmdline = exe + cmdLineOptions[format]

    # Testing
    elif format == "smack":
        cmdline = exe + cmdLineOptions[format]
    elif format == "klee":
        cmdline = exe + cmdLineOptions[format]

    # Concurrent backends
    elif format == "concurinterproc":
        cmdline = exe + cmdLineOptions[format]
        if env["domain"] != "default":
            cmdline += "-domain %s" % env["domain"]
    elif format == "impara":
        cmdline = exe + cmdLineOptions[format]
    elif format == "seahorn":
        cmdline = exe + cmdLineOptions[format]
        if env["extra-args"] == "":
            cmdline += "no_inline "
    else:
        print("This backend (%s) is not supported yet" % format)
        sys.exit(2)

    cmdline += env["extra-args"] + " "

    if env["memorylimit"] != -1:
        cmdline = "ulimit -v %s;" % env["memorylimit"] + cmdline

    if env["verbose"]:
        print("cmdline:", cmdline)

    return cmdline

def step2APreprocessLLVM(seqfile, logfilename, backend, clangpath):
    import subprocess
    llvmcmd = ""   # llvm command

    if backend == "llbmc":
        if clangpath == "":    # No supported version from user
            # Check for clang version 3.3 in default search path
            try:
                output = subprocess.check_output("which clang", shell=True)
            except subprocess.CalledProcessError:
                print("error: llbmc requires clang version 3.3 installed in the system")
                sys.exit(2)
            try:
                output = subprocess.check_output("clang --version", shell=True)
                if "version 3.3" not in output:
                    print("error: the current version of clang does not match llbmc requirement (require version 3.3)")
                    sys.exit(2)
                else:
                    llvmcmd = "clang -c -g -emit-llvm %s -o %s" % (seqfile, seqfile[:-2] + ".bc")
            except subprocess.CalledProcessError:
                pass   # supress error
        else:
            llvmcmd = "%s -c -g -emit-llvm %s -o %s" % (clangpath, seqfile, seqfile[:-2] + ".bc")

    if backend == "klee":
        if clangpath == "":    # No supported version from user
            # Check for clang version 3.3 in default search path
            try:
                output = subprocess.check_output("which llvm-gcc", shell=True)
            except subprocess.CalledProcessError:
                print("error: klee requires llvm-gcc version 2.9 installed in the system")
                sys.exit(2)
            try:
                output = subprocess.check_output("llvm-gcc --version", shell=True)
                if "LLVM build 2.9" not in output:
                    print("error: the version of llvm-gcc in the system does not match klee requirement (require version 2.9)")
                    sys.exit(2)
                else:
                    llvmcmd = "llvm-gcc -c -g -emit-llvm %s -o %s" % (seqfile, seqfile[:-2] + ".bc")
            except subprocess.CalledProcessError:
                pass   # supress error
        else:
            # TODO: remember to add this before using KLEE     `ulimit -s unlimited`
            llvmcmd = "%s -c -g -emit-llvm %s -o %s" % (clangpath, seqfile, seqfile[:-2] + ".bc")

    if backend == "pagai":
        try:
            output = subprocess.check_output("which clang-3.5", shell=True)
        except subprocess.CalledProcessError:
            print("error: pagai requires clang installed in the system")
            sys.exit(2)
        # Copy pagai_assert.h to the directory of the files
        execpath = os.path.dirname(sys.argv[0])
        assertfile = execpath + "/backends/pagai/pagai_assert.h"
        shutil.copy(assertfile, os.path.dirname(seqfile))
        # Register compile script for pagai
        llvmscript = execpath + "/backends/pagai/compile_llvm.sh"
        llvmcmd = "%s -g -i %s -o %s" % (llvmscript, seqfile, seqfile[:-2] + ".bc")

    command = utils.Command(llvmcmd)
    out, err, code = command.run(timeout=86400)
    utils.saveFile(logfilename, err)

def step2RunCMD(cmdline, timeout, seqfile, format):
    currentdir = os.path.dirname(sys.argv[0])
    newcmdline = cmdline + seqfile
    if format in ("klee", "llbmc", "pagai"):
        newcmdline = newcmdline[:-2] + ".bc"
    if format in ("seahorn",):
        os.chdir(currentdir + "/backends/SeaHorn/bin")
    # Run command
    command = utils.Command(newcmdline)
    # store stdout, stderr, process" return value
    results = command.run(timeout=timeout)
    
    os.chdir(currentdir) # change back to current dir
    return results

def step3ProcessResult(seqfile,
        format, verbose, counterexample, witness,
        out, err, retcode, memory,
        logfilename, realstarttime, timeBeforeCallingBackend, keepLog=True):

    # Expressions to check for from the log to see whether verification went fine.
    verificationOK = {}
    # BMC backends
    verificationOK["esbmc"] = "VERIFICATION SUCCESSFUL"
    verificationOK["cbmc"] = "VERIFICATION SUCCESSFUL"
    verificationOK["blitz"] = "VERIFICATION SUCCESSFUL"
    verificationOK["llbmc"] = "No error detected."
    # AI
    verificationOK["framac"] = "__FRAMAC_spec"
    verificationOK["2ls"] = "VERIFICATION SUCCESSFUL"
    verificationOK["pagai"] = "RESULT: TRUE"       #  TODO
    verificationOK["interproc"] = "TOBEPROCESSED"
    verificationOK["satabs"] = "VERIFICATION SUCCESSFUL"
    verificationOK["cpachecker"] = "Verification result: SAFE. No error path found by chosen configuration."
    # Testing
    verificationOK["klee"] = "NOSUCHTHINGFORKLEE"
    verificationOK["smack"] = "Finished with 1 verified, 0 errors"
    # Concurrent
    verificationOK["concurinterproc"] = "TOBEPROCESSED"
    verificationOK["impara"] = "VERIFICATION SUCCESSFUL"
    verificationOK["seahorn"] = "BRUNCH_STAT Result TRUE"

    # Expressions to check for from the log to check whether verification failed.
    verificationFAIL = {}
    # BMC
    verificationFAIL["cbmc"] = "VERIFICATION FAILED"
    verificationFAIL["esbmc"] = "VERIFICATION FAILED"
    verificationFAIL["blitz"] = "VERIFICATION FAILED"
    verificationFAIL["llbmc"] = "Error detected."
    # AI
    verificationFAIL["framac"] = "__FRAMAC_spec"
    verificationFAIL["2ls"] = "VERIFICATION FAILED"
    verificationFAIL["pagai"] = "RESULT: UNKNOWN"
    verificationFAIL["interproc"] = "TOBEPROCESSED"
    verificationFAIL["satabs"] = "VERIFICATION FAILED"
    verificationFAIL["cpachecker"] = "Verification result: UNSAFE."
    # testing
    verificationFAIL["smack"] = "Finished with 0 verified,"
    verificationFAIL["klee"] = "ASSERTION FAIL: "
    # Concurrent
    verificationFAIL["concurinterproc"] = "TOBEPROCESSED"
    verificationFAIL["impara"] = "VERIFICATION FAILED"
    verificationFAIL["seahorn"] = "BRUNCH_STAT Result FALSE"

    # report analysis details

    outcome = ""
    cex = ""
    overalltime = time.time() - realstarttime
    backendtime = time.time() - timeBeforeCallingBackend
    mem = maxmem = variables = clauses = 0

    if out != "":
        backendAnswer = out if format != "klee" else err

        if format in ("cbmc", "esbmc",):
            for line in backendAnswer.splitlines():
                if " variables, " in line:
                    splitline = line.split()
                    variables = splitline[0]
                    clauses = splitline[2]
                if verificationOK[format] in line:
                    outcome = "TRUE"
                    break
                elif verificationFAIL[format] in line:
                    outcome = "FALSE"
                    break
        elif format == "concurinterproc":
            if retcode != 0:
                outcome = "UNKNOWN"
            if retcode == -9:
                outcome = "TIMEOUT"
            for line in reversed(backendAnswer.splitlines()):
                if "ERROR" in line:
                    if "bottom" not in line:
                        outcome = "UNKNOWN"
                        break
            if outcome != "UNKNOWN" and outcome != "TIMEOUT":
                outcome = "TRUE"
        else:   # Other backends
            for line in reversed(backendAnswer.splitlines()):
                # this works only with CBMC and ESBMC,
                # example: 2174 variables, 5558 clauses

                if format == "interproc":
                    outcome = "TRUE"
                else:
                    if verificationOK[format] in line:
                        if format == "framac":
                            if "{0}" in line:
                                outcome = "TRUE"
                            else:
                                outcome = "UNKNOWN"
                        else:
                            outcome = "TRUE"
                        break
                    elif verificationFAIL[format] in line:
                        if format == "pagai":
                            outcome = "UNKNOWN"
                        else:
                            outcome = "FALSE"
                        break

        if outcome == "" and retcode == -9:  # backend killed due to timeout
            outcome = "TIMEOUT"
        if outcome == "":
            outcome = "UNKNOWN"

        # Report statictis
        if verbose:
            print("file:   %s" % seqfile)
            print("")
            print("size:   %s variables" % variables)
            print("        %s clauses" % clauses)
            print("")
            print("space:  %s " % mem)
            print("        %s peak" % maxmem)
            print("")
            print("time:   %0.2fs preprocess" % (timeBeforeCallingBackend - realstarttime))
            print("        %0.2fs backend" % (backendtime))
            print("        %0.2fs overall" % (overalltime))
            print("")
            if outcome == "FALSE":
                print(utils.colors.RED + "        FALSE" + utils.colors.NO)
            elif outcome == "TRUE":
                print(utils.colors.GREEN + "        TRUE" + utils.colors.NO)
            elif outcome == "TIMEOUT":
                print(utils.colors.YELLOW + "        TIMEOUT" + utils.colors.NO)
            elif outcome == "UNKNOWN":
                print(utils.colors.YELLOW + "        UNKNOWN" + utils.colors.NO)
            if "warning" in err:
                print(utils.colors.YELLOW + "       (warnings on stderr from the backend)" + utils.colors.NO)
            print("")

        if format != "klee":
            utils.saveFile(logfilename, out)   # klee outputs errors to stdout
        else:
            utils.saveFile(logfilename, err)    # all other backends to stderr

        if outcome == "FALSE" and counterexample:
            # Write counterexample to inputfile (this file will get overwrite if there is more cex)
            cexGen = CEX(seqfile, backendAnswer)
            cexGen.produceCEX()
            cex = cexGen.output
            # save to witness file
            utils.createFolder(witness)
            with open(witness + "/" + os.path.basename(seqfile) + ".cex", "w") as witnessfile:
                witnessfile.write(cex)

            if verbose:
                print(cex)

        if not keepLog:
            try:
                os.remove(logfilename)
            except os.error as e:
                print(str(e))
    else:
        outcome = "UNKNOWN"

    sys.stdout.flush()

    return outcome, backendtime, overalltime, memory, cex

def callBackend(env, seqfile, realstarttime, logger=None):
    format = env["backend"]
    # Setting up CMD
    cmdline = step1SetUpCMD(env)
    logfilename = seqfile + "." + format + ".log"

    if env["verbose"]:
        print("output: %s" % (seqfile))
    if env["verbose"]:
        print("log:    %s\n" % (logfilename))
    if env["verbose"]:
        print("cmd:   %s\n" % (cmdline + seqfile))
    if env["verbose"]:
        print("start:  %s\n" % (strftime("%Y-%m-%d %H:%M:%S", gmtime())))

    timeBeforeCallingBackend = time.time()    # save wall time
    if format in ("klee", "llbmc", "pagai"):
        step2APreprocessLLVM(seqfile, logfilename, format, env["clang-path"])

    # Run command
    out, err, retcode, memory = step2RunCMD(cmdline, env["timelimit"], seqfile, format)

    outcome, backendtime, overalltime, memory, cex = step3ProcessResult(seqfile,
        format, env["verbose"], env["cex"], env["witness"],
        out, err, retcode, memory,
        logfilename, realstarttime, timeBeforeCallingBackend)
    return outcome, overalltime

def start_process():
    """ Put some debug information here if wanted
    """
    pass

def backendWorker(cmdline):
    (cmd, format, inputfile, logfilename, timeout, keepLog, clangPath, verbose, cex, witness) = cmdline
    #time.sleep(3*(index+1))
    #print"PIPPO %d" % (index+1)
    #eturn (inputfile, "FALSE", 1, 1)
    timeBeforeCallingBackend = time.time()    # save wall time

    if format in ("klee", "llbmc", "pagai"):
        step2APreprocessLLVM(inputfile, logfilename, format, clangPath)

    out, err, code, memory = step2RunCMD(cmd, timeout, inputfile, format)
    out = out.decode()
    err = err.decode()
    outcome, backendtime, overalltime, memory, cex = step3ProcessResult(inputfile,
        format, verbose, cex, witness,
        out, err, code, memory,
        logfilename, 0, timeBeforeCallingBackend,
        keepLog=keepLog)
    if not verbose:
        printStats(inputfile, outcome, backendtime, memory)
    return (inputfile, outcome, backendtime, memory, time.time())
          
def callBackendSwarm(env, listFile, realstarttime, logger=None, instanceIterator=None):
    if instanceIterator == None:
        seqfileList, result = translator_handler.step5GetFileListNormal(listFile)
        format = env["backend"]
        # Setting up CMD
        cmdline = step1SetUpCMD(env)
        if env["execution-mode"] == "sequential":
            initalTimeout = env["initial-timeout"]
            foundBug = False
            allTrue = False
            noInstance = len(seqfileList)  # number of instances
            ignoreFileList = {}
            instanceName = ""
            instanceLog = ""
            instanceTimeBackend = 0
            while initalTimeout <= env["timelimit"]:   # Sequential loop until reach time limit
                if foundBug or allTrue:     # Break when found bugs or all instance are true
                    break
                print("Analyzing %s instance(s) SEQUENTIALLY with %ss timeout for each instance" % (noInstance, initalTimeout))
                print("============================================================================")
                sys.stdout.flush()
                # Run backend through seq file list
                for seqf in seqfileList:
                    if seqf in ignoreFileList:
                        continue       # Next if this file is already processed
                    logfilename = seqf + "." + format + ".log"
                    timeBeforeCallingBackend = time.time()    # save wall time
                    if format in ("klee", "llbmc", "pagai"):
                        step2APreprocessLLVM(seqf, logfilename, format, env["clang-path"])
                    out, err, code, memory = step2RunCMD(cmdline, initalTimeout, seqf, format)
                    outcome, backendtime, overalltime, memory, cex = step3ProcessResult(seqf,
                        format, env["verbose"], env["cex"], env["witness"],
                        out, err, code, memory,
                        logfilename, realstarttime, timeBeforeCallingBackend,
                        keepLog=env["keep-logs"])
                    if not env["verbose"]:
                        printStats(seqf, outcome, backendtime, memory)
                    if outcome == "FALSE":
                        foundBug = True
                        instanceName = seqf
                        instanceLog = logfilename
                        instanceTimeBackend = backendtime
                        if env["exit-on-error"] is True:
                            break
                    if outcome == "TRUE":
                        ignoreFileList[seqf] = True
                        noInstance -= 1
                        if noInstance == 0:
                            allTrue = True
                # Modifying timeout
                if env["incremental"]:
                    if initalTimeout == env["timelimit"]:
                        break
                    initalTimeout *= 2
                    if initalTimeout > env["timelimit"]:
                        initalTimeout = env["timelimit"]
                else:
                    break
                print("============================================================================")
            totalTime = time.time() - realstarttime
            if foundBug:
                printInstanceStats(instanceName, instanceLog, instanceTimeBackend, totalTime)
            # with split-config other instances will potentially follow, cannot anticipate the result
            elif allTrue and not env["split-config"]:
                printAllTrue(totalTime)
            elif not env["split-config"]:
                printNoFoundBug(totalTime)
            return foundBug,totalTime
        elif env["execution-mode"] == "parallel":   # Parallel execution, preparing for cluster
            initalTimeout = env["initial-timeout"]
            foundBug = False
            noInstance = len(seqfileList)
            while initalTimeout <= env["timelimit"]:
                # create jobs for all workers
                joblist = []
                for seqf in seqfileList:
                    logfilename = seqf + "." + format + ".log"
                    cmdpack = (cmdline, format, seqf, logfilename, initalTimeout, env["keep-logs"], env["clang-path"],
                               env["verbose"], env["cex"], env["witness"])
                    joblist.append(cmdpack)

                # Spawning multiple process in a pool
                pool_size = multiprocessing.cpu_count()  # for cores of cpu
                if pool_size > len(joblist):
                    pool_size = len(joblist)

                pool_size = env["cores"]

                print("Analyzing %s instance(s) with %ss timeout for %s processes" % (noInstance, initalTimeout, pool_size))
                print("============================================================================")

                sys.stdout.flush()
                pool = multiprocessing.Pool(processes=pool_size, initializer=start_process)
                try:
                    for out in pool.imap(backendWorker, joblist):
                        if "FALSE" in out:
                            foundBug = True
                            totalTime = time.time() - realstarttime
                            if env["exit-on-error"]:
                                print("Bug found in: %0.2fs" % totalTime)
                                sys.stdout.flush()
                                pool.close()
                                pool.terminate()
                                pool.join()
                                break
                except KeyboardInterrupt as e:
                    print("Interupted by user")
                    pool.terminate()
                    pool.close()
                    pool.join()

                # Stop pool nicely
                pool.close()
                pool.join()

                # if foundBug:
                #     break

                # Modifying timeout
                if env["incremental"]:
                    if initalTimeout == env["timelimit"]:
                        break
                    initalTimeout *= 2
                    if initalTimeout > env["timelimit"]:
                        initalTimeout = env["timelimit"]
                else:
                    break
                print("============================================================================")
                sys.stdout.flush()
            # Calculate overall time
            overalltime = time.time() - realstarttime
            if foundBug:
                print("===================================================")
                print("Found bugs in this configuration")
                print("Found time: %0.2fs " % totalTime)
                print("FALSE, %0.2fs" % overalltime)
                sys.stdout.flush()
            # with split-config other instances are potentially running, cannot anticipate the result
            elif not env["split-config"]:
                print("===================================================")
                print("Cannot found bugs in this configuration")
                print("TRUE, %0.2fs" % overalltime)
                sys.stdout.flush()
            return foundBug,overalltime

    else:
        format = env["backend"]
        # Setting up CMD
        cmdline = step1SetUpCMD(env)
        if env["execution-mode"] == "sequential":
            initalTimeout = env["initial-timeout"]
            foundBug = False
            allTrue = False
            #noInstance = len(seqfileList)  # number of instances
            ignoreFileList = {}
            instanceName = ""
            instanceLog = ""
            instanceTimeBackend = 0
            print("Analyzing instance(s) SEQUENTIALLY with %ss timeout for each instance" % (initalTimeout))
            print("============================================================================")
            sys.stdout.flush()
                # Run backend through seq file list
            for index in instanceIterator:
               seqfileList, result = translator_handler.step5GetFileListNormal(listFile)
               for seqf in seqfileList:
                    if seqf in ignoreFileList:
                        continue       # Next if this file is already processed

                    logfilename = seqf + "." + format + ".log"
                    timeBeforeCallingBackend = time.time()    # save wall time

                    if format in ("klee", "llbmc", "pagai"):
                        step2APreprocessLLVM(seqf, logfilename, format, env["clang-path"])

                    out, err, code, memory = step2RunCMD(cmdline, initalTimeout, seqf, format)

                    outcome, backendtime, overalltime, memory, cex = step3ProcessResult(seqf,
                        format, env["verbose"], env["cex"], env["witness"],
                        out, err, code, memory,
                        logfilename, realstarttime, timeBeforeCallingBackend,
                        keepLog=env["keep-logs"])

                    if not env["verbose"]:
                        printStats(seqf, outcome, backendtime, memory)

                    if outcome == "FALSE":
                        foundBug = True
                        instanceName = seqf
                        instanceLog = logfilename
                        instanceTimeBackend = backendtime
                        if env["exit-on-error"]:
                            break

                    #if outcome == "TRUE":
                    #    ignoreFileList[seqf] = True
                    #    noInstance -= 1
                    #    if noInstance == 0:
                    #        allTrue = True

               if foundBug and env["exit-on-error"]:
                     break

                # Modifying timeout
                #if env["incremental"]:
                #  if initalTimeout == env["timelimit"]:
                #      break
                #  initalTimeout *= 2
                #  if initalTimeout > env["timelimit"]:
                #      initalTimeout = env["timelimit"]
                #else:
                #  break
                #print "============================================================================"

            totalTime = time.time() - realstarttime
            if foundBug:
                printInstanceStats(instanceName, instanceLog, instanceTimeBackend, totalTime)
            # with split-config other instances will potentially follow, cannot anticipate the result
            elif allTrue and not env["split-config"]:
                printAllTrue(totalTime)
            elif not env["split-config"]:
                printNoFoundBug(totalTime)
            return foundBug,totalTime

        elif env["execution-mode"] == "parallel":
            initalTimeout = env["initial-timeout"]
            foundBug = False

            def getJobIterator(iterator):
                for index in iterator:
                    try:
                        seqfileList, result = translator_handler.step5GetFileListNormal(listFile)
                        for seqf in seqfileList:
                            logfilename = seqf + "." + format + ".log"
                            cmdpack = (cmdline, format, seqf, logfilename, initalTimeout, env["keep-logs"], env["clang-path"],
                                       env["verbose"], env["cex"], env["witness"])
                            yield cmdpack

                    except StopIteration as e:
                        sys.exit(0)

            manager = multiprocessing.Manager()
            results = manager.Queue()

            def logResults(out):
                 results.put(out)
            #    event.set()

            #interrupted = False
            pool_size = multiprocessing.cpu_count()  # for cores of cpu
            pool_size = env["cores"]
            print("Analyzing instance(s) with %ss timeout for %s processes" % (initalTimeout, pool_size))
            print("============================================================================")
            sys.stdout.flush()
            pool = multiprocessing.Pool(processes=pool_size, initializer=start_process)

            # create jobs for all workers
            jobIterator = getJobIterator(instanceIterator)
            #while initalTimeout <= env["timelimit"]:
                # Spawning multiple process in a pool
                #    joblist.append(cmdpack)
            sentinel = object()
            try:
                for i in range(0, pool_size):
                    job = next(jobIterator, sentinel)
                    if job is sentinel:
                        break
                    pool.apply_async(backendWorker, args=(job,), callback=logResults)
                out = results.get()
                if "FALSE" in out:
                    x,y,z,w,t = out
                    foundBug = True
                    totalTime = t - realstarttime
                    if env["exit-on-error"]:
                        print("Bug found in: %0.2fs" % totalTime)
                        sys.stdout.flush()
                        pool.terminate()
                        pool.close()
                        pool.join()
            except KeyboardInterrupt as e:
                print("Interupted by user")
                #interrupted = True
                pool.terminate()
                pool.close()
                pool.join()


            # Stop pool nicely
            pool.close()
            pool.join()
            #if interrupted or (env["exit-on-error"] and foundBug):
            #          break
            if not foundBug:
               while not results.empty():
                  out = results.get(False)
                  x,y,z,w,t = out
                  totalTime = t - realstarttime
                  if "FALSE" in out:
                      foundBug = True
                      break

            # Calculate overall time
            overalltime = time.time() - realstarttime
            if foundBug:
                print("===================================================")
                print("Bugs found in this configuration")
                print("Found time: %0.2fs " % totalTime)
                print("FALSE, %0.2fs" % overalltime)
                sys.stdout.flush()
            # with split-config other instances are potentially running, cannot anticipate the result
            elif not env["split-config"]:
                print("===================================================")
                print("Cannot find bugs in this configuration")
                print("TRUE, %0.2fs" % overalltime)
                sys.stdout.flush()
            #print "PID %s" % os.getpid()
            #os.killpg(os.getpid(),signal.SIGKILL)
            os.system("killall -q -9 cbmc")
            return foundBug, overalltime

def callBackendSwarmSA(env, seqfileList, realstarttime, logger=None):
    format = env["backend"]
    # Setting up CMD
    cmdline = step1SetUpCMD(env)
    # Begin business here
    timeout = env["timeout"]
    realstarttime = time.time()
    if env["execution-mode"] == "sequential":  # Sequential analyzing
        noInstance = len(seqfileList)  # number of instances
        candidateList = {}
        m = "Analyzing %s instance(s) SEQUENTIALLY with %ss timeout for each" % (noInstance, env["timeout"])
        logger.record(m + "\n")
        print(m)
        print("============================================================================")
        sys.stdout.flush()
        for seqf in seqfileList:
            timeBeforeCallingBackend = time.time()    # save wall time
            logfilename = seqf + "." + format + ".log"
            if format in ("klee", "llbmc", "pagai"):
                step2APreprocessLLVM(seqf, logfilename, format, env["clang-path"])

            out, err, code, memory = step2RunCMD(cmdline, timeout, seqf, format)
            outcome, backendtime, overalltime, memory, cex = step3ProcessResult(seqf,
                format, env["verbose"], env["cex"], env["witness"],
                out, err, code, memory,
                logfilename, realstarttime, timeBeforeCallingBackend,
                keepLog=env["keep-logs"])

            if not env["verbose"]:
                printStats(seqf, outcome, backendtime, memory)

            if outcome == "FALSE":
                candidateList[seqf] = backendtime
                if timeout > backendtime:
                    timeout = int(backendtime+1)

        # Calculate overall time
        overalltime = time.time() - realstarttime
        logger.record("Finish in %0.2fs\n" % overalltime)
        print("========================================================")
        print("Finish analyzing all instances in %0.2fs" % overalltime)
        print("========================================================")
        print("============================================================================")
        sys.stdout.flush()
        # Set up thing before return
        env["timeout"] = timeout
        return candidateList
    if env["execution-mode"] == "parallel":  # Parallel
        candidateList = {}
        noInstance = len(seqfileList)
        # create jobs for all workers
        joblist = []
        for seqf in seqfileList:
            logfilename = seqf + "." + format + ".log"
            cmdpack = (cmdline, format, seqf, logfilename, timeout, env["keep-logs"], env["clang-path"],
                        env["verbose"], env["cex"], env["witness"])
            joblist.append(cmdpack)
        # Spawning multiple process in a pool
        pool_size = env["cores"]
        m = "Analyzing %s instance(s) IN PARALLEL with %ss timeout for %s process(es)" % (
            noInstance, timeout, pool_size)
        logger.record(m + "\n")
        print(m)
        print("============================================================================")
        sys.stdout.flush()
        pool = multiprocessing.Pool(processes=pool_size, initializer=start_process)
        for out in pool.imap(backendWorker, joblist):
            mess = "%s, %s, %s" % (out[0], out[1], out[2])
            logger.record(mess + "\n")
            if "FALSE" in out:
                instanceName = out[0]
                instanceTimeBackend = out[2]
                candidateList[instanceName] = instanceTimeBackend
                if timeout > instanceTimeBackend:
                    timeout = int(instanceTimeBackend+1)
        # Stop pool nicely
        pool.close()
        pool.join()
        env["timeout"] = timeout
        # Calculate overall time
        overalltime = time.time() - realstarttime
        logger.record("Finish in %0.2fs\n" % overalltime)
        print("========================================================")
        print("Finish analyzing all instances in %0.2fs" % overalltime)
        print("========================================================")
        print("============================================================================")
        sys.stdout.flush()
        return candidateList
