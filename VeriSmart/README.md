# VeriSmart

Built upon Lazy-CSeq 2.0

## Package contents

| File/Directory | Description                     |
| -------------- | ------------------------------- |
| verismart.py   | VeriSmart wrapper script        |
| lazycseq.py    | Lazycseq wrapper script         |
| cseq-feeder.py | Complete tool script            |
| bin/           | VeriSmart modules               |
| core/          | Lazy-CSeq core framework        |
| modules/       | modules and configuration files |
| examples/      | example files                   |
| LICENSE        | VeriSmart license               |
| LICENSE-CSeq   | CSeq framework license          |
| CBMC_LICENSE   | CBMC license                    |
| README.md      | this file                       |

## Installation

To install VeriSmart, please follow the steps below:

    1. (locally) install the dependencies for Python 3:
        - Python 3.8
        - PYCParser 2.20 (pip3 install --user pycparser==2.20)
        - ijson (pip3 install --user ijson)
        - CBMC (available from http://www.cprover.org/cbmc/) 
          note that we tested VeriSmart with CBMC v5.11 only
        - g++-multilib (apt install g++-multilib)
        - libopenmpi-dev
    
    2. create a directory, suppose this is called /workspace
    
    3. extract the entire package contents into /workspace
    
    4. cd /workspace
    
    5. set execution (+x) permissions for verismart.py, cseq-feeder.py 
    and lazycseq.py

## Usage

The general usage of VeriSmart is 

   ./verismart.py [options] -i FILE (.c)

For example,  

    ./verismart.py -i examples/lazy_unsafe.c 

generates all possible five instances and runs the default verification backend
over the number of threads started (default: 4). This finds a bug in third
configuration attempted.

VeriSmart produces a configuration file FILE_auto_config.json and a directory
FILE.swarm with the sequentialized instance files and their CBMC logs.

The number of threads that are started can be modified with the --cores option:

    ./verismart.py --cores 2 -i examples/lazy_unsafe.c 

only starts up two threads but this still finds the error quickly.

The window length can be specified with the --window-length (or -l) option; the
argument gives the number of visible statements in the tile:

    ./verismart.py -l 2 -i examples/lazy_unsafe.c 

produces only three configuations but still finds the error. Alternatively, the
window length can be specified via the --window-percent option as percentage of
the threads' length; this needs to be used with care because small percentages
can lead to empty windows.

The (maximum) number of tiles selected in each thread can be controlled by the
--picked-window (or -p) option; for example, 

    ./verismart.py -p 2 -i examples/lazy_unsafe.c 

picks two tiles in each thread, if the thread is actually long enough to allow
this, and so generates ten configurations, of which four demonstrate the error.
We can force the analysis to stop after the first error using the
--exit-on-error option; note that other pending tasks may still finish (and so
actually produce multiple errors), due to delays in killing the processes.

The --shift-window option allows VeriSmart to randomly shift the windows up and
down by half a window size. This has empirically shown to lead to better
results.

The number of configurations can grow large very quickly, in particular for
small window lengths and larger numbers of picked windows; it can be limited
with the --instances-limit option:

    ./verismart.py --instances-limit 2 -i examples/lazy_unsafe.c 

Note that VeriSmart chooses random configurations if the instance limit (which
defaults to 100) is smaller than the number of possible instances.  Hence,
different runs can yield different results, and may fail to find the error.

VeriSmart also provides options to controll the loop unrolling done by
Lazy-CSeq:

    -u<X>, --unwind<X>       sets the unwind bound for all loops
    -w<X>, --while-unwind<X> sets the unwind bound for potentially 
                             unbounded loops
    -f<X>, --for-unwind<X>   sets the unwind bound for bounded loops
    -r<X>, --rounds<X>       sets the number of round-robin schedules

All bounds default to one. Similarly, VeriSmart also provides options to
controll the backend; the --help (or -h) option lists them in more detail.

By default, VeriSmart manages the full verification process: it generates the
configuraion and instance files, and runs the verification backend over all
instances on a single machine. However, this can be changed: VeriSmart can stop
after generating the configuraion and instance files, respectively, so that the
verification can in a second stage be re-started on a different machine (or at
a later time); it can also generate a set of configuration files that can can
then be used to run several instances of VeriSmart in parallel, e.g., on a
cluster.

Specifically, with the --config-only option, VeriSmart
stops afer writing the configuration file:

    ./verismart.py --config-only -i examples/lazy_unsafe.c

Note that the contents of this file depend on any other control parameters such
as -l or -p.  These configuration files can then independently be used with the
--config-file (or -c) option to re-start the verification process;
configuration files can also be created manually or by other tools.

Similarly, with the --instances-only option, VeriSmart stops afer 
writing the instance files (i.e., the sequentialized program
variants):

    ./verismart.py --instances-only -i examples/lazy_unsafe.c

Finally, VeriSmart can also be used to generate a set of configuration
files, each describing the specified number of configurations:

    ./verismart.py --cluster-config 2 examples/lazy_unsafe.c

This can then be used in a second stage to run several instances 
of VeriSmart in parallel, each using the --config-file option to 
read one of the generated configuration files and then to generate
and verify the described instances.

To try a more complicated example, run

  ./verismart.py -i examples/elimination-backoff-stack.c -p2 -l12 -r2 --instances-limit 20 --timeout 500 --cores 5

Note that you need to increase the --instances-limit --timeout, --cores, or -l 
to find the error, depending on the hardware.
