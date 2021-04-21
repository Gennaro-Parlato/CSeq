#!/usr/bin/env python3
import os.path
import subprocess
import shlex
import os
import os.path
import sys
import getopt

from bin import log_handler


def main(args):
	cmd = args[0]
	cmdline = os.path.dirname(sys.argv[0]) + "/"
	from bin import config
	cmdline += config.relpath["translator"]
	for argument in args[1:]:
		if "-h" in argument:
			os.system(cmdline + " -h")
			sys.exit(0)
		if "-H" in argument:	
			os.system(cmdline + " -H")
			sys.exit(0)
		cmdline += " %s" % argument
	#print(cmdline)
	os.system(cmdline)
	sys.exit(0)


if __name__ == "__main__":
	main(sys.argv[0:])
