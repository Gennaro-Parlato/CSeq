import re
import signal
import subprocess
import threading
import json
import os
import os.path
import itertools
import random
import sys
import resource
import shlex
import time
import math

"""
TODO:
	- fix bug of consuming all memory

Changelog:
	2018.07.09  Split config file in fixed-size bags using a generator (full memory bug ok?)
	2016.10.27  Add option to pick windows deterministically
	2016.10.27  Add option to pick non consecutive windows
	2015.06.24  Add Warning when the number of combinations for a thread is extremely large
	2015.01.19  Add feature of generating configuration
	2015.01.14  Fix crashing memory when using itertools.product
"""


""" Reverse replace
"""
def rreplace(s, old, new, occurrence):
	li = s.rsplit(old, occurrence)
	return new.join(li)


""" Write to a file the contents of a string.
"""
def saveFile(filename, string):
	try:
		outfile = open(filename, "w")
		# outfile = open(filename,"w")
		outfile.write(str(string))
		outfile.close()
	except IOError:
		pass


def is_float_try(str):
	try:
		float(str)
		return True
	except ValueError:
		return False


class colors:
	BLINK = "\033[5m"
	BLACK = "\033[90m"
	DARKRED = "\033[31m"
	RED = "\033[91m"
	GREEN = "\033[92m"
	YELLOW = "\033[93m"
	BLUE = "\033[94m"
	NO = "\033[0m"


#  Changes:
#       2015.06.16:   Fix killing child process
#


class Command(object):
	status = None
	output = stderr = ""

	def __init__(self, cmdline):
		self.cmd = cmdline
		self.process = None

	def run(self, timeout):
		def target():
			# Thread started
			self.process = subprocess.Popen(self.cmd, shell=True, preexec_fn=os.setsid, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
			self.output, self.stderr = self.process.communicate()
			# Thread finished

		thread = threading.Thread(target=target)

		try:
			thread.start()
			thread.join(float(timeout))

			if thread.is_alive():
				# Terminating process
				# self.process.terminate()
				# os.killpg(self.process.pid, signal.SIGTERM)
				os.killpg(self.process.pid, signal.SIGKILL)
				thread.join()
		except KeyboardInterrupt:
		   # print "Interrupted by user"
			# self.process.terminate()
		   # print "%s" % self.process.pid
			os.killpg(self.process.pid, signal.SIGKILL)
		finally:
			os.chdir(os.path.dirname(sys.argv[0])) # change back to current dir

		memsize = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
		return self.output, self.stderr, self.process.returncode, memsize


def choose(n, k):
	"""
	A fast way to calculate binomial coefficients by Andrew Dalke (contrib).
	"""
	if 0 <= k <= n:
		ntok = 1
		ktok = 1
		for t in range(1, min(k, n - k) + 1):
			ntok *= n
			ktok *= t
			n -= 1
		return ntok // ktok
	else:
		return 0


def binomial_coefficients(n, k, consecutive=True):
	if consecutive:
		return choose(n, k)
	else:
		if n-k+1 < k:
			print("The number of picked windows (%s) is too large comparing to the number of context switches (%s)" % (k, n))
			sys.exit(1)
		return choose(n-k+1, k)


def parseConfig(inputfile):
	try:
		input = open(inputfile)
		config = json.load(input)
		input.close()
		return config
	except IOError as e:
		raise IOError("Please input configuration file\n")
		sys.exit(2)
	except ValueError:
		raise ValueError("Please input correct configuration file\n")
		sys.exit(2)


def preprocessConfigFile(inputfile, limit):
	config = parseConfig(inputfile)
	newinputfile = inputfile[:inputfile.rfind(".json")] + "_select_%s.json" % limit
	newconfig = {}
	if limit > len(config):
		newconfig = config
	else:
		keylist = random.sample(config.keys(), limit)
		for k in keylist:
			newconfig[k] = config[k]
	try:
		with open(newinputfile, "w") as outfile:
			json.dump(newconfig, outfile)
	except TypeError as e:
		raise e
		sys.exit(2)
	return newinputfile


def list2dict(a):
	b = {}
	for i in a:
		b[i] = True
	return b


def calculateProduct(pack):
	total = 1
	string = []
	for item in pack:
		temp = len(item)
		try:
		  total *= temp
		except OverflowError as err: 
		  total = 1000000000000000000000
		string.append(str(temp))

	string = "x".join(string)
	return total, string


def checksamples(samples, consecutive):
	if consecutive:   # Allow consecutive windows
		for i in range(0, len(samples) - 1):
			if samples[i+1] <= samples[i] + 1:     # Old choice for double windows (not scatter)
				return False
		return True
	else:     # Scatter windows
		for i in range(0, len(samples) - 1):
			if samples[i+1] <= samples[i] + 2:
				return False
		return True


def generateCombinationDoubleWindowsRandomize(seq, r, limit, consecutive=True):
	random.seed()    # Initialize randomize
	if limit == 0: limit = 1000
	totalCombinations = binomial_coefficients(len(seq), r, consecutive=consecutive)
	# print "totalCombinations", totalCombinations
	loopbound = min(totalCombinations, limit)
	# print len(seq), totalCombinations, loopbound
	timeout = time.time() + 60   # 1 min timeout
	i = 0
	while True:
		if time.time() > timeout or i >= loopbound:
			break
		samples = random.sample(range(len(seq)-1), r)
		samples.sort()     #  select increasing number of indices
		if checksamples(samples, consecutive):
			i += 1
			doublesamples = [0]*(2*r)
			for j in range(0, len(samples)):
				doublesamples[2*j] = samples[j]
				doublesamples[2*j+1] = samples[j]+1
			# print doublesamples
			yield [seq[j] for j in doublesamples]


def generateCombinationDoubleWindows(seq, r, limit, consecutive=True):
	if limit == 0: limit = 1000
	totalCombinations = binomial_coefficients(len(seq), r, consecutive=consecutive)
	# print "totalCombinations", totalCombinations
	loopbound = min(totalCombinations, limit)
	# print len(seq), totalCombinations, loopbound
	timeout = time.time() + 60   # 1 min timeout
	i = 0
	while True:
		if time.time() > timeout or i >= loopbound:
			break
		for samples in itertools.combinations(range(len(seq)-1), r):
			newsamples = list(samples)
			newsamples.sort()     #  select increasing number of indices
			if checksamples(newsamples, consecutive):
				i += 1
				doublesamples = [0]*(2*r)
				for j in range(0, len(newsamples)):
					doublesamples[2*j] = newsamples[j]
					doublesamples[2*j+1] = newsamples[j]+1
				# print doublesamples
				yield [seq[j] for j in doublesamples]


def generateCombinations(seq, r, total, consecutive=True, limit=0, randomness=True):
	""" Return  (limit) number of  (random) combination, iterator
	"""
	if total > 10000000:      # Just make it faster
		total = 10000000
	sample = {}
	if limit > 0:
		if randomness:
			sample = list2dict(random.sample(range(total), limit))
		else:
			sample = list2dict(range(limit))
	if consecutive:
		i = 0
		count = 0
		for t in itertools.combinations(seq, r):
			if not sample or i in sample:
				yield t
				count += 1
				if count == limit:
					break
			i += 1
	else:     # Non consecutive generation
		# http://stackoverflow.com/questions/15421886/generating-non-consecutive-combinations
		count = 0
		total = 0
		stack = [(0, r, ())]
		while stack:
			j, r, prev = stack.pop()
			if r == 0:
				if not sample or count in sample:
					yield prev
					total += 1
					if total == limit:
						break
				count += 1
			else:
				for i in range(len(seq)-1, j-1, -1):
					stack.append((i+2, r-1, prev + (seq[i],)))


class ConfigGenerator():

	def __init__(self, data, percent, clusterConfig, windowWidth, windowPercent, pickWindow, instanceslimit, configonly,
					consecutive=True, memoryguard=True, double=False, skiplist={}):
		"""
			data: threads specs
			windowWidth: length of windows
			pickWindow: number of windows
			instanceslimit: the number of instances
			consecutive: whether the windows are consecutive
			memoryguard: automatic prevent memory consumption when the number is huge
			double: choose double windows
		"""
		self.data = data
		self.generatedData = {}   # This object is for json file
		self.percent= percent
		self.windowWidth = windowWidth
		self.windowPercent = windowPercent
		self.realWindowWidth = windowWidth
		self.realWindowPercent = windowPercent
		self.pickWindow = pickWindow
		self.limit = instanceslimit
		self.consecutive = consecutive
		self.memoryguard = memoryguard
		self.double = double    # shift windows
		self.configonly = configonly
		self.clusterConfig = clusterConfig
		 
		if self.double:     # Double mean window is shifted up or down, that is why
						    # the width need to be halved
			if percent: 
				self.windowPercent = int(self.windowPercent/2)
			elif self.windowWidth > 1:
				self.windowWidth = int(self.windowWidth/2)
			else: 
				self.double=False

		self.skiplist = skiplist

	def generatingManualConfigString(self):
		return json.dumps(self.generatedData, indent=4, separators=(",", ": "))

	def generatingManualConfig(self, outputfile):
		# Read context switch line
		lines = self.data.splitlines()
		self.data = {}
		for l in lines:
			if "context-switch" not in l and ":" in l and "/*" not in l:
				d = l.split(":")
				self.data[d[0].strip()] = int(d[1].strip())
		# Collecting thread data
		self.generatedData["manual"] = {}
		for threadName in self.data:
			tSize = []
			tSize.append(1)
			tSize.append(self.data[threadName])
			self.generatedData["manual"][threadName] = []
			self.generatedData["manual"][threadName].append(tuple(tSize))
		# Write to file
		fd = open(outputfile, "w")
		json.dump(self.generatedData, fd)
		fd.close()

	# generate one configFile
	## TODO : same transformation for all generators?
	def generatingConfig(self, outputfile, iteratorFile, inputfile, softLimit=0, hardLimit=0,
			verbose=False, randomness=True, start=0):
		selectedInstances = self.computeConfig(softLimit, hardLimit,verbose, randomness, start)
		# generate config file
		#print "%s" % self.generatedData
		if self.configonly:
			fd = open(outputfile, "w")
			json.dump(self.generatedData, fd)
			fd.close()
			sys.exit(0)
		if self.clusterConfig>0:
			j=0
			configSets=[]
			config = {}
 
			idirname, ifilename = os.path.split(os.path.abspath(inputfile))
			dirname, filename = os.path.split(os.path.abspath(outputfile))
			outputdir = dirname+"/"+ifilename[:-2]+".cluster/"
			newoutputfile = outputdir + filename[:-5]
			if not os.path.exists(outputdir):
				 os.makedirs(outputdir)
			suffix = ".json" 
			for key in self.generatedData: 
				if j<self.clusterConfig:
					config[key]=self.generatedData[key]
					j +=1
				else:
					j = 1  
					configSets.append(config)
					config={}
					config[key]=self.generatedData[key]
			configSets.append(config) 
			for i in range(0,len(configSets)): 
				fd = open(newoutputfile+str(i)+suffix, "w")
				json.dump(configSets[i], fd)
				fd.close()           
			sys.exit(0)

		
		return self.generatorConfigIterator(iteratorFile,selectedInstances,self.generatedData)
		#gen = self.generatorConfig(outputfile, softLimit, hardLimit,verbose,
		#                               randomness, start,bagsize=0)
		#try:
		#    configFile,chosenInstances,num,result = gen.next()
		#    # with bagsize=0, all configurations should be written in outputFile
		#    assert (configFile == outputfile)
		#    return chosenInstances,result
		#except StopIteration:
		#    return False # no typing error??


	# returns a config generator, ex:
	#
	# gen = generatorConfig(outputfile,...,bagsize=100)
	# configFile,_,_ = gen.next() # configFile = outputfile_0.json contains the first 100 configurations
	# configFile,_,_ = gen.next() # outputfile_1.json contains the 100 next configurations
	# ...
	# get StopIteration exception when there is no more configurations
	def computeConfig(self, softLimit=0, hardLimit=0,
			verbose=False, randomness=True, start=0):
		""" Automatic generating configuration file for generating instances
		"""
		# read context switch lines
		lines = self.data.splitlines()
		# self.data is the information of the last context switch of each thread
		self.data = {}
		for l in lines:
			if "context-switch" not in l:
				d = l.split(":")
				self.data[d[0].strip()] = int(d[1].strip())

		# For each thread create a list of partitioning point
		# For example:
		#   main: 0, 3, 5
		#   t1: 0, 5, 10, ..
		threadsPartitioningPoints = {}
		for thread in self.data:
			max_contextswitch = self.data[thread]
			threadsPartitioningPoints[thread] = []
			if self.percent: 
					realWindowWidth = findlength(max_contextswitch, self.realWindowPercent)
					windowWidth = findlength(max_contextswitch, self.windowPercent)
					if windowWidth < 1:
						windowWidth=realWindowWidth
						self.data = False
			else:
				windowWidth = self.windowWidth
				realWindowWidth = self.realWindowWidth
			# print thread, windowWidth
			if thread not in self.skiplist and windowWidth < max_contextswitch - 2 and realWindowWidth*self.pickWindow < max_contextswitch:
				i = 1
				while i < max_contextswitch:
					lrange = i
					rrange = i + windowWidth - 1
					if rrange > max_contextswitch:
						rrange = max_contextswitch
					threadsPartitioningPoints[thread].append((lrange, rrange))
					i = rrange + 1
			else:  # No need to divide window if this window is nearly the size of thread
				l = []
				l.append((1, max_contextswitch))
				threadsPartitioningPoints[thread].append(tuple(l))


		# for each thread, list every possible choice of windows
		threadNames = []   # name of each thread
		threadInstances = []   # list of threads

		for thread in threadsPartitioningPoints:
			threadNames.append(thread)
			if self.pickWindow >= len(threadsPartitioningPoints[thread]):
				threadsPartitioningPoints[thread] = []    # pick whole thread when #windows > #points
				l = []
				l.append((1, self.data[thread]))
				threadsPartitioningPoints[thread].append(tuple(l))
				threadInstances.append(threadsPartitioningPoints[thread])
			else:
				if self.double:
					# Generate random combinations
					if randomness:
						threadInstances.append([t for t in generateCombinationDoubleWindowsRandomize(threadsPartitioningPoints[thread], self.pickWindow, softLimit, consecutive=self.consecutive)])
					else:
						threadInstances.append([t for t in generateCombinationDoubleWindows(threadsPartitioningPoints[thread], self.pickWindow, softLimit, consecutive=self.consecutive)])

				else:
					totalCombinations = binomial_coefficients(len(threadsPartitioningPoints[thread]), self.pickWindow, self.consecutive)
					if totalCombinations > 10000000 and self.memoryguard:
						print("WARNING: The number of combinations for %s is gigantic (%s), limiting to 1000000" % (thread, totalCombinations))
						# Put a softlimit here to prevent memory exploding
						threadInstances.append([t for t in generateCombinations(threadsPartitioningPoints[thread], self.pickWindow, totalCombinations, consecutive=self.consecutive, limit=1000000, randomness=randomness)])
					else:
						# threadInstances.append([t for t in itertools.combinations(threadsPartitioningPoints[thread], self.pickWindow)])
						threadInstances.append([t for t in generateCombinations(threadsPartitioningPoints[thread], self.pickWindow, totalCombinations, consecutive=self.consecutive)])

		# Generate Cartesian product of all thread instances
		# Now improving with iteration of one by one
		totalPossibleInstances, stringTotal = calculateProduct(threadInstances)
		print("Total possible instances is", totalPossibleInstances, ":", stringTotal)

		if verbose and bagsize > 1:
			configsize = 2 # outer "{}"
			# each tiling configuration (in the json file) is of the form :
			# "s01": {"main": [[1, 1], [2, 2]], "thr1": [[1, 1], [4, 4]], "thr2": [[2, 2], [3, 3]]}
			# the mean length of "s..."
			tilingsize = 6 + math.ceil(math.log10(totalPossibleInstances))  # ""s??": {}"
			for t in self.data:
				max_cs = self.data[t]
				tilingsize += len(t) + 6 # ""name": ..., "
				tilingsize += 2 + self.pickWindow * 7 # "[ ... ]"
			configsize += bagsize * tilingsize
			print("Estimated size of a (complete) config file bag: %d bytes" % configsize)

		# There is a hard limit
		if hardLimit != 0 and totalPossibleInstances > hardLimit:
			raise StopIteration

		hasSoftlimit = False
		softlimitedInstances = totalPossibleInstances
		# There is a soft limit
		if softLimit != 0:
			if totalPossibleInstances > softLimit:
				hasSoftlimit = True
				softlimitedInstances = softLimit

		sys.stdout.flush()

		chosenInstances = softlimitedInstances
		if self.limit != 0:
			chosenInstances = self.limit

		partial = False   # Determine if instance generating is random or not
		sampleList = {}
		if softlimitedInstances > chosenInstances:
			partial = True
			if randomness:
				try:
					sampleList = random.sample(range(softlimitedInstances), chosenInstances)
				except OverflowError as err:
					softlimitedInstances = min(softlimitedInstances,int(1000000000000000000))
					chosenInstances = min(min(chosenInstances,softlimitedInstances),int(1000000))
					sampleList = random.sample(range(softlimitedInstances), chosenInstances)
				sampleList = list2dict(sampleList)
			else:
				sampleList = list2dict([i for i in range(start, min(start + chosenInstances, softlimitedInstances))])
		else:
			chosenInstances = softlimitedInstances

		index = 0
		#numInstance = 0
		#:wq
		#fileno = 0 # current outputfile suffix
		if not partial: # Generating all possible instances
			for item in itertools.product(*threadInstances):
				key = "s%s" % index
				self.generatedData[key] = {}   # Each sample
				for i in range(0, len(item)):
					self.generatedData[key][threadNames[i]] = item[i]
				index += 1 
		else:
			for index in sampleList:
				key = "s%s" % index
				self.generatedData[key] = {}   # Each sample
				indices = getIndicesOfThreadInstances(threadInstances, index)
				for i in range(0, len(indices)):
					self.generatedData[key][threadNames[i]] = threadInstances[i][int(indices[i])]

			## special case: do note write a file for one tiling but return the string
			#if bagsize == 1:
			#    yield (json.dumps(self.generatedData).replace(""", "\\""),chosenInstances,0,True)
			#    self.generatedData = {}

			# pause the generation and write the current contents into the file
			#elif bagsize > 1 and (numInstance % bagsize == 0 or numInstance >= chosenInstances):
			#    filename = re.sub(".json$", str(fileno) + ".json", outputfile)
			#    fd = open(filename, "w")
			#    json.dump(self.generatedData, fd)
			#    fd.close()
			#    self.generatedData = {}
			#    yield (filename,chosenInstances,fileno,True)
			#    fileno += 1

			#if numInstance >= chosenInstances:
			#    break
			#index += 1
		if verbose:
			if partial:
				if hasSoftlimit:
					print(chosenInstances, " instances (random from first %s of %s)" % (softlimitedInstances, totalPossibleInstances))
				else:
					print(chosenInstances, " instances (random from %s=%s)" % (stringTotal, totalPossibleInstances))
			else:
				print(chosenInstances, "instances")

		return chosenInstances


	def generatorConfigIterator(self,outputfile,selectedInstances, data):
		# write all generatedData in one file
		for key in data:
			newData= {}
			newData[key]=data[key]
			with open(outputfile, "w") as fd:
				json.dump(newData, fd)
			yield outputfile,selectedInstances,True


def findlength(threadsize, percent):
	return max(int(threadsize * percent / 100), min(1, threadsize))


class ConfigGeneratorPercentage():

	def __init__(self, data, windowPercent, pickWindow, instanceslimit,
					consecutive=True, memoryguard=True, double=False, skiplist={}):
		"""
			data: threads specs
			windowPercent: percent of thread size
			pickWindow: number of windows
			instanceslimit: the number of instances
			consecutive: whether the windows are consecutive
			memoryguard: automatic prevent memory consumption when the number is huge
			double: choose double windows
		"""
		self.data = data
		self.generatedData = {}   # This object is for json file
		self.windowPercent = windowPercent
		self.realWindowPercent = windowPercent
		self.pickWindow = pickWindow
		self.limit = instanceslimit
		self.consecutive = consecutive
		self.memoryguard = memoryguard
		self.double = double
		if self.double:    # Double mean window is shifted up or down, that is why
						   # the width need to be halved
			self.windowPercent = int(self.windowPercent/2)
		self.skiplist = skiplist

	def generatingManualConfigString(self):
		return json.dumps(self.generatedData, indent=4, separators=(",", ": "))

	def generatingManualConfig(self, outputfile):
		# Read context switch line
		lines = self.data.splitlines()
		self.data = {}
		for l in lines:
			if "context-switch" not in l:
				d = l.split(":")
				self.data[d[0].strip()] = int(d[1].strip())
		# Collecting thread data
		self.generatedData["manual"] = {}
		for threadName in self.data:
			tSize = []
			tSize.append(1)
			tSize.append(self.data[threadName])
			self.generatedData["manual"][threadName] = []
			self.generatedData["manual"][threadName].append(tuple(tSize))
		# Write to file
		fd = open(outputfile, "w")
		json.dump(self.generatedData, fd)
		fd.close()

	def generatingConfigPercentage(self, outputfile, softLimit=0, hardLimit=0,
				verbose=False, randomness=True, start=0):
		""" Automatic generating configuration file for generating instances
		"""
		# read context switch lines
		lines = self.data.splitlines()
		# self.data is the information of the last context switch of each thread
		self.data = {}
		for l in lines:
			if "context-switch" not in l:
				d = l.split(":")
				self.data[d[0].strip()] = int(d[1].strip())
		# For each thread create a list of partitioning point
		# For example:
		#   main: 0, 3, 5
		#   t1: 0, 5, 10, ..
		threadsPartitioningPoints = {}
		for thread in self.data:

			max_contextswitch = self.data[thread]
			threadsPartitioningPoints[thread] = []
			windowWidth = findlength(max_contextswitch, self.windowPercent)
			realWindowWidth = findlength(max_contextswitch, self.realWindowPercent)

			# print thread, windowWidth
			if thread not in self.skiplist and windowWidth < max_contextswitch - 2 and realWindowWidth*self.pickWindow < max_contextswitch:
				i = 1
				while i < max_contextswitch:
					lrange = i
					rrange = i + windowWidth - 1
					if rrange > max_contextswitch:
						rrange = max_contextswitch
					threadsPartitioningPoints[thread].append((lrange, rrange))
					i = rrange + 1

			else:  # No need to divide window if this window is nearly the size of thread
				l = []
				l.append((1, max_contextswitch))
				threadsPartitioningPoints[thread].append(tuple(l))


		# for each thread, list every possible choice of windows
		threadNames = []   # name of each thread
		threadInstances = []   # list of threads

		for thread in threadsPartitioningPoints:
			threadNames.append(thread)
			if self.pickWindow >= len(threadsPartitioningPoints[thread]):
				threadsPartitioningPoints[thread] = []    # pick whole thread when #windows > #points
				l = []
				l.append((1, self.data[thread]))
				threadsPartitioningPoints[thread].append(tuple(l))
				threadInstances.append(threadsPartitioningPoints[thread])
			else:
				if self.double:
					# Generate random combinations
					if randomness:
						threadInstances.append([t for t in generateCombinationDoubleWindowsRandomize(threadsPartitioningPoints[thread], self.pickWindow, softLimit, consecutive=self.consecutive)])
					else:
						threadInstances.append([t for t in generateCombinationDoubleWindows(threadsPartitioningPoints[thread], self.pickWindow, softLimit, consecutive=self.consecutive)])
				else:
					totalCombinations = binomial_coefficients(len(threadsPartitioningPoints[thread]), self.pickWindow, self.consecutive)
					if totalCombinations > 10000000 and self.memoryguard:
						print("WARNING: The number of combinations for %s is gigantic (%s), limiting to 1000000" % (thread, totalCombinations))
						# Put a softlimit here to prevent memory exploding
						threadInstances.append([t for t in generateCombinations(threadsPartitioningPoints[thread], self.pickWindow, totalCombinations, consecutive=self.consecutive, limit=1000000, randomness=randomness)])
					else:
						# threadInstances.append([t for t in itertools.combinations(threadsPartitioningPoints[thread], self.pickWindow)])
						threadInstances.append([t for t in generateCombinations(threadsPartitioningPoints[thread], self.pickWindow, totalCombinations, consecutive=self.consecutive)])

		# Generate Cartesian product of all thread instances
		# Now improving with iteration of one by one
		totalPossibleInstances, stringTotal = calculateProduct(threadInstances)
		print("Total possible instances is", totalPossibleInstances, ":", stringTotal)

		# There is a hard limit
		if hardLimit != 0 and totalPossibleInstances > hardLimit:
			return False

		hasSoftlimit = False
		softlimitedInstances = totalPossibleInstances
		# There is a soft limit
		if softLimit != 0:
			if totalPossibleInstances > softLimit:
				hasSoftlimit = True
				softlimitedInstances = softLimit

		sys.stdout.flush()

		chosenInstances = softlimitedInstances
		if self.limit != 0:
			chosenInstances = self.limit

		partial = False   # Determine if instance generating is random or not
		sampleList = {}
		if softlimitedInstances > chosenInstances:
			partial = True
			if randomness:
				sampleList = random.sample(range(softlimitedInstances), chosenInstances)
				sampleList = list2dict(sampleList)
			else:
				sampleList = list2dict([i for i in range(start, min(start + chosenInstances, softlimitedInstances))])
		else:
			chosenInstances = softlimitedInstances

		index = 0
		numInstance = 0
		for item in itertools.product(*threadInstances):
			if not partial:     # Generating all possible instances
				key = "s%s" % index
				self.generatedData[key] = {}   # Each sample
				for i in range(0, len(item)):
					self.generatedData[key][threadNames[i]] = item[i]
				numInstance += 1
			else:
				if index in sampleList:
					key = "s%s" % index
					self.generatedData[key] = {}   # Each sample
					for i in range(0, len(item)):
						self.generatedData[key][threadNames[i]] = item[i]
					numInstance += 1
			if numInstance >= chosenInstances:
				break
			index += 1

		if verbose:
			if partial:
				if hasSoftlimit:
					print(chosenInstances, " instances (random from first %s of %s)" % (softlimitedInstances, totalPossibleInstances))
				else:
					print(chosenInstances, " instances (random from %s=%s)" % (stringTotal, totalPossibleInstances))
			else:
				print(chosenInstances, "instances")

		fd = open(outputfile, "w")
		json.dump(self.generatedData, fd)
		fd.close()
		return chosenInstances, True, self.generatedData

	def generatorConfigIterator(self,outputfile,selectedInstances, data):
		# write all generatedData in one file
		for key in data:
			newData= {}
			newData[key]=data[key]
			with open(outputfile, "w") as fd:
				json.dump(newData, fd)
			yield outputfile,selectedInstances,True


class ConfigGeneratorWMM():

	def __init__(self, data, windowWidth, pickWindow, WMMwindowWidth, WMMpickWindow, instanceslimit, consecutive=True, memoryguard=True, double=False, WMMdouble=False, skiplist={}):
		"""
			data: threads specs
			windowWidth: length of windows
			pickWindow: number of windows
			instanceslimit: the number of instances
			consecutive: whether the windows are consecutive
			memoryguard: automatic prevent memory consumption when the number is huge
			double: choose double windows
		"""
		self.data = data
		self.generatedData = {}   # This object is for json file
		self.windowWidth = windowWidth
		self.pickWindow = pickWindow
		self.WMMwindowWidth = WMMwindowWidth
		self.WMMpickWindow = WMMpickWindow
		self.limit = instanceslimit
		self.consecutive = consecutive
		self.memoryguard = memoryguard
		self.double = double
		if self.double:
			self.windowWidth = int(self.windowWidth/2)
		self.WMMdouble = WMMdouble
		if self.WMMdouble:
			self.WMMwindowWidth = int(self.WMMwindowWidth/2)
		self.skiplist = skiplist

	def generatingManualConfigStringWMM(self):
		return json.dumps(self.generatedData, indent=4, separators=(",", ": "))

	def generatingManualConfigWMM(self, outputfile):
		# Read context switch line
		lines = self.data.splitlines()
		self.data = {}
		for l in lines:
			if "context-switch" not in l:
				d = l.split(":")
				self.data[d[0].strip()] = int(d[1].strip())
		# Collecting thread data
		self.generatedData["manual"] = {}
		for threadName in self.data:
			tSize = []
			tSize.append(1)
			tSize.append(self.data[threadName])
			self.generatedData["manual"][threadName] = []
			self.generatedData["manual"][threadName].append(tuple(tSize))
		# Write to file
		fd = open(outputfile, "w")
		json.dump(self.generatedData, fd)
		fd.close()

	def generatingConfigWMM(self, outputfile, softLimit=0, hardLimit=0, verbose=False):
		""" Automatic generating configuration file for generating instances
		"""
		# read context switch lines
		lines = self.data.splitlines()
		# self.data is the information of the last context switch of each thread
		self.data = {}
		for l in lines:
			if "context-switch" not in l:
				d = l.split(":")
				self.data[d[0].strip()] = int(d[1].strip())
				self.data[d[0].strip() + "_WMM"] = int(d[1].strip())   # Duplicate thread for WMM barrier

		# For each thread create a list of partitioning point
		# For example:
		#   main: 0, 3, 5
		#   t1: 0, 5, 10, ..
		threadsPartitioningPoints = {}
		for thread in self.data:
			windowWidth = self.WMMwindowWidth if thread.endswith("_WMM") else self.windowWidth
			max_contextswitch = self.data[thread]
			threadsPartitioningPoints[thread] = []
			if thread not in self.skiplist and windowWidth < max_contextswitch - 2:
				i = 1
				while i < max_contextswitch:
					lrange = i
					rrange = i + windowWidth - 1
					if rrange > max_contextswitch:
						rrange = max_contextswitch
					threadsPartitioningPoints[thread].append((lrange, rrange))
					i = rrange + 1
			else:  # No need to divide window if this window is nearly the size of thread
				l = []
				l.append((1, max_contextswitch))
				threadsPartitioningPoints[thread].append(tuple(l))

		# print threadsPartitioningPoints
		# for each thread, list every possible choice of windows
		threadNames = []   # name of each thread
		threadInstances = []   # list of threads

		for thread in threadsPartitioningPoints:
			pickWindow = self.WMMpickWindow if thread.endswith("_WMM") else self.pickWindow
			double = self.WMMdouble if thread.endswith("_WMM") else self.double
			threadNames.append(thread)
			if pickWindow >= len(threadsPartitioningPoints[thread]):
				threadsPartitioningPoints[thread] = []    # pick whole thread when #windows > #points
				l = []
				l.append((1, self.data[thread]))
				threadsPartitioningPoints[thread].append(tuple(l))
				threadInstances.append(threadsPartitioningPoints[thread])
			else:
				if double:
					# Generate random combinations
					# print "consecutive:", self.consecutive
					threadInstances.append([t for t in generateCombinationDoubleWindowsRandomize(threadsPartitioningPoints[thread], pickWindow, softLimit, consecutive=self.consecutive)])
				else:
					totalCombinations = binomial_coefficients(len(threadsPartitioningPoints[thread]), pickWindow, self.consecutive)
					if totalCombinations > 10000000 and self.memoryguard:
						print("WARNING: The number of combinations for %s is gigantic (%s), limiting to 1000000" % (thread, totalCombinations))
						# Put a softlimit here to prevent memory exploding
						threadInstances.append([t for t in generateCombinations(threadsPartitioningPoints[thread], pickWindow, totalCombinations, consecutive=self.consecutive, limit=1000000, randomness=True)])
					else:
						# threadInstances.append([t for t in itertools.combinations(threadsPartitioningPoints[thread], pickWindow)])
						threadInstances.append([t for t in generateCombinations(threadsPartitioningPoints[thread], pickWindow, totalCombinations, consecutive=self.consecutive)])

		# Generate Cartesian product of all thread instances
		# Now improving with iteration of one by one
		totalPossibleInstances, stringTotal = calculateProduct(threadInstances)
		print("Total possible instances is", totalPossibleInstances, ":", stringTotal)

		# There is a hard limit
		if hardLimit != 0 and totalPossibleInstances > hardLimit:
			return False

		hasSoftlimit = False
		softlimitedInstances = totalPossibleInstances
		# There is a soft limit
		if softLimit != 0:
			if totalPossibleInstances > softLimit:
				hasSoftlimit = True
				softlimitedInstances = softLimit

		sys.stdout.flush()

		chosenInstances = softlimitedInstances
		if self.limit != 0:
			chosenInstances = self.limit

		randomness = False   # Determine if instance generating is random or not
		sampleList = {}
		if softlimitedInstances > chosenInstances:
			randomness = True
			sampleList = random.sample(range(softlimitedInstances), chosenInstances)
			sampleList = list2dict(sampleList)
		else:
			chosenInstances = softlimitedInstances

		index = 0
		numInstance = 0
		for item in itertools.product(*threadInstances):
			if not randomness or index in sampleList:     # Generating all possible instances
				print("PIPPO")
				key = "s%s" % index
				self.generatedData[key] = {}   # Each sample
				for i in range(0, len(item)):
					self.generatedData[key][threadNames[i]] = item[i]
				numInstance += 1
			#else:
				#if index in sampleList:
				#    key = "s%s" % index
				#    self.generatedData[key] = {}   # Each sample
				#    for i in range(0, len(item)):
				#        self.generatedData[key][threadNames[i]] = item[i]
				#    numInstance += 1
			if numInstance >= chosenInstances:
				break
			index += 1

		if verbose:
			if randomness:
				if hasSoftlimit:
					print(chosenInstances, " instances (random from first %s of %s)" % (softlimitedInstances, totalPossibleInstances))
				else:
					print(chosenInstances, " instances (random from %s=%s)" % (stringTotal, totalPossibleInstances))
			else:
				print(chosenInstances, "instances")

		fd = open(outputfile, "w")
		json.dump(self.generatedData, fd)
		fd.close()
		return chosenInstances, True


def getWindowSize(string, strategy="MT"):
	lines = string.splitlines()
	data = {}
	for l in lines:
		if "context-switch" not in l:
			d = l.split(":")
			data[d[0].strip()] = int(d[1].strip())

	if strategy == "AT":
		sum = 0
		i = 0
		for t in data:
			sum += data[t]
			i += 1
		ret = (sum/i)/2 + 1
		return int(ret)
	else:
		# Use default strategy
		ret = 0
		for t in data:
			if ret < data[t]:
				ret = data[t]
		return int(ret/2 + 1)


def threadLinesToDict(info):
	lines = info.splitlines()
	data = {}
	for l in lines:
		if "context-switch" not in l:
			d = l.split(":")
			region = []
			region.append
			data[d[0].strip()] = int(d[1].strip())
	generatedData = {}
	generatedData["original"] = {}
	for threadName in data:
		tSize = []
		tSize.append(1)
		tSize.append(data[threadName])
		generatedData["original"][threadName] = []
		generatedData["original"][threadName].append(tSize)
	return generatedData


def generatingHelper(inputdict, outputdict, countFrom, pickWindow=1, Warning=False, instancesLimit=0):
	threadNames = []
	threadInstances = []
	for thread in inputdict:
		threadNames.append(thread)
		if pickWindow >= len(inputdict[thread]):
			l = []
			l.append(tuple(inputdict[thread]))
			threadInstances.append(l)
		else:
			threadInstances.append([t for t in itertools.combinations(inputdict[thread], pickWindow)])

	totalPossibleInstances, stringTotal = calculateProduct(threadInstances)

	# Generate Cartesian product of all thread instances
	for item in itertools.product(*threadInstances):
		key = "s%s" % countFrom
		outputdict[key] = {}   # Each sample
		for i in range(0, len(item)):
			outputdict[key][threadNames[i]] = item[i]
		countFrom += 1
		if instancesLimit > 0 and countFrom >= instancesLimit:   # limit the number of instances
			break
	return countFrom


def generatingConfigHalfSizeInstance(info, outputfile, pickWindow=2, instancesLimit=0):
	"""
		info: store instances which are picked to be divided into half size
	"""
	generatedData = {}
	minWindowSofar = 1000000   # Imagine a thread with 1000000 cs !
	cached = ""
	countFrom = 0
	for s in info:
		# Each sample to be divided
		divided = {}
		for thread in info[s]:
			if thread != "main":
				divided[thread] = []
				for reg in info[s][thread]:
					lrange = reg[0]
					rrange = reg[1]
					if (rrange - lrange) < 2:
						minWindowSofar = 1
						divided[thread].append(reg)
					else:
						length = rrange - lrange + 1
						hlen = int(length/2)
						if minWindowSofar > hlen:
							minWindowSofar = hlen
						mid = lrange + hlen
						reg1 = []
						reg1.append(lrange)
						reg1.append(mid-1)
						reg2 = []
						reg2.append(mid)
						reg2.append(rrange)
						divided[thread].append(reg1)
						divided[thread].append(reg2)
			else:    # main thread
				cached = info[s][thread]
		# Dividing main thread
		divided["main"] = []
		for reg in cached:
			lenreg = reg[1] - reg[0] + 1
			if minWindowSofar < lenreg - 2:
				lrange = reg[0]
				rrange = reg[1]
				length = rrange - lrange + 1
				hlen = int(length/2)
				mid = lrange + hlen
				reg1 = []
				reg1.append(lrange)
				reg1.append(mid-1)
				reg2 = []
				reg2.append(mid)
				reg2.append(rrange)
				divided["main"].append(reg1)
				divided["main"].append(reg2)
			else:
				divided["main"].append(reg)

		countFrom = generatingHelper(divided, generatedData, countFrom, pickWindow=pickWindow, instancesLimit=instancesLimit)
		if instancesLimit > 0 and countFrom >= instancesLimit:
			minWindowSofar = 1000000
			break
		# reset minwindowsofar
		minWindowSofar = 1000000

	# Write to file
	fd = open(outputfile, "w")
	json.dump(generatedData, fd)
	fd.close()
	return countFrom, True


def generatingConfigQuarterSizeInstance(info, outputfile, pickWindow=2):
	"""
	"""
	generatedData = {}
	minWindowSofar = 1000000   # Imagine a thread with 1000000 cs!
	cached = ""   # to store main thread
	countFrom = 0
	for s in info:  # there is only one at the beginning but who cares
		# Each sample to be divided
		divided = {}
		for thread in info[s]:
			if thread != "main":
				# In each thread in main
				divided[thread] = []
				if len(info[s][thread]) != 1:
					print("Something wrong with the information of context switch in thread %s" % thread)
					sys.exit(2)
				reg = info[s][thread][0]
				lrange = reg[0]  # first cs
				rrange = reg[1]  # last cs
				if (rrange - lrange) < 4:  # there is no point to divide here
					minWindowSofar = rrange - lrange
					divided[thread].append(reg)
				else:
					length = rrange - lrange + 1
					quadlen = int(length/4)
					if minWindowSofar > quadlen:
						minWindowSofar = quadlen
					milestone1 = lrange + quadlen
					milestone2 = lrange + 2*quadlen
					milestone3 = lrange + 3*quadlen
					reg0 = []
					reg0.append(lrange)
					reg0.append(milestone1-1)
					reg1 = []
					reg1.append(milestone1)
					reg1.append(milestone2-1)
					reg2 = []
					reg2.append(milestone2)
					reg2.append(milestone3-1)
					reg3 = []
					reg3.append(milestone3)
					reg3.append(rrange)
					divided[thread].append(reg0)
					divided[thread].append(reg1)
					divided[thread].append(reg2)
					divided[thread].append(reg3)
			else:    # main thread
				cached = info[s][thread]
		# Dividing main thread
		divided["main"] = []
		if len(cached) != 1:
			print("Something wrong with the information of context switch in main thread")
			sys.exit(2)
		reg = cached[0]
		lenreg = reg[1] - reg[0] + 1
		if lenreg > 4 and minWindowSofar < lenreg - 2:  # just a proximation
			lrange = reg[0]
			rrange = reg[1]
			length = rrange - lrange + 1
			quadlen = int(length/4)
			milestone1 = lrange + quadlen
			milestone2 = lrange + 2*quadlen
			milestone3 = lrange + 3*quadlen
			reg0 = []
			reg0.append(lrange)
			reg0.append(milestone1-1)
			reg1 = []
			reg1.append(milestone1)
			reg1.append(milestone2-1)
			reg2 = []
			reg2.append(milestone2)
			reg2.append(milestone3-1)
			reg3 = []
			reg3.append(milestone3)
			reg3.append(rrange)
			divided["main"].append(reg0)
			divided["main"].append(reg1)
			divided["main"].append(reg2)
			divided["main"].append(reg3)
		else:
			divided["main"].append(reg)

		countFrom = generatingHelper(divided, generatedData, countFrom, pickWindow=pickWindow, Warning=True)
		# reset minwindowsofar
		minWindowSofar = 1000000
	# Write to file
	fd = open(outputfile, "w")
	json.dump(generatedData, fd)
	fd.close()
	return countFrom, True


def jobsperworker_partition(total, workers):
	if total < workers:
		return 1
	else:
		if total % workers == 0:
			return total/workers
		else:
			return int(total/workers) + 1


def distributingGenerators(inputfile, numWorker=1):
	jobFileList = []
	configs = parseConfig(inputfile)

	jobsPerWorker = jobsperworker_partition(len(configs), numWorker)

	i = 1
	tempConfig = {}
	tempfile = ""
	for item in itertools.izip_longest(*[iter(configs.items())]*jobsPerWorker):
		tempConfig = dict(sample for sample in item if sample is not None)
		tempfile = inputfile[:-5] + ".part%s.json" % i
		with open(tempfile, "w") as configFile:
			json.dump(tempConfig, configFile)
		jobFileList.append(tempfile)
		i += 1

	return tuple(jobFileList)


def combineList(fileList, outFilename, keepFiles=False):
	outfile = open(outFilename, "w")
	for f in fileList:
		try:
			with open(f, "r") as data:
				outfile.write(data.read())
		except IOError as e:
			print(str(e))
	outfile.close()
	if not keepFiles:
		for f in fileList:
			try:
				os.remove(f)
			except OSError:
				pass   # supress


def getDateTime():
	import datetime
	now = datetime.datetime.now()
	return now.strftime("%Y-%b-%d-%H-%M-%S")


def makeBackup(filename):
	if os.path.exists(filename):
		newfilename = filename + "." + getDateTime() + ".bak"
		import shutil
		shutil.copy(filename, newfilename)


def chunk(input, size):
	return map(None, *([iter(input)] * size))


def dumpDict2File(dict, outfilename):
	makeBackup(outfilename)
	with open(outfilename, "w") as out:
		json.dump(dict, out)


def json_deserialize(obj):
	processed_obj = {}
	for key in obj:
		newkey = key.split(":")
		processed_obj[tuple(newkey)] = obj[key]
	return processed_obj


def createFolder(directory):
	try:
		if not os.path.exists(directory):
			os.makedirs(directory)
	except OSError:
		print("Error: Creating directory. " +  directory)

def getIndicesOfThreadInstances(list, n):
		indices=[]
		l=len(list)
		for i in range(0,l):
		   d = len(list[i])  
		   indices.append(n%d)
		   n = n/d
		return indices
