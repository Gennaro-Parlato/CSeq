import os
import os.path
import gmpy2
import itertools


def partition(total, part):
    if total % part == 0:
        return total/part
    else:
        return int(total/part) + 1


def calculateProduct(pack):
    total = 1
    string = []
    for item in pack:
        temp = len(item)
        total *= temp
        string.append(str(temp))

    string = "x".join(string)
    return total, string

def calculateProduct2(pack):
    total = 1
    string = []
    for item in pack:
        total *= item
        string.append(str(item))

    string = "x".join(string)
    return total, string

def totalinstancescatter(data, windowWidth, pickWindow):
    threadsPartitioningPoints = {}
    for thread in data:
        max_contextswitch = data[thread]
        threadsPartitioningPoints[thread] = []
        if windowWidth < max_contextswitch - 2:
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
    threadInstances = []   # list of threads

    for thread in threadsPartitioningPoints:
        if pickWindow >= len(threadsPartitioningPoints[thread]):
            threadsPartitioningPoints[thread] = []    # Choose whole thread when #windows > #points
            l = []
            l.append((1, data[thread]))
            threadsPartitioningPoints[thread].append(tuple(l))
            threadInstances.append(1)
        else:
            # BUG: this will consume all the memory when number of picked window very large
            totalCombinations = gmpy2.comb(len(threadsPartitioningPoints[thread]) - pickWindow + 1, pickWindow)
            threadInstances.append(totalCombinations)

    # Generate Cartesian product of all thread instances
    # Now improving with iteration of one by one
    totalPossibleInstances, stringTotal = calculateProduct2(threadInstances)
    return totalPossibleInstances


def totalinstance(data, windowWidth, pickWindow):
    threadsPartitioningPoints = {}
    for thread in data:
        max_contextswitch = data[thread]
        threadsPartitioningPoints[thread] = []
        if windowWidth < max_contextswitch - 2:
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
    threadInstances = []   # list of threads

    for thread in threadsPartitioningPoints:
        if pickWindow >= len(threadsPartitioningPoints[thread]):
            threadsPartitioningPoints[thread] = []    # Choose whole thread when #windows > #points
            l = []
            l.append((1, data[thread]))
            threadsPartitioningPoints[thread].append(tuple(l))
            threadInstances.append(threadsPartitioningPoints[thread])
        else:
            # BUG: this will consume all the memory when number of picked window very large
            totalCombinations = gmpy2.comb(len(threadsPartitioningPoints[thread]), pickWindow)
            threadInstances.append([t for t in itertools.combinations(threadsPartitioningPoints[thread], pickWindow)])

    # Generate Cartesian product of all thread instances
    # Now improving with iteration of one by one
    totalPossibleInstances, stringTotal = calculateProduct(threadInstances)
    return totalPossibleInstances


def savefile(filename, content):
    if not os.path.exists(os.path.dirname(filename)):
        try:
            os.makedirs(os.path.dirname(filename))
        except OSError as exception:
            print(str(exception))

    with open(filename, "w") as out:
        out.write(content)


def appendfile(filename, content):
    with open(filename, "a+") as out:
        out.write(content)