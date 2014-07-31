import os
import subprocess
import sys
import shlex, subprocess
from subprocess import call
from sets import Set
import threading
import time
import signal
from threading import Timer


SkippableSet = Set()
SkippableDict = Set()
ParticipateSet = Set()
SkippableTable = {}
totalSkippable = 0

def GetSuffixesOfLength(S, suffixLen):
	suffixSet = Set()
	for i in S:
		ctxt = i.split()
		if len(ctxt) < suffixLen: continue
		suffix = ' '.join(ctxt[0:suffixLen])
		suffixSet.add(suffix)
	return suffixSet

def GetFullContextForGivenSuffixes(S, SkippableSuffix):
	fullCtxtSet = Set()
	for i in S:
		for j in SkippableSuffix:
			if i.startswith(j):
				fullCtxtSet.add(i)
				break
	return fullCtxtSet

def GetFullContextHashForGivenSuffixes(S, SkippableSuffix):
	fullCtxtHashList = []
	for i in S:
		for j in SkippableSuffix:
			if i.startswith(j):
				fullCtxtHashList.append(SkippableTable[i][1])
				break
	return fullCtxtHashList


def OrderSuffixByFrequency(S, presentationSet, suffixFile, doPrint):
    totalSkippable = 0
    suffixTable  = {}
    for i in presentationSet:
        for j in S:
            if j.startswith(i):
                totalSkippable = totalSkippable + SkippableTable[j][0]
                if suffixTable.has_key(i) : 
                    suffixTable[i] = suffixTable[i] + SkippableTable[j][0]
                else: 
                    suffixTable[i] = SkippableTable[j][0]


    if doPrint:
        fp = open(suffixFile,'w')
        fp.write('#Total = ' + str(totalSkippable))
        for w in sorted(suffixTable, key= suffixTable.get, reverse=True):
            fp.write('\n###################')
            fp.write('\n#' + w + ':' + str(suffixTable[w]) + ':' + str(suffixTable[w] * 100.0 / totalSkippable))
            c1 = ['addr2line', '-C', '-f', '-e', '/global/homes/m/mc29/nwchem-6.3_opt/bin/LINUX64/nwchem_bd'] + w.split()
            p = subprocess.Popen(c1 , stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            out, err = p.communicate()
            fp.write('\n#' + out.replace('\n','\n#'))
        fp.close()
    return sorted(suffixTable, key= suffixTable.get, reverse=True)


def FindSuffixes(suffixFile, doPrint):
# ALGORITHM
#Let S be the set of all contexts that the tool believes to have a redundant barrier.
#Let P be the set of all contexts that the tool believes to have a necessary barrier.
#Assert (S intersect P == empty)
#i = 1
#PresentationSet = {}
#While ( S  not empty and P != empty) {
# SkipCandidates = Set of all context suffixes of length i in S.
# ParticipateCandidates = Set of all context suffixes of length i in P.
# SkippableSuffix = SkipCandidates - ParticipateCandidates.
# PresentationSet += SkippableSuffix 
# S = S - All contexts in S whose suffix matches some context in SkippableSuffix
# i = i + 1
#}

    assert SkippableSet & ParticipateSet != set(), " SkippableSet & ParticipateSet != set() "

    S = SkippableSet.copy()
    P = ParticipateSet.copy()

    SkippableSuffix = Set()
    PresentationSet = Set()
    i = 1
    while len(S) > 0:
        SkipCandidates = GetSuffixesOfLength(S, i)	
        ParticipateCandidates = GetSuffixesOfLength(P, i)
        SkippableSuffix = SkipCandidates - ParticipateCandidates
        PresentationSet |= SkippableSuffix
        S -= GetFullContextForGivenSuffixes(S, SkippableSuffix) 
        print 'S=', len(S)
        i = i + 1

    return OrderSuffixByFrequency(SkippableSet, PresentationSet, suffixFile, doPrint)
	#print PresentationSet, len(PresentationSet)

def ReadInputFiles(skippableFile , participateFile):
# first read skippables which has the following format "<num> : <percent> : <hash1 > : <first barrier ctxt> : <hash 2> :<second redundant barrier ctxt>"
	l = open(skippableFile).readlines()
	for i in l:
	#skip comments
		if i.startswith('#'):  continue
		pieces  = i.split(':')
		s1 = ' '.join([x.strip() for x in pieces[5].split()])
		SkippableSet.add(s1)
		SkippableTable[s1] = (int(pieces[0].strip()), long(pieces[4].strip()))

# read participated barriers which has the following format "<num> : <percent> : <hash> : <barrier ctxt> "
	l = open(participateFile).readlines()
	for i in l:
		if i.startswith('#'):  continue
		pieces  = i.split(':')
		s1 = ' '.join([x.strip() for x in pieces[3].split()])
		ParticipateSet.add(s1)


def WriteFullCtxtHashForGivenSuffix(SkippableSet, SkippableSuffix):
    hashes = GetFullContextHashForGivenSuffixes(SkippableSet, SkippableSuffix)
    f = open('ctxt_hashes.txt', 'w')
    for h in hashes:
        f.write(str(h) + "\n")
    f.close()
    return hashes

def ReadSuffixFile(suffixFile):
    l = open(suffixFile).readlines()
    SkippableSuffix = []
    print 'You chose ' , len(SkippableSuffix) , 'suffixes'
    print SkippableSuffix
    cnt = 0
    for i in l:
        cnt = cnt + 1
        if i.startswith('#'):  continue
        print i, cnt
        print SkippableSuffix
        pieces  = i.split(':')
        s1 = ' '.join([x.strip() for x in pieces[0].split()])
        SkippableSuffix.append(s1)

        print 'You chose ' , len(SkippableSuffix) , 'suffixes'
    print SkippableSuffix
    WriteFullCtxtHashForGivenSuffix(SkippableSet, SkippableSuffix)



class Monitor(threading.Thread):
    def __init__(self, proc, maxTime):
        threading.Thread.__init__(self)
        self.proc = proc
        self.maxTime = maxTime
    def run(self):
        cnt = 0
        while self.proc.poll() == None:
            time.sleep(10)
            cnt = cnt + 10
            if cnt > self.maxTime:
                print "before kill"
                #os.kill(self.proc.pid, signal.SIGTERM)
                self.proc.terminate()
                self.proc.kill()
                print "after kill"
                time.sleep(10)

                break

def kill_proc(proc):
    print "Killing..."
    proc.kill()


def IsSafeSuffix():
    # copy ctxt_hashes.txt to its destination
    os.putenv("NWCHEM_GUIDED_OPTIMIZATION_MODE",  "optimize")
    directory = '/global/homes/m/mc29/nwchem-6.3_opt/src/'
    #directory = '.'
    ret = os.system('cp ctxt_hashes.txt ' + directory)
    assert(ret == 0)
    # run the test 10 times
    maxRuns = 10
    timeOutVal = 90
    expectedString = 'Total Barriers = 77418, Enabled = 77418, Skippable'
    cmd = ['aprun', '-N', '4', '-n', '32', '../bin/LINUX64/nwchem_bd', 'nwchem_inputs/tce_ccsd2_t_cl2o.nw']
    #cmd = ['aprun', '-n', '8', '../bin/LINUX64/nwchem_bd', 'nwchem_inputs/tce_ccsd2_t_cl2o.nw']
    #cmd = ['ls']
    for i in range(maxRuns):
            try:
                with open('output.txt', 'w') as fp:
                    proc = subprocess.Popen(cmd, stdout=fp, stderr=subprocess.STDOUT, cwd=directory)
                    # launch a side thread to monitor
                    #thread1 = Monitor(proc, timeOutVal)
                    #thread1.start()
                    timer = Timer(90, kill_proc, [proc])
                    timer.start()
                    proc.wait()
                    #(output, err) = proc.communicate()
                    timer.cancel()
                    if proc.returncode != 0:
                        print "BAD ret code", proc.returncode
                        return False
                # parse output for the right number of barriers
                
                with open('output.txt') as fp:
                    output = fp.read()
                    strLoc = output.find(expectedString)
                    if strLoc == -1:
                        print 'str not found'
                        return False
                    print output[strLoc:strLoc+100]
                
            except subprocess.CalledProcessError:
                (output, err) = proc.communicate()
                print 'subprocess.CalledProcessError'
                return False
                    
    return True



def AutomaticTesting():
    suffixes = FindSuffixes('', False)
    
    with open('useful_suffixes.txt', 'w') as fp:
        #suffixes = ["2325926c 22714a1b 22711631 20610ff0"]
        for s in suffixes:
            hashes = WriteFullCtxtHashForGivenSuffix(SkippableSet, [s])
            c1 = ['addr2line', '-C', '-f', '-e', '/global/homes/m/mc29/nwchem-6.3_opt/bin/LINUX64/nwchem_bd'] + s.split()
            p = subprocess.Popen(c1 , stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            out, err = p.communicate()
            print  s, '\n#', out.replace('\n','\n#')
            if IsSafeSuffix():
                # enlighten the user about this suffix
                print 'SAFE SUFFIX: ', s, "total ctxts = ", len(hashes)
                fp.write(s + '\n')
            else:
                # enlighten the user about this suffix
                print 'UNSAFE SUFFIX: ', s, "total ctxts = ", len(hashes)
                fp.write('#UNSAFE' + s + '\n')




ReadInputFiles('skippables.txt', 'participated.txt')


if sys.argv[1] == 'shirkToSuffix':
    FindSuffixes('suffixFile.txt', True)
elif sys.argv[1] == 'convertSuffixToFullCtxt' : 
	FindSuffixes('', False)
	ReadSuffixFile('suffixFile.txt')
elif sys.argv[1] == 'fullyAutomatic' :
    AutomaticTesting()








