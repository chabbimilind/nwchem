import os
import subprocess
import sys
import shlex, subprocess
from subprocess import call
#from sets import Set
import threading
import time
import signal
from threading import Timer


SkippableSet = set()
SkippableDict = set()
ParticipateSet = set()
SkippableTable = {}
totalSkippable = 0


NWCHEM_ROOT = ''
skipInitial = 0
skipAfter = sys.maxsize
maxRuns = 2
timeOutVal = 70
#expectedString = 'Total Barriers = 84269, Enabled = 84269, Skippable'
expectedString = 'Total Barriers = 77401, Enabled = 77401, Skippable ='
#cmd = ['aprun', '-N', '8', '-n', '64', './nwchem_bd', 'ip/tce_ccsd2_t_cl2o_new.nw']
cmd = ['aprun', '-t', str(timeOutVal), '-S', '4', '-n', '8', './nwchem_bd_L', 'ip/tce_ccsd2_t_cl2o.nw']
addrLineCmd = ['addr2line', '-C', '-f', '-e', './nwchem_bd_L'] 
whiteList = []
blackList = []

def ReadWhileAndBlackList():
    with open('white_list.txt') as fp:
        l = fp.readlines()
        for i in l:
        #skip comments
            if i.startswith('#'):  continue
            pieces  = i.split(':')
            s1 = ' '.join([x.strip() for x in pieces[0].split()])
            whiteList.append(s1)
    with open('black_list.txt') as fp:
        l = fp.readlines()
        for i in l:
            #skip comments
            if i.startswith('#'):  continue
            pieces  = i.split(':')
            s1 = ' '.join([x.strip() for x in pieces[0].split()])
            blackList.append(s1)
			

def GetSuffixesOfLength(S, suffixLen):
	suffixSet = set()
	for i in S:
		ctxt = i.split()
		if len(ctxt) < suffixLen: continue
		suffix = ' '.join(ctxt[0:suffixLen])
		suffixSet.add(suffix)
	return suffixSet

def GetFullContextForGivenSuffixes(S, SkippableSuffix):
	fullCtxtSet = set()
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
                if i in suffixTable:
                    suffixTable[i] = suffixTable[i] + SkippableTable[j][0]
                else: 
                    suffixTable[i] = SkippableTable[j][0]


    if doPrint:
        fp = open(suffixFile,'w')
        fp.write('#Total = ' + str(totalSkippable))
        for w in sorted(suffixTable, key= suffixTable.get, reverse=True):
            fp.write('\n###################')
            fp.write('\n#' + w + ':' + str(suffixTable[w]) + ':' + str(suffixTable[w] * 100.0 / totalSkippable))
            #c1 = ['addr2line', '-C', '-f', '-e', '/global/scratch2/sd/mc29/nwchem/guided_opt/nwchem_bd'] + w.split()
            c1 = addrLineCmd  + w.split()
            p = subprocess.Popen(c1 , stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            out, err = p.communicate()
            fp.write('\n#' + out.decode("utf-8").replace('\n','\n#'))
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

    assert SkippableSet & ParticipateSet == set(), " SkippableSet & ParticipateSet != set() "

    S = SkippableSet.copy()
    P = ParticipateSet.copy()

    SkippableSuffix = set()
    PresentationSet = set()
    i = 1
    while len(S) > 0:
        SkipCandidates = GetSuffixesOfLength(S, i)	
        ParticipateCandidates = GetSuffixesOfLength(P, i)
        SkippableSuffix = SkipCandidates - ParticipateCandidates
        PresentationSet |= SkippableSuffix
        S -= GetFullContextForGivenSuffixes(S, SkippableSuffix) 
        print ('S=', len(S))
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
		SkippableTable[s1] = (int(pieces[0].strip()), int(pieces[4].strip()))

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
    print ('You chose ' , len(SkippableSuffix) , 'suffixes')
    print (SkippableSuffix)
    cnt = 0
    for i in l:
        cnt = cnt + 1
        if i.startswith('#'):  continue
        print (i, cnt)
        print (SkippableSuffix)
        pieces  = i.split(':')
        s1 = ' '.join([x.strip() for x in pieces[0].split()])
        SkippableSuffix.append(s1)

        print ('You chose ' , len(SkippableSuffix) , 'suffixes')
    print (SkippableSuffix)
    WriteFullCtxtHashForGivenSuffix(SkippableSet, SkippableSuffix)




def IsSafeSuffix():
    # copy ctxt_hashes.txt to its destination
    os.putenv("NWCHEM_GUIDED_OPTIMIZATION_MODE",  "optimize")
    directory = '/global/scratch2/sd/mc29/nwchem/guided_opt/'
    #directory = '.'
    #ret = os.system('cp ctxt_hashes.txt ' + directory)
    #assert(ret == 0)
    # run the test 10 times
    #expectedString = 'Total Barriers = 77418, Enabled = 77418, Skippable'
    #cmd = ['aprun', '-n', '8', '../bin/LINUX64/nwchem_bd', 'nwchem_inputs/tce_ccsd2_t_cl2o.nw']
    #cmd = ['ls']
    for i in range(maxRuns):
            proc = None
            try:
                proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=directory)
                
                try:
                    #outs, errs = proc.communicate(timeout=timeOutVal)
                    outs, errs = proc.communicate()
                
                    if proc.returncode != 0:
                        print ("BAD ret code", proc.returncode)
                        return False
                
                    # parse output for the right number of barriers
                    outs = outs.decode("utf-8")
                    strLoc = outs.find(expectedString)
                    if strLoc == -1:
                        print ('str not found')
                        return False

                    print (outs[strLoc:strLoc+100])

                except subprocess.TimeoutExpired:
                    print ("Killing...")
                    proc.terminate()
                    proc.kill()
                    print ("Killed")
                    time.sleep(5)
                    return False



            except subprocess.CalledProcessError:
                (output, err) = proc.communicate()
                print ('subprocess.CalledProcessError')
                return False
                    
    return True



def AutomaticTesting():
    suffixes = FindSuffixes('', False)
    
    ReadWhileAndBlackList();
    #SuffixesToSkip = ['none'] #["2325a87e 22714a1b 22710b72 2263b0ec 225ff688"]
    with open('useful_suffixes.txt', 'w') as fp:
        #suffixes = ["2325926c 22714a1b 22711631 20610ff0"]
        initial = 0
        safeList = []
        for s in suffixes:
            #skip first skipInitial
            initial = initial + 1
            if initial < skipInitial: continue
            if initial > skipAfter: continue
            if s in blackList:
                print ('Skipping:', s)
                continue

            if s in whiteList:
                print ('not testing:', s)
                safeList.append(s)
                continue

            hashes = WriteFullCtxtHashForGivenSuffix(SkippableSet, safeList + [s])
            c1 = addrLineCmd + s.split()
            p = subprocess.Popen(c1 , stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            out, err = p.communicate()
            out = out.decode("utf-8")
            print  (s + '\n#' + out.replace('\n','\n#') )
            fp.write('#' + s + '\n#' + out.replace('\n','\n#') )
            if IsSafeSuffix():
                # enlighten the user about this suffix
                print ('SAFE SUFFIX: ', s, "total ctxts = ", len(hashes))
                fp.write ('\n#SAFE SUFFIX: '+ s+ "total ctxts = "+ str(len(hashes)))
                fp.write(' : ' + s + '\n')
                safeList.append(s)
            else:
                # enlighten the user about this suffix
                print ('UNSAFE SUFFIX: ', s, "total ctxts = ", len(hashes))
                fp.write ('#UNSAFE SUFFIX: '+ s+ "total ctxts = "+ str(len(hashes)))
                fp.write('\n#UNSAFE:' + s + '\n')
            #flush io
            fp.flush()
            os.fsync(fp)





ReadInputFiles('skippables.txt', 'participated.txt')


if sys.argv[1] == 'shirkToSuffix':
    FindSuffixes('suffixFile.txt', True)
elif sys.argv[1] == 'convertSuffixToFullCtxt' : 
	FindSuffixes('', False)
	ReadSuffixFile('suffixFile.txt')
elif sys.argv[1] == 'fullyAutomatic' :
    if len(sys.argv) >= 3:
        skipInitial = int(sys.argv[2])
    if len(sys.argv) >= 4:
        skipAfter = int(sys.argv[3])
    AutomaticTesting()








