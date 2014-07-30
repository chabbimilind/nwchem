#!/usr/local/bin/python 
# -*- python -*-
#   

import sys
import string
import os
import copy
import re
import time
import getopt
import socket
import pdb


dmappSkipList = [
'dmapp_register_progress_cb',
'dmapp_deregister_progress_cb',
'dmapp_queue_attach',
'dmapp_queue_detach',
'dmapp_get_version',
'dmapp_initialized',
'dmapp_thread_register',
'dmapp_thread_unregister',
# this is important... althought it is a dmapp call it is fully local
'dmapp_get_jobinfo',
'dmapp_get_rma_attrs',
'dmapp_get_rma_attrs_ext',
'dmapp_syncid_test',
'dmapp_syncid_wait',
'dmapp_gsync_test',
'dmapp_gsync_wait', 
'dmapp_thread_gsync_wait',
'dmapp_thread_gsync_test'
]

def WriteDMAPPWrappedSymbol(file, funcSig):
    fp = open(file,'w')
            
    for sig in funcSig:
        #skip the manually done ones
        if sig[1] in dmappSkipList: continue
            
        fp.write(' -Wl,--wrap=' + sig[1])
    fp.close();

def WriteDMAPPFunctionWrapper(file, funcSig):
    fp = open(file,'w')
    fp.write('''
// GENERATED FILE DON'T EDIT
#include<dmapp.h>
#include<stdbool.h>
#include "barrier_deletion.h"
extern "C" {
#define REAL_FUNCTION(name)  __real_ ## name
#define WRAPPED_FUNCTION(name)  __wrap_ ## name
''')

    for sig in funcSig:
        #skip the manually done ones
        if sig[1] in dmappSkipList: continue

        fp.write('extern ' + sig[0] +  ' REAL_FUNCTION(' +  sig[1] + ') (' + sig[2] + ') ;\n' )
        fp.write(sig[0] +  ' WRAPPED_FUNCTION(' +  sig[1] + ') (' + sig[2] + ') {\n' )

        if 'get' in sig[1] or 'ga_zero' in sig[1]:
            fp.write('\t gRemoteGetSeen = true;\n')
        fp.write('\t gAccessedRemoteData = true;\n')
        fp.write('\t return ')

        fp.write('REAL_FUNCTION(' + sig[1] + ')(') 
 
        args = sig[2].split(',')
        first = True
        for argTypeName in args:
            if not first:
                fp.write(', ')
            else:
                first = False
            param = argTypeName.split()[-1].split('*')[-1]
            param = param.replace('[]', '')
            if param.strip() != "void":
                fp.write(param)

        fp.write( ');\n')

        fp.write('}\n')
    fp.write('}\n')
    fp.close();


dmappPattern = '\s*(dmapp_return_t[\s\n]+)(dmapp_[a-zA-Z0-9_]*[\s\n]*)\(([^;]*)\)[\s\n]*;'


inFile = open(sys.argv[1]).read()
generatedWrapperFile = sys.argv[2]
generatedWraperScript = sys.argv[3]

lines = re.finditer(dmappPattern,inFile, re.MULTILINE)


defaultValue = re.compile('__dv\s*\(.*\)')

signatures = []
for line in lines:
    funcName = line.group(2)
    funcPrefix = line.group(1) 
    funcArgs = line.group(3)
    noDefaultArgs = defaultValue.sub('',funcArgs)
    #print p.group(1), p.group(2), p.group(3), p.group(4), p.group(5), '(', n, ')'
    args = noDefaultArgs.split(',')
    #print funcPrefix, funcName, '(' , noDefaultArgs, ')'
    for argTypeName in args:
        last = argTypeName.split()[-1]
	last = last.split('*')[-1] 
    	#print last
    signatures.append((funcPrefix, funcName, noDefaultArgs))

# explicitly add GA_Zero
signatures.append(('void', 'ga_zero_', 'int g_a', True))

WriteDMAPPFunctionWrapper(generatedWrapperFile, signatures)
WriteDMAPPWrappedSymbol(generatedWraperScript, signatures)

