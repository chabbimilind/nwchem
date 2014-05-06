import os
import sys
import subprocess
from subprocess import call

f = open(sys.argv[1])

f.readline()

while True:
        l = f.readline()
	if l == "": break
        l1 = l.strip()
        l2 = f.readline().strip().split()
	print "==============" + l1 + str(l2)

	c1 = ['addr2line', '-C', '-f', '-e', '/global/homes/m/mc29/nwchem-6.3_opt/bin/LINUX64/nwchem_barrier_trace'] + l2
	p = subprocess.Popen(c1 , stdout=subprocess.PIPE, stderr=subprocess.PIPE)
	out, err = p.communicate()
	print out
	#print 'addr2line -C -f -e ~/nwchem-6.3_opt/bin/LINUX64/nwchem ' + str(cnt [1:])
