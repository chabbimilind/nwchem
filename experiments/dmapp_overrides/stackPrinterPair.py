import os
import subprocess
from subprocess import call
l = open('barrier_call_stack').readlines()

for i in l:
	pieces  = i.split(':')
	s1 = pieces[2].split()
	s2 = pieces[3].split()
	print '==================:' + pieces[0] +    pieces[1] + '\n'
	#c1 = 'addr2line -C -f -e ~/nwchem-6.3_opt/bin/LINUX64/nwchem_dump ' + ' '.join(s1) 
	c1 = ['addr2line', '-C', '-f', '-e', '/global/homes/m/mc29/nwchem-6.3_opt/bin/LINUX64/nwchem_bd'] + s1
	c2 = ['addr2line', '-C', '-f', '-e', '/global/homes/m/mc29/nwchem-6.3_opt/bin/LINUX64/nwchem_bd'] + s2 
	#c2 = 'addr2line -C -f -e ~/nwchem-6.3_opt/bin/LINUX64/nwchem_dump ' + ' '.join(s2) 
	p = subprocess.Popen(c1 , stdout=subprocess.PIPE, stderr=subprocess.PIPE)
	out, err = p.communicate()
	print out
	print '------------\n' 
	p = subprocess.Popen(c2 , stdout=subprocess.PIPE, stderr=subprocess.PIPE)
	out, err = p.communicate()
	print out
	#print 'addr2line -C -f -e ~/nwchem-6.3_opt/bin/LINUX64/nwchem ' + str(cnt [1:])
