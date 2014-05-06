import os
l = open('barrier_call_stack').readlines()

for i in l:
	cnt = i.split()
	print '------------:' + cnt[0] + '\n'
	os.system('addr2line -C -f -e ~/nwchem-6.3_opt/bin/LINUX64/nwchem ' + ' '.join(cnt[1:])) 
	#print 'addr2line -C -f -e ~/nwchem-6.3_opt/bin/LINUX64/nwchem ' + str(cnt [1:])
