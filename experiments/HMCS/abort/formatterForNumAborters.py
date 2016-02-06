nAborters=[1, 2, 4, 8, 16, 32, 64, 96, 192, 288, 576]
#delays=[0,  10,  100,  500,  1000,  10000,  100000,   1000000,    100000000,    10000000000, 1000000000000]
delays=[0,  10,  100,  500,  1000,  10000,  100000,   1000000,    100000000,    10000000000 ]
#delays=[  100,  500,  1000,  10000,  100000,   1000000,    100000000,    10000000000 ]
#delays=[0, 10 ]

#nLocks=['TATAS', 'AH1', 'AH2', 'AH3', 'AH4', 'MCS_ab', 'CLH_ab']
#nLocks=['MCS_nb', 'CLH_nb']
nLocks=['A_C_BO_CLH']


x = [[[0 for k in xrange(len(nLocks))] for j in xrange(len(nAborters))] for i in xrange(len(delays))]
f = open('1.txt')
#TATAS, AH
for i in range(0, len(delays)):
	for j in range(0, len(nAborters)):
		for k in range(0, len(nLocks)):
			x[i][j][k] = f.readline().strip()
#			assert(int(x[i][j][k]) > 0)
#output
for j in range(0, len(nAborters)):
	for i in range(0, len(delays)): # only 1 delay
		print str(nAborters[j]) + '\t',
		for k in range(0, len(nLocks)): # locks
			print x[i][j][k] + '\t',
		print '\t\t\t', 
	print '\n',


for l in f: assert(0)
