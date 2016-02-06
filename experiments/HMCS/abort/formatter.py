#nThreads=[1, 2,4, 8, 16, 32, 36, 72, 144, 288, 576]
nThreads=[576/i for i in [576, 288, 144, 72, 36, 18, 9, 6, 3,  2, 1]]
delays=[0,  10,  100,  500,  1000,  10000,  100000,   1000000,    100000000,    10000000000]
nLocks=['AH1', 'AH2', 'AH3', 'AH4', 'TATAS', 'MCS_abort', 'CLH_abort' , 'H1', 'H2', 'H3', 'H4']


x = [[[0 for k in xrange(len(nLocks))] for j in xrange(len(nThreads))] for i in xrange(len(delays))]
f = open('1.txt')
#TATAS, AH
for i in range(0, len(delays)):
	for j in range(0, len(nThreads)):
		for k in range(0, 7):# 7 lks
			x[i][j][k] = f.readline().strip()
#	assert(int(x[i][j][k]) > 0)
#H

for i in range(0, 1): # only 1 delay
	for j in range(0, len(nThreads)):
		for k in range(7, 11):#a H locks
			x[i][j][k] = f.readline().strip()
#			assert(int(x[i][j][k]) > 0)

#output
for j in range(0, len(nThreads)):
	for i in range(0, len(delays)): # only 1 delay
		print str(nThreads[j]) + '\t',
		for k in range(0, 7): # locks
			print x[i][j][k] + '\t',
		print '\t\t\t', 
	print '\n',

for j in range(0, len(nThreads)):
	for i in range(0, 1): # only 1 delay
		print str(nThreads[j]) + '\t',
		for k in range(7,11): # locks
			print x[i][j][k] + '\t',
		print '\t\t\t', 
	print ''



for l in f: assert(0)
