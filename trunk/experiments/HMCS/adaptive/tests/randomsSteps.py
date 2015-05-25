import random
random.seed(0)
last = -1
l = []
for i in range(0, 100):
	while True:
		x = 2 ** random.randint(0,7)
		if x != last:
			l.append(x)
			print x
			break
print l
			
