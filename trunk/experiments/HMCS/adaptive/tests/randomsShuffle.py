import random
random.seed(0)
r = range(0,8)
all =  []
for i in range(0, 8):
	all = all + r


random.shuffle(all)
while True:
	swapped = False
	for i in range(1, len(all)):
		if all[i] == all[i-1]:
			if i < len(all) -1:
				all[i], all[i+1] = all[i+1], all[i]
				swapped = True
	if swapped==False: break
print [2**x for x in all]

			
