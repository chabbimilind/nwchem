import random

random.seed(0)
r = range(0,8)
allLists = []

transitions = []

def CreateTransition(loc):
	transitions.append(loc)
	if len(allLists[loc])== 0: return -1
	while  len(allLists[loc]) != 0: 
		x = allLists[loc].pop(0)
		if CreateTransition(x) == -1:
			transitions.append(loc)
	return 0


for i in range(0, len(r)):
	allLists.append(list(r))
	allLists[i].pop(i)
	random.shuffle(allLists[i])

CreateTransition(0)
print allLists
print transitions, len(transitions)
print [2**i for i in  transitions]


			
