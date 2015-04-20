import sys
f = open('1.txt')
i = 0
for lines in f:
	if i % 4 == 0: sys.stdout.write('\n')
	sys.stdout.write(lines.strip() + '\t')
	i = i + 1
