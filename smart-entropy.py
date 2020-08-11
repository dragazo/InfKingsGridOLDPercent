#!/usr/bin/env python

import sys, math

if len(sys.argv) != 4:
	print(f"usage: {sys.argv[0]} [target] [lower bound] [max size]")
	sys.exit(1)

target = float(sys.argv[1])
lowerbound = float(sys.argv[2])
maxsize = int(sys.argv[3])
for size in range(1, maxsize + 1):
	v = math.floor(target * size) / size
	if v >= lowerbound:
		print(f'{size} -> {v}')