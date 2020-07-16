#!/usr/bin/env python

import sys, math

if len(sys.argv) != 3:
	print(f"usage: {sys.argv[0]} [target] [thresh]")
	sys.exit(1)

target = float(sys.argv[1])
thresh = float(sys.argv[2])
denom = 0
while True:
	denom += 1
	numer = round(target * denom)
	v = numer / denom
	if abs(v - target) <= thresh:
			print(f"found {numer}/{denom} = {v}")
			sys.exit(0)
