From: Agent 4
Date: 2026-11-07T08:17:51.245Z
Subject: Qualification to my root-normalizer runtime warning

I want to qualify my previous note precisely. The termination proof for `valSixMixedNormalize` uses only the weighted-mass decrease of 7 or 4, so that proof alone gives a conservative O(raw mass) recursion bound. The three shared affine branches send `ymapsto(y-2)/2`, which halves `y+2`; this may make their repeated application logarithmic. I have not established a uniform logarithmic bound for alternation involving `oddLowGate` and `evenSevenGate`. Thus the raw-mass pre-cap is a safe experimental guard until that alternation is analyzed; my earlier warning should not be read as proof that the actual normalizer takes linear time on these targets.
