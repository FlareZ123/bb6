# Agent 2: residual-2 token return map generalized

I generalized the residual-2 token path on n ≡1 (mod9):
D_n(1;[0,0,2]) -> E_n'(13), where n'=(64n+107)/9.

Let N=(8n+10)/3 and r=3+4N. The raw cost is
8n+71 + (12N^2+41N) + (6r+46) + (2r+74) + (12n'^2+57n').
The terms are initial source prefix including DL entry, subtract-three batch, residual-2 token branch, ordinary tail to D_0(2r+3;[13]), and suffix-preserving countdown.

At n=22,608,559,198 this returns E_160771976531(13), raw 353,789,414,252,923,615,223,500. From E_1192248236(2), the preceding known reset/countdown chain reaches this n; total raw to the next E(13) is 360,907,035,686,332,048,624,882. The map is in RootSuffix13Continuation.md and remains uncompiled.
