# Raw54 E1=0LE E0=1LA: candidate census and certificates

Scope: `1RB---_1RC---_0RD---_1LD0LE_1LA0LE_------`. These are reproducible discovery results; no parent Cover has yet been checked.

The existing first-hole enumerator (agent47-raw112-cut/enumerate_fast.cpp) gives 1,816 splits, 27,205 cycle leaves, 13,222 last leaves and 1,342 open leaves, total completion mass 9,765,625. Largest observed weighted halt 545 (544 moves, one halt, zero delay), table `1RB1RF_1RC0RA_0RD0LD_1LD0LE_1LA0LE_HHH0RC`. Open table SHA256 c6ce7be3631b4544b5528fd717af5628a4b885745f16a8170970ffcc049efb4f. The frozen Raw54 bank (blob 56bf67275d597e354a0e827f6422ec68aa77f416) matches 1178 rows, leaving 164 misses (SHA256 0abdd7b494f234417e9079f683c2066174dcd3649a5e89070baff4686af3220b). IDs below are zero-based among misses in enumeration order.

74 additional FAR candidates appear in la-mutated.txt. Sparse n-gram candidates, width: IDs:
- 4: 16 68 75
- 6: 31 51 67 82 87 102 105 121 123 132 137
- 8: 36 54 78 80 81 133 134
- 12: 32 34 52 58 106 107 109 141 142 147 148
- 16: 59 110 111 129 131
- 20: 135

Ten additional exact symbolic return candidates, for the existing raw112_multisweep generator. Columns ID, state, left, right, P, jump, entry, a,b (cost a*n+b; V denotes repetition variable, - empty):
```
2 E - 0011V 010011 1 7 18 26
13 D 0000001 1111V 1 4 37 2 34
79 C 0111V 11 0111 2 13 32 70
89 D 0000V1001 - 0 4 15 2 30
90 D 0000V1001 - 0 6 15 4 38
92 D 0000V1001 - 0 4 15 2 28
103 B 001 1111V 1 8 25 4 66
143 D 01110111 1111V 1 8 69 4 138
157 C - 101011111V 1 6 32 4 82
163 C 0111V 11 0111 2 11 28 60
```
Generated proof bodies, not yet checked. Remaining 42 IDs: 26 27 37 38 40 42 44 45 48 49 55 56 60 61 62 63 64 65 66 69 70 76 77 83 84 93 94 95 99 100 104 108 119 122 126 127 138 144 145 151 161 162. Priority: recursive counter family 60,62–66; D alternating pair family 48,55,56,69,70,122; nested D family 76,77,144,145,161,162. Exact score 545 still requires proof for all cylinders.

The separate E0=1RF child has 2610 splits, 45064 cycles, 12821 last, 2146 open, observed maximum weighted score 845. Frozen bank hits 1967, misses 179. Open SHA ae1d7c235351d32702026c6d6d416d01548c257aab30e98773ea88b81d63113c; misses SHA b5cc41348b6fb3a76c7abd71623b8b36f880a5c0579b7478df7c99b82d9e0461. No further search on RF yet.
