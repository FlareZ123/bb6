# Five-hole weighted TNF certificates: raw73 and raw80

Both are previously retained cylinders in the 124-entry authentic first-one residual roster. Local exact finite replay passed all branches, cycle conditions, FAR closures and weighted halt bounds.

| Raw | B1 | Exact candidate weighted maximum | Splits | Last-hole | Side-cycle | FAR |
|---|---|---:|---:|---:|---:|---:|
| 73 | 0LD | 367 | 599 | 1929 | 11624 | 225 |
| 80 | 1RE | 164 | 916 | 3163 | 17511 | 395 |

Each covers 25^5 = 9,765,625 compatible completions, with no cutoff-based verdict. Raw73's attaining completion is 1RB0LA_1RC0LD_0RD1RF_1LD1RE_1LA0LB_0RBHHH (366 ordinary moves); raw80's is 1RB1LA_1RC1RE_0RDHHH_1LD1RE_0RF0LB_0LA0LF (161 ordinary moves and two incoming blank moves E→F→A). The last halt query adds one.

Run `python generate.py 73 80`. This regenerates the complete enumerator trees, checks exact open-roster hashes and reconstructs FAR masks using the shared checker. It splits large proof terms into chunks of at most 120 nodes, combines their checked subtrees using a structural split lemma, and emits 24 modules per cylinder. Run `python replay.py 73` and `python replay.py 80` to independently replay exact tape-set and automata-set conditions. `FiveSiblingRoster.lean` projects these two exact keys from the original 124-roster, retaining bound 395.

**Source status:** local generation and independent Python replay passed; full original Lean source compilation remains pending. No global upper bound or BB(6) solution claimed.
