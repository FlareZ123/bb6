# Raw39 1LE paired/triple invariant: 18789, 18790, 20550

These three literal partial machines have a common kernel-checked nonhalting proof:
```
18789 1RB1LE_1RC---_0RD0RC_1LD0RA_1LF0LE_0LA0LE
18790 1RB1LE_1RC---_0RD0RC_1LD0RA_1LF0LF_0LA0LE
20550 1RB1LE_1RC---_0RD0RC_1LD0RA_1LF0LE_0LA1RA
```
All completions of B1 never halt. At a section in A reading zero, the left list (excluding the scanned cell) is in (11|000)*. The right list has an initial zero followed by a terminal one run of length 3k, or a run of length 3k+1, an odd zero gap, and a tail. In a tail the terminal one run has length 3(k+1), and a nonterminal one run has length 3(k+1)+1; all intervening zero gaps are odd. The terminal run in the outer language may be empty.

A singleton gap transfers the first run to the left: the resulting left prefix is 0^(3k)11, and the next right run becomes active. The exact cost is 7+(3k+1). For a gap of three or more zeros (including the infinite blank suffix), the C/D sweep enters E with the left word intact and the right run increased by three. Its cost is 9+2r+e, where r is the old run length and e=2 for 20550, 0 otherwise. E consumes j leading pairs, converting them to zeros, then consumes two zeros of the next triple, and returns to A at the third zero (cost 2j+2). The new right prefix after the initial zero is a single one followed by 2j+1 zeros and the enlarged old run. Thus every section has a positive-cost return to the language. Explicit zero padding is semantically neutral under the original embed function. Blank belongs to the invariant.

The theorem BB6.Agent11Raw391LEPairTriple.never establishes NeverHalts for every compatible completion, using the original run, zrun_sound and run_project. Lean 4.36.0-rc2 compiled successfully against artifact 15036330602 (the existing accepted Raw39 1RB dependency bundle); the reachable import source/object hashes and compiler hash matched its manifest. Axiom report for advance and never: [propext, Quot.sound]. No fresh full source audit or child Cover is claimed.

Source: Raw391LEPairTriple.lean.xz.b64, decoded SHA256 d1544eb03d92ef5cd18d5761fa4a02290d3d787167cdebae1bc9f6b529555248. The generator prepare_le_residual.py decodes and maps the three frozen normalized indices to variants .a/.b/.c. The 1LE normalized residual is now 15. The local theorem is separate from the eventual audited semantic partition.
