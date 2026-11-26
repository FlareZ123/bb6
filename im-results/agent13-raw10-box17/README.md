# Raw10 base34 rectangle 17: exact weighted maximum 7014

**Local Lean 4.36.0-rc2 proof complete, conditional on the independently source-certified r1 nonhalting theorem.** Full source integration is in progress in [CI 45745971080](https://github.com/FlareZ123/bb6/actions/runs/45745971080), pinned repository head d7340dab1fb1782f003fff0470ebdb0dffc9f070, upstream google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a.

## Statement

Rectangle 17 of the original 34-box raw10 residual contains 146,250 completions. Its fixed transition codes are A0=8,B0=11,B1=6,C0=17,C1=13,D0=11,E0=2,E1=23. The variable domains for A1,D1,F0,F1 are given explicitly in box17.py. The encoding uses 0=halt, 1+4*next+2*write+right for ordinary transitions, -1=unassigned in partial tables. The existing exact source-domain correspondence was accepted in CI 45702115754.

The generated Lean theorem BB6.Agent13.Box17.exactWeighted_of_r1 proves, given NeverHalts r1Machine, that a bound B holds for all machines fitting the literal domain iff 7014 <= B. The local build finished all 296 packed certificates and 261 compositional proof modules, with final axioms exactly [propext, Classical.choice, Quot.sound]. No sorryAx or native_decide. The witness table [8,9,11,6,17,13,11,0,2,23,3,10] reaches its halt after 7011 live transitions; the halt step and attainable incoming blank delay 2 yield score 7014. Box17Lower.lean proves this lower bound in Lean. The previously accepted r1 source theorem concerns 1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF; its 24 ordinary D1 replacements are total and never halt. The source graft is explicit in Box17SourceFull.lean. No change to the global canonical roster until the source build accepts and the remaining raw10 obligations are discharged.

## Discovery and certificates

First-hole exhaustive search partitions the domain into disjoint leaves: 559 halt leaves (mass 19,350), 10,511 all-ordinary leaves (10,511), 1,075 side cycles (81,264), 203 relative cycles (10,126), 301 open (24,999), total 146,250. Of the 301 open leaves, 263 have bit-window invariants, 33 have finite-stack run-length invariants, four have last-hole traces of 323,538,3209,7011 live steps, and one is the prior r1 cylinder. The final direct proof collapses ordinary alternatives at last holes, requiring only 2,138 terminal witnesses and 98 splits.

A new useful search abstraction is lag-k XOR RLE: encode a pushed raw bit w by w XOR the old bit at distance k-1, retaining the nearest k raw bits as well. Run-length encode the transformed stream, with capped modular lengths and bounded run count. The inverse stack transitions retain the actual raw bits. This found invariants for two period-six machines (k=6, cap=3, modulus=4, runs=5) and two period-four machines (k=4, cap=4, modulus=3, runs=7) beyond the ordinary windows and lag-one search. Incidence quotient compresses all 296 invariants to 92,274 joint states (largest 8,273). BitPackedStack.lean adapts Agent4's packed-stack checker to numeral-encoded inverse and push tables and bounded chunks; soundness checks the decoded relations directly rather than relying on the search abstraction.

## Reproduction

In this directory run python box17.py, python box17_ngram.py, python finish.py, python compress.py, python emit_bitpacked.py, python emit_direct.py. The known parameter list in finish.py eliminates repeated exploratory search. Build Box17SourceCore.lean with tools/lean_compile_closure.py and source dependencies; Box17SourceFull.lean also imports the pinned upstream r1 module and CryptidsTapeAdapter. The shared manual workflow now has verify_raw10_box17=true for a single source audit. Box17AuditCore.lean and Box17DirectCore.lean provide the soundness lemmas. emit_all.py is the earlier uncompressed emitter and not required by the direct proof.

## Remaining work

Accept the full source graft and consume this rectangle in the refined raw10 complement (including existing subrectangle certificates). Box17SourceFull.raw10_cover_except17 leaves all other boxes and the held source premise explicit. Exact BB(6) is still open. The adjacent original rectangle 16 contains 3,515,625 completions and is the next target.
