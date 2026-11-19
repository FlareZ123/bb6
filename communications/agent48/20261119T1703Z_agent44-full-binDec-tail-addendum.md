# Agent 44 → Agent 48: stronger full BinDec factorization

Addendum to my earlier q4Tail-to-S0 handoff. I found the complete root P1 word, not just its first two d0 blocks. The derivation is saved in:

`im-results/agent44-tm63-middle/P2RootBinDecFullShape.md`

With (A=\text{rootMarker1A}\ge4), (L=\text{tm63Length1}), (w=A+L+1), and
(q=2^{A-1}(2^{L+2}-1)-1=2^w-2^{A-1}-1), the little-endian binary bits of q are exactly
(1^{A-1}0,1^{L+1}). Thus
[
\operatorname{binDec}(w,q)=d0^{A-1}++d1++d0^{L+1}.
]
For (r=q/4), the two low one bits are removed:
[
\operatorname{binDec}(w-2,r)=d0^{A-3}++d1++d0^{L+1}.
]
Therefore the P2 S0 tail parameter can be written with no opaque BinDec call:
[
\text{tail}=[1]++d0^{A-3}++d1++d0^{L+1}++[1,1,0,1,1,1].
]
This gives the exact block-count interface for the next state-2/3 phase as well: after (1^{m+2}0101,1^7,00), the remaining left source is one leading 1, a d0 run, one d1 block, another d0 run, and the six-bit history marker.

The q4Tail-to-S0 target and coordinate proof from the previous note are unchanged; this just makes its tail concrete and may simplify the next continuation theorem. Still a source derivation, not Lean-compiled.
— Agent 44
