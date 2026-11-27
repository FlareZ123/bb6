# Triple before a nonbinary entry: an arbitrary-tail halting cylinder

**Status:** source-clause proof, finite cost corroboration; extends the [general binary triple barrier](GeneralTripleBarrier.md). No authentic blank-root hit is proved.

Let (G(M,U)=CR([0],0^M U)), (M\ge 1), with first-coordinate pair entries in (U). For every binary word (w) containing 111, every (z\ge0), and **every finite natural-valued tail (T)**, the configuration

[
G(M,w\,1\,0^z\,2\,T)
]

halts. The extra 1 separates the protected triple from the nonbinary entry; neither the number of intervening zeros nor the tail entries are bounded. A second version replaces 2 by any (x\ge2) provided (T\in(\{0,2,3,\ldots\}\mid 01)^*). The latter means a concatenation of single entries other than 1 and two-entry blocks [0,1], not a condition on binary tape bits.

## Protected zero invariant

In the general triple proof replace the strict pairable-token tail grammar by

[
P ::= \epsilon\mid kP\ (k\ne2)\mid 12P\mid 0T
]

where (T) in the final alternative is completely arbitrary. Thus we require pairing of 2s only *before* the first zero. A good head still has positive value different from 2; its tail belongs to (P). The strict grammar is a special case.

Every lemma of the general proof remains valid. In the splitting lemma the new case (0T) is an immediate stop at zero, with empty scanned prefix. The zero branch is fatal using only the following token, because the collected left prefix is in ((0\mid10)^*); it never needs to inspect the arbitrary suffix after that token. The high branch preserves the grammar: it removes a high token after leading ones and prepends at least four ones before its residual. If that residual is zero it establishes a protected cut, otherwise the existing cut is preserved in the tail. For residual two its preceding 1 is available. Head-zero and head-10 collection also preserve the grammar. All other cases of the termination argument are unchanged.

A final two-zero padding in the token representation still ensures a following token exists at every zero stop, including the last token. This is not an assumption about the physical input: the padding occurs at the blank end.

## Exact entry into the protected region

Use the source's token encoding of the ordinary pair stack; each right entry (u) maps to token (u+1), followed at the blank end by two zero tokens. Define (W=\operatorname{reverse}(w)) and (R=\operatorname{map}(t\mapsto t+1,T)). The existing source-clause prefix reaches

[
tok\_EL((w+1)\,2\,1^z\,(x+1)\,R\,00,[],0^{M+2}1)
]

at cost (2M+23). Scanning (w) by tok_EL_1 / tok_EL_2 costs (2\#_0(w)+7\#_1(w)). The additional 1 and (z) zeros cost (7+2z), with left stack (0^{z+1}1W0^{M+1}1).

Apply tok_EL_add3 to (x+1), costing 5 and leaving residual (x-2), then (z+1) tok_DR_zero steps (cost (4(z+1))) and tok_DR_succ (cost 3). The exact resulting configuration is

[
tok\_CR(1^{z+3}(x-2)R00,[],0W0^{M+1}1).
]

The total entry cost is

[
2M+42+2\#_0(w)+7\#_1(w)+6z.
]

The left word still contains 111, because only the *extra* 1 was consumed. For (x=2), the zero at the end of (1^{z+3}0) protects all of (R); the new good condition holds even when (T) contains arbitrarily long adjacent-1 runs. For (x\ge2) and the specified grammar for (T), (R) is strictly pairable and the residual (x-2) is either a singleton different from 2 or paired with the last leading 1. Thus the same argument applies.

The exact halting time is this entry cost plus the protected-good CR algorithm of the general theorem. Its time can depend on the inspected prefix of (R), but no subsequent portion after the first zero stop affects it. In the (x=2) case the time is independent of all of (T) (including whether it is empty), because the protected zero is retained until used in the fatal branch. That branch's cost does not depend on the token following zero.

## Finite corroboration

The executable [nonbinary_triple_barrier.js](nonbinary_triple_barrier.js) compares the exact algebraic cost with the independent source-clause transcription, from the **ordinary G entry**. It tested 34,596 configurations: every binary word of length 3–8 containing 111, offsets 1 and 5, zero gaps 0,1,3, five high values 2,3,4,5,9 and ten different tails restricted by the protected invariant. All exact halting times agreed. In particular 5,580 of the x=2 cases had tails violating strict pairing; they still halted. Largest observed cost 277. These are finite cross-checks of a general proof, not evidence about the frequency of root hits.

The missing source gate is the formal grammar extension and quantified G-entry composition. The missing machine-level gate is proving that an authentic root reaches one of the expanded cylinders. No BB(6) numerical claim is made.
