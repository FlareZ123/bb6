# Candidate A-section ↔ pair-stack encoding

**Status:** exact local tape-encoding identity identified; the full A-step2/stack-system correspondence is still a conjectural bridge and is not proved here.

This note records a concrete match between the external `int-y1/proofs` A-section macro and the `google-deepmind/cryptids` token-stack representation.

## The first halting-cylinder macro

The external source's `step_An_1101` theorem has a branch for (n\equiv1\pmod3). Write (n=3k+1) and (m=4k-1). Its output is an E-state configuration whose left `ListBlank` expression is

```lean
default << 1 << 1 <+ [S1, S0]^m << 0 << 0
```

with the right side unchanged. Under the external `ListBlank` notation, this finite left list is
[
[0,0]\; ++\; [1,0]^m\; ++\; [1,1],
]
up to the usual blank-extension equivalence.

In the DeepMind #85 token encoding,
[
\operatorname{encTokens}(K,R3)
]
encodes each (k_i\in K) as (1^{k_i}0), followed by `encLeft R3`; and
[
\operatorname{encLeft}([(1,0)])=110.
]
Therefore, with
[
K=[0,0]\; ++\; \operatorname{replicate}(m,1),
\qquad R3=[(1,0)],
\qquad L=[],
]
we have
[
\operatorname{encTokens}(K,R3)
=00\,(10)^m\,110,
]
which is the same left `ListBlank` as the external expression, since the final extra zero is blank-equivalent. The control state is E and the right side is blank, so this A-step2 intermediate is exactly a `tok_EL K R3 []`-shaped configuration.

The DeepMind source has the generic transition lemma `tok_EL_0_cons`:
[
\operatorname{tok\_EL}(0::k::K)\;R3\;L
\;\vdash^+\;
\operatorname{tok\_CR}(k+1::K)\;R3\;L.
]
It applies to this (K), producing a C-token configuration with (K'=1::\operatorname{replicate}(m,1)). This is a concrete common subconfiguration in the two formal descriptions.

## Right-suffix encoding

The DeepMind definition
[
\operatorname{encRightNat}(a::L)=1^{a+1}0\;\operatorname{encRightNat}(L)
]
is a run-length encoding of a finite right suffix whose runs of ones are separated by zeros. If the right side begins with a run of ones and has no trailing nonblank zero, its unique run-length list (L) gives the same tape up to blank extension. If the scanned cell is a zero before that suffix, the zero belongs to the head rather than to `encRightNat L`; this is why the exact head-boundary convention matters. The `DL_0_n` mode supplies an explicit leading-zero variant.

## What is and is not established

Established from the source definitions:
1. the (n\equiv1\pmod3) output of `step_An_1101` has the displayed left tape;
2. the stated `K,R3` choice gives the same `ListBlank` encoding;
3. the E control state and blank right side match `tok_EL K R3 []`;
4. the generic `tok_EL_0_cons` theorem applies.

Not yet established:
- that the full `A_step2` macro (including its `iterate`, sweep, and return steps) is exactly the corresponding DeepMind token-stack closure;
- a uniform mapping for the (n\equiv0,2\pmod3) branches and arbitrary suffixes;
- a mapping from the blank-root `DR_n_n` stack trajectory to the particular A-section cylinder input;
- that the external 107-call halting path is a path in the DeepMind closed stack system.

## Next proof target

Formalize the displayed E-branch identity in a Lean file importing both source descriptions (or port the small encoding definitions into one project). Then prove one complete A-step2 call corresponds to a finite `tok_EL`/mode closure transition, preserving the encoded `(K,R3,L)` state. The 107-call cylinder can then be translated into a stack-system halting path. Separately, derive the stack state corresponding to the authentic blank root and prove that its orbit reaches the cylinder's input stack state. Do not infer the latter from the local encoding identity alone.


## Notation check

The external `BusyLean/TM.lean` defines
```lean
s << a  := ListBlank.cons a s
s <+ l  := ListBlank.append l s
l +> s  := ListBlank.append l s
```
and Mathlib's `ListBlank.append_mk` gives
`ListBlank.append l (ListBlank.mk s) = ListBlank.mk (l ++ s)`.
Thus the stored left-list calculation above is literal:
`[0,0] ++ [1,0]^m ++ [1,1]`.
The stack encoding gives
`[0,0] ++ [1,0]^m ++ [1,1,0]`; the extra final zero is identified with blank by `ListBlank`'s quotient. This removes the list-order ambiguity; the remaining uncertainty is the global A-step2/token-closure correspondence, not this local tape equality.


## Prefix parser correspondence

The DeepMind token lemmas give an exact run-length interpretation of several suffix cases. In particular,
[
\operatorname{encRightNat}(0::L)=10\;\operatorname{encRightNat}(L),
]
and the generic `tok_CR_zero` theorem is
[
\operatorname{tok\_CR}(k::K1)\;R3\;(0::L1)
\;\vdash^+\;
\operatorname{tok\_CR}((k+2)::K1)\;R3\;L1.
]
Thus a right-suffix prefix `10` (one 1 followed by its zero separator) is exactly an (L)-head of zero, and the token rule consumes it while increasing the current K-counter by two. This is the correct local counterpart of the A-step2 interpreter's repeated `10)-pair reduction.

For comparison, DeepMind's `tok_CR_1_0` theorem handles
[
\operatorname{encRightNat}(1::0::L)=11010\;\operatorname{encRightNat}(L),
]
not a bare `10` prefix:
[
\operatorname{tok\_CR}(k::K1)\;R3\;(1::0::L2)
\;\vdash^+\;
\operatorname{tok\_CR}(1::(k+3)::K1)\;R3\;L2.
]
The `tok_CR_1_1_nil` and `tok_CR_1_1_cons` lemmas similarly handle right-run lengths at least two. This gives a principled way to match the A-step2 suffix parser to the token rules: parse the bit suffix into run lengths, then select the corresponding `tok_CR` case.

This remains a structural correspondence, not yet a proof that the entire A-step2 sweep/return is the same run. The exact list update, head position, and accumulated raw-step count still need to be matched. The E-family's other suffix tests (`111`, `1100`, `110111`, `1101100`) should be compared against the corresponding `tok_CR`/`tok_DR` case lemmas rather than re-derived independently.
