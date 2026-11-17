# Valuation-uniform M0-even 8q increment: experimental extension

**Status:** intermediate computational result and proof plan only. This is not a Lean theorem and does not belong in `results/`.

## Conjectured source theorem

The existing `M0EvenEightGenericSource.lean` handles `n = 8q` with `q` odd. Experiments on the original TM63 transition table indicate that the oddness restriction is unnecessary.

Let (t=v_2(q)), with (q>0). For (Lge4+t), (8q<2^L), (a>0), and arbitrary (b), the proposed generalized q4 prefix has length
[
60+12a+12t.
]
It reaches state 4 at the original head, with the existing q4 right interface and left-facing word
[
[1];d_1^{a-1};operatorname{marker}(2);d_0;
operatorname{binDec}(L,8q-1);ell_h.
]

The existing q4 suffix then takes (39+3b) steps and reaches
[
S1(L,8q-1,2,a+b+1,2^b-1,0,h+5+3b).
]
Thus the complete reset prefix has cost
[
99+12a+12v_2(q)+3b
=operatorname{resetPrefixCost}(0,8q,a,b).
]
Composing the existing generic counted drain would give
[
operatorname{proposedIncrementCost}(0,8q,a,b)
=6cdot4^b+42cdot2^b+12a+12v_2(q)-9b+51.
]

The current odd-`q` theorem is exactly the (t=0) special case.

## Discovered phase decomposition

The observed prefix decomposes into source-level operations:

| Phase | Steps | Endpoint |
|---|---:|---|
| Existing left sweep | (9a) | state 3, head (h-3a) |
| Fixed bridge prefix | (44) | state 3, head (h-3a-14) |
| Valuation bubble | (9t) | state 3, head (h-3a-14-3t) |
| Zero exit | (4) | state 1, head (h-3a-12-3t) |
| Right scan of (4+t) d1-blocks | (12+3t) | state 1, head (h-3a) |
| Final `101` boundary | (3) | state 4, head (h-3a+3) |
| Existing E-scan | (3(a-1)) | state 4, head (h) |

The sum is (60+12a+12t).

The key operation is a zero-bubble sweep. At a state-3 head (x), with a one at (x) and a zero at (x+1), the original-table transitions
[
3/1	o1/1R,quad 1/0	o2/1L,quad 2/1	o3/0L
]
move the zero one cell left in three steps. Repeating this across (3t) ones costs (9t) and moves the head left (3t). The existing `counted_left_sweep` lemma in `im-results/agent24-champion-time/CountedSweep.lean` is the natural formalization.

The four-step zero exit uses the resulting three-zero boundary and enters state 1. The next (4+t) d1-blocks are scanned rightward from state 1. A reusable three-step lemma should establish
[
1/1	o5/0R,quad 5/1	o3/0R,quad 3/1	o1/1R,
]
transforming one `111` block to `001` and advancing three cells. A final three-step `101` boundary enters state 4. The existing E-scan returns to the original head.

## Binary encoding identity

Write (q=2^t u), with (u) odd. The recursive `binDec` identities to prove are
[
egin{aligned}
operatorname{binDec}(L,8q)
&=d_1^{3+t};d_0;
  operatorname{binDec}left(L-4-t,rac{u-1}{2}ight),\
operatorname{binDec}(L,8q-1)
&=d_0^{3+t};d_1;
  operatorname{binDec}left(L-4-t,rac{u-1}{2}ight).
end{aligned}
]
The bridge therefore converts the leading (d_1^{3+t}d_0) into (d_0^{3+t}d_1). The generalized q4 left interface retains `d0 ++ binDec L (8*q-1)` without expanding that tail by parity cases.

The q4 suffix target-left proof can consequently be generalized without a q-odd hypothesis: retain
[
operatorname{binDec}(a+b+1,2^b-1)=d_0^b d_1^{a+1}
]
and split (d_1^{a+1}=d_1^2d_1^{a-1}), leaving `binDec L (8*q-1)` untouched.

## Reproducible experiment

Run:
```sh
node im-results/agent48-counted-inc0/m0_even_eight_valuation_probe.js
```

The probe uses the original TM63 table, the repository's S1 tape encoding, and exact finite-support equality. It checks every (q=1,ldots,32), (a=1,2,3), and (b=0,1,2): 288 cases. It checks every phase boundary, the generalized q4 cut tape, and the exact pre-drain S1 endpoint after the existing q4 suffix. Expected output: `tested = 288`, `failures = []`.

This is bounded computational evidence only. It does not prove the generalized theorem or execute the counted drain for these even-`q` cases.

## Lean proof route

1. Split the existing finite bridge at step 44. Prove the 44-step prefix with the bit at its final head parameterized; that bit is not read during the prefix. The pre-transition heads stay in the fixed window.
2. Lift the fixed prefix to the original infinite tape.
3. Apply `counted_left_sweep` to (3t) ones.
4. Prove the four-step zero exit from the resulting three-zero boundary.
5. Add the state-1 rightward d1-block sweep (`111 -> 001`) by induction, followed by the three-step `101` boundary.
6. Reuse the existing E-scan and q4 right-interface lemmas.
7. Instantiate `exists_odd_factor_bounded` from S1Encoder with `q` and length `L-3`; then apply its existing `binDec_carryPrefix` and `binDec_sub_one_carryPrefix` lemmas with exponent `t+3`. Use CountedReset's `v2_odd_factor` to rewrite `v2(8*q)=t+3` in the reset cost.
8. Prove the generalized q4 suffix target-left equality using the existing unary-counter identity, then reuse the q4 suffix and counted-drain theorems.

The 44-step prefix, left zero-bubble, four-step exit, right d1-block scan, and final `101` boundary are the only new bridge components. The existing q-odd source theorem remains valid and should not be removed until the generalized Lean proof compiles and its transitive axiom profile is inspected.


## Lean helper candidate

`M0EvenEightValuationMacros.lean` now contains candidate source lemmas for the state-1 right d1-block scan (`111 -> 001`), its n-block iteration, and the final `101` boundary. It is uncompiled. Agent6 has been asked to locally preflight this leaf and report its axiom profile.
