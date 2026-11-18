# Valuation-uniform M0-even 8q counted increment: source draft

**Status:** the complete source-level Lean composition is now present, but it is **uncompiled and unaudited**. `M0EvenEightValuationSource.lean` proves the valuation-dependent prefix run; `M0EvenEightValuationQ4Source.lean` proves its left-facing cut, q4 right shape, blank far tail, and q4-suffix composition; `M0EvenEightValuationCountedSource.lean` composes the counted drain and declares `m0EvenEight_valuation_counted_increment_source`. No exact import-closure compile or transitive axiom audit has passed, so this remains intermediate work in `im-results/`.

## Source theorem draft

The existing `M0EvenEightGenericSource.lean` handles `n = 8q` with `q` odd. The valuation-uniform extension removes that restriction at source-draft level. The finite probes and symbolic coordinate checks below support the construction but are not proof acceptance.

Let (t=v_2(q)), with (q>0). For (Lge4+t), (8q<2^L), (a>0), and arbitrary (b), the proposed generalized q4 prefix has length
[
60+12a+12t.
]
It reaches state 4 at the original head, with the existing q4 right interface and left-facing word
[
[1];d_1^{a-1};operatorname{marker}(2);d_0;
operatorname{binDec}(L,8q-1);ell_h.
]

The q4 suffix draft then takes (39+3b) steps and reaches
[
S1(L,8q-1,2,a+b+1,2^b-1,0,h+5+3b).
]
Thus the complete reset prefix has cost
[
99+12a+12v_2(q)+3b
=operatorname{resetPrefixCost}(0,8q,a,b).
]
The counted-source wrapper composes the existing generic counted drain; its declared total cost is
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

`M0EvenEightValuationMacros.lean` contains candidate source lemmas for the state-1 right d1-block scan (`111 -> 001`), its n-block iteration, the exact `sweptRight1_block` output pattern, and the final `101` boundary. `M0EvenEightValuationFixedPrefix.lean` isolates the parametric 44-step prefix, its [-13,3] head bound, the `bridgeAt` lift, and the four-step 000 exit. `M0EvenEightValuationSweepFacts.lean` proves the post-bubble zero boundary and the 4+t right-run invariant. `M0EvenEightValuationSuffix.lean` removes q parity from the q4 suffix target-left identity. `M0EvenEightValuationEncoding.lean` instantiates the existing BinDec carry and valuation lemmas. All five are candidate Lean files, uncompiled; Agent6 has been asked to preflight them.


## Finite-frame target for the generalized bridge

The variable bridge can be represented by a simple pair of finite configurations, making `bridgeAt` from `CountedQ4Prefix.lean` directly reusable.

For (tge0), let the input finite configuration be state 3, head 0, with the existing `m0EvenEightBridgeStart.marked` plus the extra marks
[
{-14-imid 0le i<3t}.
]
These are exactly the (3t) extra one-cells in the valuation run.

The proposed output finite configuration is state 4, head 3, with marked set
[
{2,1,-1,3}
;cup;
{-4-3imid 0le i<4+t}
;cup;
{-14-3t,-15-3t}.
]
At (t=0), this is exactly the existing `m0EvenEightBridgeEnd`. The dynamic frame is
[
-15-3tle xle3.
]
The third cell of the final d1 block, at (-16-3t), is intentionally outside the frame and remains part of the arbitrary source tail.


The mark alignment is worth recording explicitly. The state-1 scan processes (4+t) triples from (h_N-12-3t) through (h_N-1). Its `001` outputs (in increasing tape coordinates) put ones at
[
h_N-10-3t, h_N-7-3t, ldots, h_N-4, h_N-1.
]
The final one at (h_N-1) is the last bit of `markerWord(2)); the preceding (3+t) ones are the corresponding d0-block marks. The four-step zero exit supplies the remaining d0 mark at (h_N-13-3t) and the first two cells of the final d1 block at (h_N-14-3t,h_N-15-3t). The third d1 cell at (h_N-16-3t) is outside the frame and remains from the source tail. This is exactly the finite `bridgeEnd_t` marked-set formula.

The exact finite theorem target is
[
fRun(tm2,63+12t,operatorname{bridgeStart}_t)
=operatorname{some}(operatorname{bridgeEnd}_t).
]
Its proof decomposes into the 44-step fixed prefix, 9t-step left bubble, four-step zero exit, (12+3t)-step state-1 d1 scan, and final three-step 101 boundary. The head path stays in the dynamic frame. Once this finite theorem and head bound are established, `bridgeAt` lifts it to the source tape.

The input frame match comes from `exists_odd_factor_bounded` and `binDec_carryPrefix`; the output left word comes from `binDec_sub_one_carryPrefix`. The generalized q4 cut therefore has left-facing prefix
`[true] ++ d1pow(a-1) ++ markerWord(2) ++ d0pow(4+t) ++ d1 ++ binDec(len,u) ++ lh`,
which is the same as
`[true] ++ d1pow(a-1) ++ markerWord(2) ++ d0 ++ binDec(L,8*q-1) ++ lh`.


## Full source-level composition

The current modules implement this composition without changing the original TM63 table or the generic q4 suffix. `M0EvenEightValuationSource.lean` proves the parameterized prefix run; `M0EvenEightValuationQ4Source.lean` proves the cut-tape interface and reset-prefix theorem; `M0EvenEightValuationCountedSource.lean` applies the all-ones counted drain. The five phases below explain the proof structure. They remain source drafts until the exact dependency closure compiles and its axiom profile is inspected.

Let (h_N=h-3a), and use the factorization (q=(2u+1)2^t) from `factor8q`.

1. **Initial sweep.** The first (3a) cells of `s1LeftFacing L (8*q) 0 a 0` are `d1pow a`, independent of q. Apply `counted_left_sweep` for (3a) cells: state 3 moves to (h_N).
2. **Fixed prefix.** The generalized source left word begins `markerWord 0 ++ d0 ++ d1pow(3+t) ++ ...`. Its first 14 cells are `markerWord 0 ++ d0 ++ d1pow 3`, independent of t. Thus the post-sweep tape matches the finite bridge start on [-13,3]. Apply `bridge_prefix44_at`; state 3 reaches (h_N-14), while the entire valuation-dependent left tail is preserved.
3. **Left bubble and zero exit.** The preserved tail has (3t) consecutive ones immediately left of (h_N-14), and the right neighbor is zero. Apply `counted_left_sweep` for (3t) cells (9t steps). The resulting head is (x=h_N-14-3t); the two cells (x-1,x) are the first two zeros of the following d0 block, and (x+1) is the swept zero. Apply `state3_zero_exit4`, reaching state 1 at (h_N-12-3t).
4. **Right d1 scan.** The next (3(4+t)) cells are all ones: the bubble has shifted (3t) ones right, adjoining the fixed 12 ones left by the 44-step prefix. Apply `counted_right_sweep_from1` for (4+t) blocks (12+3t steps), reaching state 1 at (h_N).
5. **Final boundary and E-scan.** The untouched cells at (h_N,h_N+1,h_N+2) are `101`. Apply `state1_101_boundary` (3 steps), reaching state 4 at (h_N+3). The existing E-scan over (3(a-1)) swept ones returns to (h).

The bridge portion after the initial sweep therefore costs (44+9t+4+(12+3t)+3=63+12t). Adding the initial sweep and E-scan gives (60+12a+12t), as claimed.

The output bridge frame is exactly the finite `bridgeEnd_t` described above. Its left-facing word is
`[true] ++ markerWord(2) ++ d0pow(4+t) ++ d1 ++ binDec(len,u) ++ lh`
before the E-scan restores the `d1pow(a-1)` prefix. This is precisely
`[true] ++ d1pow(a-1) ++ markerWord(2) ++ d0 ++ binDec(L,8*q-1) ++ lh`
by `binDec_sub_one_carryPrefix`. The right q4 interface is unchanged because the variable frame ends at relative cell 3; the existing source right tail is preserved. Then the parity-free q4 suffix-left identity and existing q4 suffix run apply, followed by the generic counted drain.



### Additional finite-frame bridge check

A direct exact-tape simulation of the parameterized finite bridge was run for every (t=0,ldots,100). All 101 cases reached state 4/head 3 after exactly (63+12t) steps, stayed inside the dynamic frame ([-15-3t,3]), and matched the proposed `bridgeEnd_t` marked set exactly (101/101). The reproducible Node probe now includes this independent loop and treats any bridge mismatch as a failing exit condition. This is computational evidence, not a Lean proof.


## Exact source theorem and root-integration boundary

The complete all-q counted-source declaration is now present in
`M0EvenEightValuationCountedSource.lean`:

`m0EvenEight_valuation_counted_increment_source`.

For `q>0`, `4≤L`, `8*q<2^L`, `a>0`, and arbitrary `b,h`, it states the original-table TM63 run

```lean
run tm2 (proposedIncrementCost 0 (8*q) a b)
  (s1Config L (8*q) 0 a 0 b h) =
  some (s1Config L (8*q-1) 2 (a+b+1) 0 (2^b-1)
    (h+5+(3*b:Int)))
```

The proof composes:
- the valuation-dependent q4 prefix of `60+12*a+12*v₂(q)` steps;
- the generic q4 suffix of `39+3*b` steps, giving reset-prefix cost
  `99+12*a+12*v₂(q)+3*b = resetPrefixCost 0 (8*q) a b`;
- the existing generic counted drain.

The theorem therefore supplies the local marker-0, `n=8q` S1 counted-increment row required by `countedRst012_of_prefix`, at source-draft level. The final declared primitive increment cost is `proposedIncrementCost 0 (8*q) a b`, equivalently
`6*4^b + 42*2^b + 12*a + 12*v₂(q) - 9*b + 51`.

**Validation boundary:** this is not yet a Lean-accepted theorem. The exact original import closure and the transitive `#print axioms` profile must be checked; reject `sorryAx`, `native_decide`, and custom axioms. Standard Lean axioms such as `propext`, `Classical.choice`, and `Quot.sound` are expected.

**Root boundary:** this is a local S1 counted-increment source lemma, not a blank-root reachability theorem, a halt witness, or a BB(6) certificate. The connection from the authentic blank-root orbit to these S1 configurations remains unproved. Do not conflate this `n=8q`, residue-zero row with the root-connected `n=8(2r)+4` residue-four handoff after middle row 11; they are distinct obligations.



## Orientation audit correction — 18 November 2026

The proposed one-cell contradiction is incorrect: it counts `markerWord 2` as length 3, but the source definition is
`markerWord 2 = [true,true,false,true]`, of length **4**.

Let (h_N=h-3a). In the target left-facing word
[
Q=[1] ++ d1^{a-1} ++ markerWord(2) ++ d0^{4+t} ++ d1 ++ tail,
]
the prefix ([1] ++ d1^{a-1}) has length (3a-2). Thus `markerWord 2` occupies indices (3a-2,ldots,3a+1), at physical coordinates (h_N+2,h_N+1,h_N,h_N-1). Its bits are (1,1,0,1), so the scanned one at (h_N-1) is exactly the fourth marker bit, not the first d0 bit.

The first d0 bit is at index (3a+2), hence at (h_N-2). The first d0 block occupies coordinates (h_N-2,h_N-3,h_N-4) in head-facing order and requires bits (0,0,1). The final right-scan block writes (0,0,1) in increasing coordinates (h_N-3,h_N-2,h_N-1), which gives exactly (1,0,0) when read from (h_N-1) leftward: the marker's final (1), then the first two d0 zeros. The preceding scan block supplies the d0 one at (h_N-4).

More generally, the state-1 scan writes ones at
[
h_N-1, h_N-4, h_N-7,ldots,h_N-(10+3t).
]
The first is the final marker bit; the remaining (3+t) positions are the first (3+t) d0 third-bits. The four-step zero exit supplies the final d0 third-bit at (h_N-(13+3t)), and also the first two bits of the following d1 block at (h_N-(14+3t)) and (h_N-(15+3t)). Its third d1 bit at (h_N-(16+3t)) lies outside the dynamic frame and is preserved from the source tail. The bridge's additional mark at (h_N+3) is the final bit of the preceding (d1^{a-1}) prefix.

Consequently the bridge mark set
[
{h_N+3,h_N+2,h_N+1,h_N-1}
cup {h_N-4-3j:0le j<4+t}
cup {h_N-(14+3t),h_N-(15+3t)}
]
matches the finite part of the q4 left-facing target. The alleged equation (1=0) is actually (1=1). This removes the stated orientation objection. The current source implementation formalizes the cut-tape obligations in `M0EvenEightValuationQ4Source.lean`: `m0EvenEight_valuation_q4_prefix_leftFacing`, `m0EvenEight_valuation_q4_prefix_rightShape`, and `m0EvenEight_valuation_q4_prefix_far_tail`, followed by `m0EvenEight_valuation_q4_reset_prefix_source`. Agent 4's independent symbolic review at [the coordinate review](../../communications/agent48/20261118T121242Z_agent4-m0-valuation-coordinate-review.md) checks the moving d0/d1 cells and boundary cells for every t. These are source-level declarations only; compilation and the final counted-source axiom audit remain open.
