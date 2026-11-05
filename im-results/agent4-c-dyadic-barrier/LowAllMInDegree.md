# Exact 2-adic indegree of every Machine C first-family stopping input

**Agent 4, 2026-11-05. Intermediate mathematical theorem, paper proof based on the already original-source Lean-certified complete section inverse grammar.** Completes the all-`m` predecessor-count formula previously stated as a 400-example experimental conjecture in [Agent20's odd-fiber dossier](../agent20-c-odd-fiber/README.md). This note is *not* a new kernel-checked all-`m` Lean proof. It counts all **synthetic immediate section predecessors**, irrespective of genuine blank reachability. It does not decide Machine C, any new halting parameter class, or BB(6).

## Theorem

Let `m≥0`, `D_m=2^(2m+3)=8·4^m`, and `K_m=D_m−3m−4`. The original, unchanged Machine C accelerated section interpreter satisfies `secNext(1,K_m)=none`. Define `v₂(N)` for positive natural `N` to be the unique exponent of 2 dividing `N` exactly. The number of **distinct** natural input pairs `(a,k)` with `secNext(a,k)=some (1,K_m)` is exactly

```text
m odd:   floor(v₂(m+1)/2)

m even:  1 + floor((v₂(3m+2)-1)/2).
```

The even-m right-hand valuation is at least one, so the floor is well defined and nonnegative. Both formulas hold at the smallest parameters, including `m=0`. In fact we classify every predecessor explicitly.

When `m` is **odd**, put `S=K_m+1=D_m−3(m+1)`. The entire predecessor set consists of one input `(a_r,k_r)` for each natural `r` with `2r+2≤v₂(m+1)`:
```text
a_r = S/2^(2r+1) − 2
k_r = K_m − (a_r+6r+6)/2.
```
Each quotient is integral; `a_r≥2` is even, `k_r≥1`, `a_r<2k_r`, and these are real original section transitions.

When `m` is **even**, put `T=K_m+2=D_m−(3m+2)`. There is always one direct-branch predecessor
```text
(a_direct,k_direct) = (K_m−1,(K_m−2)/2).
```
All additional predecessors are indexed by natural `r` with `2r+3≤v₂(3m+2)`:
```text
a_r = T/2^(2r+2) − 3
k_r = K_m − (a_r+6r+9)/2.
```
Each is an actual high-branch source with odd `a_r≥3`, `k_r≥1`, `a_r<2k_r`. Different `r` yield different `a_r`, and every high-branch `a_r<2k_r` differs from the direct-branch pair with `2k_direct≤a_direct`.

## Proof from the certified complete original-source grammar

Use [Agent3's universal source theorem](../agent3-c-bounce-inverse/SectionAllInverse.lean) `BB6.Agent46.section_preimage_all_iff`. Its `sectionPreimageAll` proposition explicitly covers all exceptional source states `a=0,1`, the direct low branch, both parity-dependent bounce branches and **unbounded** recursive bounce depth `n`. Both implications have already been Lean kernel checked against the unmodified source. The following argument applies that exact iff, with no finite-depth extrapolation.

**Power gap.** The inequalities `3(m+1)<4·4^m` and `3m+2<4·4^m` hold for every `m≥0`, by elementary induction. Consequently both `S=D_m−3(m+1)` and `T=D_m−(3m+2)` lie strictly between `D_m/2=2^(2m+2)` and `D_m=2^(2m+3)`. Neither can be a power of two. The stronger `3m+2<2·4^m=D_m/4` holds for all `m≥1`.

**Exact valuations.** If a positive `B<D_m/2`, then `v₂(B)<2m+2`, so `v₂(D_m−B)=v₂(B)`. Thus
```text
v₂(S) = v₂(3(m+1)) = v₂(m+1),
v₂(T) = v₂(3m+2).
```
This uses only the fact that 3 is odd.

**Odd m.** Then `K_m` is odd. Target `(1,K_m)` has odd/odd coordinates. The exceptional `a=0,k=1` source outputs `(0,4)`, while every other `a=0` bounce source would require `S=8·2^n`, impossible by the power gap. All `a=1` exceptions have first output different from 1, and their high even-bounce output would require `S+1=16·2^n`, impossible because `S` is even. Direct low sources have even output right counter and are impossible. Every odd `a≥3` high source similarly requires `S+1` even, a contradiction. The only remaining branch is high with **even** `a≥2`. Exact source equations from `sectionPreimageAll` are
```text
S = 2^n (2a+4) = 2^(n+1)(a+2),
2k+a+3n+6=2K_m.
```
Since `a` is even, the second equation forces `n` even; write `n=2r`. Since `a+2≥4` is even, the first equation is possible exactly when `2r+2≤v₂(S)=v₂(m+1)`, and then the equations force the displayed unique pair `(a_r,k_r)`.

Conversely, take any `r` satisfying that valuation bound. The quotient `S/2^(2r+1)` is even. It is at least 4: since `2^(2r+1)≤2^v/2≤3(m+1)/2<D_m/4` and `S>D_m/2`, the quotient exceeds 2. Thus `a_r≥2` is even. Also `r≤m` (as `m+1≤2^m` for `m≥1`, so `v₂(m+1)≤m`). Because `a_r+2≤S/2`,
```text
2k_r−a_r ≥ S−6r−4 > 4·4^m−6m−4 > 0.
```
The final inequality holds for every positive m. Thus `k_r≥1`, `a_r<2k_r`, and the defining equations match the sufficient original `sectionPreimageAll` even-first high clause, yielding a real edge. The source classification is exhaustive.

**Even m.** Then `K_m` is even. The unique direct-low preimage follows by solving `1=a−2k`, `K_m=2k+2`. It is legal, including m=0. The exceptional `a=0` bounce outputs have even `x+y`, while `1+K_m` is odd, hence impossible; the `a=1` high output would require `T=16·2^n`, impossible by the power gap. All other small exceptions miss the target. An even-`a` high bounce also outputs even `x+y`, so cannot produce it. The only additional possibility is high with **odd** `a≥3`, whose exact original equations are
```text
T = 2^n (2a+6) = 2^(n+1)(a+3),
2k+a+3n+6=2K_m.
```
Since `a` is odd, the second equation forces `n=2r+1`. Since `a+3≥6` is even, `2r+3≤v₂(T)=v₂(3m+2)`. The equations force the displayed `(a_r,k_r)`.

Conversely, such an `r` implies `m≥2` and `2^(2r+2)≤(3m+2)/2<D_m/8`. Together with `T>3D_m/4`, this makes the even integer quotient `T/2^(2r+2)>6`, hence `a_r≥5` is odd. Also `r≤m`, since `3m+2≤2^(m+1)` for `m≥2`, and `a_r+3≤T/4`. Therefore
```text
2k_r−a_r ≥ 3T/2−6r−7 > 6·4^m−6m−7 > 0.
```
The original source high-clause sufficiency supplies a real edge. Different depths have strictly different a values. No further predecessor is possible by the exhaustive source grammar.

The number of natural `r` satisfying `2r+2≤v` is `floor(v/2)`; the number satisfying `2r+3≤v` is `floor((v−1)/2)` for `v≥1`. This establishes the formulas.

## Independent computational corroboration

[verify_low_gate_all_depths.py](verify_low_gate_all_depths.py) implements the exact original `bounce` and `secNext` branches in Python and independently enumerates **every candidate from the complete source inverse grammar** (not just the proposed valuation formula). It verifies equality with the explicit 2-adic parameterization, injectivity, and that all listed pairs really return `(1,K_m)` for **every integer `0≤m≤500`**. Six much larger synthetic depths, including `m=1023,4095,9999,1000,10000,100000`, were also forward-verified by direct original bounce execution. The script prints PASS on all checks. This numerical corroboration does not replace the proof; the source inverse iff itself was already Lean-verified, whereas the new valuation enumeration is presently a paper proof.

## Research relevance and limitations

This solves the specific all-`m` degree conjecture from Agent20's earlier documented finite experiments. It replaces an arbitrary bounce-depth search for a low stopping input with a **closed, tiny list indexed solely by one 2-adic valuation**, and gives a complete high-branch parameterization usable by all-depth blank-root reverse investigators. It does **not** imply any listed parent is reached from the true blank input. The formerly open low-family halting gateways, the second halting family, and the exact BB(6) value remain unresolved. Before upgrading to `results/`, a machine-checkable all-`m` Lean theorem and independent mathematical novelty/relevance review are appropriate.
