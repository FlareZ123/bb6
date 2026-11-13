# Source-certified sixth-versus-seventh Machine C return image

The original Machine C first-return map `BB6.Agent46.secNext` has a new explicit **strict sixth/seventh source image**:

```
V(u,v) = (641 + 1024*u, 574 + 1024*v),  u,v ≥ 0, (u+v)%4=0.
```

Every `V(u,v)` admits six genuine consecutive source returns into it, but **no seventh**, regardless of source. It never occurs in the true blank section from `(5,1)`, at any return time. The family has ambient state-lattice density `1/4194304` and is disjoint from Agent4's older explicit all-depth and strict I4/I5, I5/I6 bands. This improves the documented Agent4 union to `66305/4194304`; neither density measures the fraction of halting machines.

There is also an exact high stopping obstruction for `m>=7`, with the original stopping equation `k+j+3*m+5=2^(2*m+2)*(j+3)`, on the following four residue pairs `(j mod 2048, (j+3*m) mod 4096)`:

```
(319,3517), (831,445), (1343,1469), (1855,2493).
```

These four disjoint parameter classes occupy density `1/2097152` of all `(j,m)` pairs as an arithmetic lattice. The four-class exclusion itself is source-certified by CI 42720140809. The separate `CSixSeventhC58.lean` wrapper proves admission by the prior ValSixFull+C58 all-depth and late-fast gates and attempts to integrate both this diagonal and the later s3 family into exact criteria; that wrapper still awaits a successful original-source audit.

## Formal artifacts

- [CSixSeventhArithmetic.lean](CSixSeventhArithmetic.lean): complete inverse grammar specializes to exactly three possible parents, with second-level branching handled exhaustively
- [CSixSeventhStrict.lean](CSixSeventhStrict.lean): six authentic incoming source edges, no seven
- [CSixSeventhRoot.lean](CSixSeventhRoot.lean): true blank-origin all-time nonreachability, using the actual first seven section returns
- [CSixSeventhGate.lean](CSixSeventhGate.lean): original narrower high-stop subfamily (also certified)
- [CSixSeventhGateWide.lean](CSixSeventhGateWide.lean): four congruence classes pulled back through the exact high stopping equation
- [CSixSeventhC58.lean](CSixSeventhC58.lean): prior-sieve admission and strengthened exact C58/late-fast iff with two new high-stop progressions; pending original-source CI

The original six/seven diagonal exclusion and its initial strict-image proof were checked against **unmodified original Lean machine and inverse source** by [CI 42720140809](https://github.com/FlareZ123/bb6/actions/runs/42720140809), success, with no printed `sorryAx`. The second strict-image slice and its all-time blank-root exclusion were source-audited in [CI 43300420208](https://github.com/FlareZ123/bb6/actions/runs/43300420208), also with no `sorryAx`. That run did not certify the separate `CSixSeventhC58.lean` parameter-pullback integration. The earlier widened source-image proof alone passed [CI 42719852275](https://github.com/FlareZ123/bb6/actions/runs/42719852275). The retained integration workflow is manual-only.



## A second strict sixth/seventh image family

The original strict cone used `u+v = 0 (mod 4)`. A second, disjoint family is described compactly by

```
(u+v) % 16 = (15+4*u) % 16
```

Equivalently, its four residue slices are:

```
u = 0 (mod 4), u+v = 15 (mod 16)
u = 1 (mod 4), u+v = 3  (mod 16)
u = 2 (mod 4), u+v = 7  (mod 16)
u = 3 (mod 4), u+v = 11 (mod 16)
```

Write the second parent in the H1 branch as
`P=(1113+650*u+1298*v, 321+187*u+375*v)` and its parent as
`R=(471+276*u+548*v, 644+374*u+750*v)`. On the full family,

```
(P.x+P.y) % 8 = 1
P.y % 16 = 10
(R.x+R.y) % 4 = 1
R.y % 2 = 0
```

The congruence is derived directly from the cone: `P.y % 16 = 10` is equivalent to `v = 15+3*u (mod 16)), which is the displayed family condition; substituting gives `(P.x+P.y)%8=1`. Also `u+v=3 (mod 4)), so `(R.x+R.y)%4=1`. Thus `P` lies in Agent34's all-source three-edge exclusion cone. The even/sum-one inverse theorem makes `P` the unique parent of `R`; hence `R` has no four-return ancestry. The unique-parent lemma for the H1 second branch then makes P2 have no five-return ancestry, and H1 has no six-return ancestry. The other two branches are unchanged: P0 has no one-return ancestry, and H3 has no three-return ancestry. Therefore the whole target band still has six genuine incoming returns but no seventh.

Four explicit infinite progressions in the family are:

```
u=16*t,   v=15  ->  (641+16384*t, 15934)
u=1+16*t, v=2   ->  (1665+16384*t, 2622)
u=2+16*t, v=5   ->  (2689+16384*t, 5694)
u=3+16*t, v=8   ->  (3713+16384*t, 8766)
```

The new root theorem `blank_ne_six_seven_band_s3` excludes every state in the full four-residue family from the blank-origin orbit at every time. The family is disjoint from the original diagonal because `u+v = 3 (mod 4)), not zero.

The formal extension is in [CSixSeventhStrict.lean](CSixSeventhStrict.lean) and [CSixSeventhRoot.lean](CSixSeventhRoot.lean), with the exact six/not-seven and all-time root theorems printed for axiom auditing. Both manual source workflows now compile the affine-inverse dependency required by this proof. **This second image family and its all-time blank-root exclusion passed original-source CI 43300420208 with no `sorryAx`.** Its C58 parameter pullback remains intermediate pending a separate successful audit.

## Exact parameter-only pullback

The auxiliary image coordinates can be eliminated entirely. The full second s3 family pulls back exactly to

\[j\equiv319\pmod{512},\qquad 3m+7j+14025\equiv0\pmod{16384}.\]

Equivalently, writing \(j=319+512u\), one has \(m\equiv42-6656u\pmod{16384}\). This forces \(m\equiv42\pmod{512}\), so every member has \(m\ge42\). The parameter cylinder has exact natural density \(2^{-23}\), and is disjoint from the earlier six/seven diagonal; together, the two disjoint strict-image exclusions cover exactly \(5/2^{23}\) of the \((j,m)\) parameter lattice. Within the common base cylinder \(j\equiv319, m\equiv42\pmod{512}\), these exclusions remove five of the 32 possible \(m\)-classes modulo 16384, leaving 27 residual classes. Those residual classes are not evidence of halting. The complete derivation, including the small-\(m\) exclusion needed for the converse, is in [S3PullbackCongruence.md](S3PullbackCongruence.md). The equivalence is represented by Lean draft theorems `s3_image_pullback_iff_congruence` and `highAllowedAllS3_iff_congruence` in [CSixSeventhC58.lean](CSixSeventhC58.lean), together with `blank_ne_s3_parameter_congruence`, a direct all-time blank-root exclusion for the affine cylinder. Both C58 and the latest six-sector high predicate now use the direct congruence form and invoke that theorem in their exact halting-iff criteria; the additions have not yet had a fresh original-source CI audit and do not upgrade the still-pending source integration.

## Candidate s2 odd-bounce exclusion (not yet certified)

A further candidate subfamily of the same affine image family is given by v+93u=42 (mod 128), equivalently u+v=2 (mod 4) and v=28+11t (mod 32) for u+v=2+4t. Its exact high-stop pullback is j=319 (mod 512) and 3m+102921=185j (mod 131072), with parameter density 1/2^26. The source-root proof outline uses the exact two-parent decomposition of R, Agent34's second three-edge cone for the odd-bounce parent, and three sixEvenRightGate normalizations of the direct-parent branch to an odd-right sum-one obstruction. This would add one of the 256 m-classes in the common j=319,m=42 (mod 512) base cylinder, giving a conditional combined count of 41 excluded and 215 residual classes out of 256.

**This is not yet a proven third exclusion.** The two-parent decomposition and full-normalizer composition have not been formalized in Lean or audited by original-source CI. See [S2OddBouncePullback.md](S2OddBouncePullback.md) for the detailed derivation and exact formalization tasks. Do not include this candidate in certified exclusion totals until that work is complete.

## Pullback to the full C58 high-stop parameter family

The second strict image family pulls back parametrically through the exact high-stop counter. Its high parameters satisfy

```
j = 319+512*u
k = 2^(2*m+2)*(j+3) - (j+3*m+5) = 574+1024*v
(u+v) % 16 = (15+4*u) % 16
m >= 7
```

The new lemma `prior_latefast_admits_s3_image_family` proves that **every** such high-stop parameter passes the preceding ValSixFull+C58 all-depth and arbitrary-depth late-fast filters. In particular:
- `j % 512 = 319`;
- the stopping equation modulo 512 forces `m % 512 = 42`;
- the dyadic all-depth and late-fast gates both require an odd residue for `m % 4`, while this family has `m % 4 = 2`;
- the original diagonal is disjoint: it would force `u+v = 0 (mod 4)`, whereas this family has `u+v = 3 (mod 4)`.

Two explicit high-stop progressions witness nonemptiness:
1. `j=831`, `m=9770+16384*t`; then `k=574+1024*v` with `v=2 (mod 16)`, corresponding to `u=1).
2. `j=1855`, `m=12842+16384*t`; then `k=574+1024*v` with `v=8 (mod 16)`, corresponding to `u=3).

The strongest new exact criterion is `blank_halts_iff_c58_late_fast_all_s3`: it removes every high-stop target in this full second image family, not merely the two displayed progressions, while preserving the exact Machine C blank-halting iff. The narrower two-progression corollary `blank_halts_iff_c58_late_fast_six_seven_both` and explicit removal theorems are also retained. [CSixSeventhC58.lean](CSixSeventhC58.lean) contains the generic admission proof, both concrete pullbacks, and the exact criteria.

**The second-family strict-image proof and all-time root exclusion passed CI 43300420208; the C58 integration did not compile in that run and remains pending.** The parameter-pullback file stays in `im-results/` and neither result determines Machine C or BB(6).
## Composition with the latest six-sector exact criterion (not yet audited)

The older `blank_halts_iff_c58_late_fast_all_s3` extends the C58/late-fast criterion. The newer `CSixSeventhSixAll.lean` goes further: it composes the same strict-image exclusion with `Agent11SixAll.blank_halts_iff_six_both`, whose high predicate already includes the C58/late-fast base, the odd-diagonal filter, both m=0 guards, and the six-sector source-exact normalizer.

The new admission lemma `prior_six_all_admits_s3_image_family` proves that **every** s3 high-stop parameter still passes that latest pre-existing high predicate:
- The stopping equation forces `m % 32 = 10`, while the additional odd-diagonal filter requires `m % 32 = (j+25) % 32 = 24`.
- Both m=0 guards are vacuous because `m ≥ 7`.
- At the source target `(x,y) = (641+1024u, 574+1024v)`, `x % 16 = 1`, `y % 2 = 0`, `(x+y) % 4 = 3`, and `(x+y) % 8 = 7`. These residues make all six branches of `sixForcedNormalize` inapplicable, so `sixForcedExcluded x y=false`.

Thus the s3 family is not already removed by the latest combined sieve. The new exact iff `blank_halts_iff_six_both_s3` adds it as a genuine infinite high-parameter exclusion while preserving the latest exact low branch and fixed-target decision.

[CSixSeventhSixAll.lean](CSixSeventhSixAll.lean) contains this composition and its admission proof. The manual-only `.github/workflows/agent11-c-diagonal-late.yml` has been extended to compile it after `CSixSeventhC58.lean` and reject `sorryAx`. **Neither the repaired C58 wrapper nor this stronger six-sector composition has yet passed a fresh original-source CI run.** Keep both in `im-results/` until the existing manual workflow succeeds.

## Independence from the integrated C58 all-depth sieve

The four high-stop classes are exactly equivalent to the single diagonal

```
j % 512 = 319
(3*m) % 4096 = (j+2879) % 4096
m >= 7
```

Reducing the second congruence modulo 512 gives `3*m = 126 (mod 512)`, hence `m = 42 (mod 512)`. The resulting residues are

```
j mod 256,128,64,32,16,8,4 = 63,63,63,31,15,7,3
m mod 256,128,64,32,16,8,4 = 42,42,42,10,10,2,2
```

This residue vector misses every conjunct of the preceding ValSixFull+C58 all-depth sieve:

- The original joint high rectangles fail: `(j+3*m+7) % 16 = 4`, the other `j % 4 = 1` gate has the wrong residue, the `m % 4 = 0/1` gate has the wrong residue, and `(j+3*m+5) % 8 = 2`.
- The Agent19 odd-special cylinder can only be its `j % 8 = 7` branch, where `(j+3*m+15) % 64 = 12`, not zero. The other three branches have incompatible `j % 8`.
- The Agent29 additions require `j % 8 = 5`, `j % 32 = 17`, `j % 64 = 57`, or `m % 32 = 6`; none holds.
- The ValSix additions require `m % 8 = 4`, `j % 128 = 81`, or `j % 32 = 1`; none holds.
- Agent19's arbitrary dyadic-depth gate requires `m % 4 = (2*r+3) % 4`, and the late three-cone gate requires `m % 4 = (2*r+1) % 4`; both right sides are always odd while `m % 4 = 2`.
- The Agent19 four-link condition has `(j+3*m+19) % 64 = 16`, not zero. The remaining ValSixFull rectangles likewise miss: `(j+3*m) % 128 = 61`, `j % 8 = 7`, and `m % 32 = 10`.
- For the affine right-four guard, the exact stopping equation gives `k % 4 = 2`, while `(2*j+3) % 4 = 1`. Their sum is 3 modulo 4, so affine normalization does not fire and its right coordinate is not four.
- The C58 rectangle would require `(j+3*m+5) % 256 = 198`, but the diagonal gives 194.

Thus the family is not a re-description of a previously removed parameter class. The concrete progression `m=42, j=1343+4096*t` satisfies the diagonal for every `t : Nat`; it is an explicit infinite family admitted by the old all-depth predicate and rejected by the new source theorem.

[CSixSeventhC58.lean](CSixSeventhC58.lean) formalizes the residue derivation, admission by both the all-depth and late-fast predicates, and two strengthened exact halting iff statements. In particular, `prior_latefast_admits_six_seven_diagonal` proves that the diagonal also passes the executable arbitrary-depth late gate, while `blank_halts_iff_c58_late_fast_six_seven` adds it to the latest C58/late-fast exact criterion. The source exclusion itself was already certified in CI 42720140809; the new admission lemmas and integrated iff statements have been added to the manual-only [Agent 11 C58/late-depth workflow](../../.github/workflows/agent11-c-diagonal-late.yml), but **the integration has not yet been source-audited**. Keep this extension in `im-results/` until that check succeeds. The exact C58 low/high existential remains unbounded, and neither this family nor the integration resolves Machine C or BB(6).

The complete theorem statement, inverse branch arithmetic and density synthesis are in [the academic result](../../results/2026-11-09-machine-c-sharp-sixth-seventh-image-agent4.md). The original Machine C blank-halting problem and BB(6) remain open.


## 2026-11-12 source-audit status

CI run [43300420208](https://github.com/FlareZ123/bb6/actions/runs/43300420208) on Lean 4.36.0-rc2 compiled the **second strict sixth/seventh image theorem and its all-time blank-root exclusion**:

- `exactly_six_not_seven_s3` and its four infinite progressions have axioms `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
- `blank_ne_six_seven_band_s3` also has no `sorryAx`; it proves that every state in the `(u+v)%16=(15+4*u)%16` sector is absent from the genuine blank-root section orbit at every time.

The same run did **not** certify the `CSixSeventhC58.lean` pullback integration. Agent 11's diagnostics identified core-tactic, conjunction-destructuring, coordinate-rewrite, and local-let issues. These were repaired in commit `d751a5c111e0b2bfff821a50d9bd36d42134d081`, but that revision has not yet been audited by a fresh original-source run. Therefore the two displayed high-stop progressions `(j,m)=(831,9770+16384*t)` and `(j,m)=(1855,12842+16384*t)` remain candidate C58 parameter pullbacks, not certified exclusions from the exact C58 halting predicate. Use the existing manual workflow `.github/workflows/agent11-c-diagonal-late.yml` for the next audit; the temporary push-triggered audit workflow was removed.

This separation is important: the infinite strict image family and its all-time blank-root exclusion are proven; the parameter-family composition into the C58 halting equivalence is not yet proven.
