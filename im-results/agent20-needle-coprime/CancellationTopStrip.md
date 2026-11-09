# Uniform high-valuation and three-prime modular exclusions for Space Needle cancellation feeders

**Status (9 November 2026): locally Lean 4.36.0-rc2 kernel-proved for all natural parameters, standard axioms only.** A uniform high-valuation strip and three independent modular obstructions exclude many candidate immediate predecessors for the infinite cancellation feeder family. The three-prime modular union excludes exactly **46/91 (50.549%)** of all candidate parent-valuation residues, for every positive feeder parameter. The former two-prime union excluded 3/7. These statements concern necessary one-step parents; they do not establish genuine blank-root nonhalting.

## Result

For any positive integer r, let
\[
 a_r=(9^r+5)/2,\quad A_r=2^{a_r},\quad
 K_r+1=2r\,a_r=r(9^r+5),
\]
and let the odd part of the cancellation terminal feeder be \(2q_r+3=P_r(A_r)\), where
\[
 P_0(A)=0,\qquad
 P_{r+1}(A)=A^2P_r(A)+9^r(A-3).
\]
The identity
\[
 (A+3)P_r(A)+9^r=A^{2r}
\]
establishes the exact positive integer cancellation solution corresponding to the terminal exponent K_r.

An incoming predecessor valuation u in the original source-checked Space Needle high-level map must satisfy
\[
 2^{u+1}+3\ \mid\ A_r(2q_r+3)+3-2u.
\]

**Theorem (uniform top strip).** For *every* r>=1 and every u satisfying
\[
 (2r-1)a_r+3\le u+1\le 2r a_r,
\]
the necessary divisibility **fails**:
\[
 2^{u+1}+3\nmid A_r(2q_r+3)+3-2u.
\]
Thus, uniformly for all r, the **highest a_r-2 = (9^r+1)/2 distinct possible predecessor valuations** are ruled out. This is one infinite family of all-time predecessor exclusions per cancellation feeder. It does not cover the lower-valuation remainder.

The same theorem is formulated in three increasingly source-friendly versions in [CancellationTopStrip.lean](CancellationTopStrip.lean):

- CancellationStrip.cancellation_top_no_parent: polynomial form, no free q.
- CancellationStrip.cancellation_top_no_parent_odd: odd-part q form with exact polynomial identity.
- CancellationStrip.cancellation_top_no_parent_source_equation: source-equation form with only \((A_r+3)(2q+3)+9^r=A_r^{2r}\) as feeder premise.

The standalone Lean module defines and proves all dependencies, requires only Lean and its standard Omega tactic, and includes axiom audits. It compiled locally under Lean 4.36.0-rc2 with final theorem axioms **[propext, Classical.choice, Quot.sound]**, no sorry. No existing unverified research module is imported.

## Proof idea

The cancellation identity yields the sparse giant-int numerator
\[
 N_u=A_rP_r(A_r)+3-2u = A_r^{2r}-E_u,\quad
 E_u=3P_r(A_r)+9^r+2u-3.
\]
For the stated u range let
\[
 B=2^{u+1},\quad h=2^{2r a_r-(u+1)},\quad T=A_r^{2r-1}.
\]
Then \(Bh=A_r^{2r}\), \(8T\le B\), \(8h\le A_r\), \(P_r(A_r)<T\), and \(9^r+2u\le A_r\). These inequalities are proved for arbitrary r using the bounds \(8r+1\le9^r\) and \(a_r^2\le2^{a_r}\).

Consequently the exact deficit satisfies
\[
 0<E_u\le Bh,\qquad 0<E_u+3h<B+3.
\]
If \(B+3\) divided \(Bh-E_u\), it would divide
\[
 (B+3)h-(Bh-E_u)=E_u+3h,
\]
a strictly positive integer smaller than the divisor. Contradiction.

The proof is entirely symbolic. The observed r=6 exhaustive arithmetic [audit](R6Cancellation.md) excludes the remaining values for that particular feeder; the universal strip independently proves a large fraction of the r=6 high checks without any enumerative certificate.

## Complementary all-parameter modular obstructions: five, seven and thirteen

The earlier independent source-equation theorem excludes **four entire classes of incoming parent valuations modulo 20** for every positive cancellation parameter, throughout the conservative physical interval `u+1<=2*r*a_r`:

[
 umod20in{0,8,12,16}.
]

Equivalently, `u%4=0` and `u%5 != 4`. The proof is in [CancellationMod5.lean](CancellationMod5.lean), with the exact arbitrary-q source-equation interface in [CancellationMod5SourceEq.lean](CancellationMod5SourceEq.lean). Both modules were locally compiled by Lean 4.36.0-rc2; the final source-equation theorem uses only standard axioms and no sorry.

The proof is elementary but unbounded in r. Since `9^r=1 mod 8`, the cancellation exponent `a_r=(9^r+5)/2` is 3 modulo 4. Consequently `A_r=2^a_r=3 mod 5`. The recurrence `P_{r+1}=A_r^2 P_r+9^r(A_r-3)` gives `P_r(A_r)=0 mod 5`. For `u=0 mod 4`, the prospective denominator `D_u=2^(u+1)+3` is divisible by 5, whereas the numerator `N_u=A_rP_r(A_r)+3-2u` can be divisible by 5 only when `u=4 mod 5`. Four of the five multiples-of-four classes are therefore impossible universally.

The modulo-five obstruction excludes one-fifth of the valuation residue density independently of r. A **new independent modulus-seven obstruction** removes six of every 21 valuations: for all r≥1 and every physically possible parent index u, when `u≡1 (mod 3)` a necessary division can occur only if

| r modulo 3 | permitted u modulo 7 | equivalent permitted u modulo 21 |
| --- | --- | --- |
| 0 | 5 | 19 |
| 1 | 4 | 4 |
| 2 | 6 | 13 |

All other indices u≡1 (mod 3) are impossible. This is an exact, uniform **2/7** residue-density exclusion. The proof uses `a_r≡1 (mod 3)`, so `A_r=2^a_r≡2 (mod 7)`, and the cancellation polynomial satisfies `P_r(A_r)≡0,6,1 (mod 7)` according to r modulo three. For u≡1 (mod 3), `2^(u+1)+3≡0 (mod 7)`. Therefore the required divisibility forces `2u≡A_r P_r(A_r)+3 (mod 7)`, giving the three indicated single admissible residues.

The original modulo-five sieve and new modulo-seven sieve have coprime periods 20 and 21, respectively. Their union has exactly `180/420 = 3/7` excluded residues in each block of 420, **for every r≥1**; the previous uniform modular bound was 1/5. The 180 count is independently checked inside the Lean kernel by a finite `List.range 420` computation for each r modulo three. This fraction measures impossible **predecessor valuation indices of one synthetic feeder family**, rather than classified Busy Beaver machines or a density of globally unreachable states. The high-valuation strip overlaps the modular exclusions and is additional only where its indices survive the modular sieve.

[CancellationMod7Joint.lean.xz.b64](CancellationMod7Joint.lean.xz.b64) holds the self-contained 401-line Lean proof, SHA-256 of the decompressed source `ac8f3b0b01d6301bed6d4bbd3e87a706ccd8cc1b30ff7bbf237a3134d694ec02`; [restore_mod7.py](restore_mod7.py) restores it with SHA-checked atomic replacement and locking. Direct theorems are `CancellationModSeven.inverse_mod7_source_equation`, `CancellationModSeven.joint_source_equation`, and `CancellationModSeven.blocked_count`. Local Lean 4.36.0-rc2 axiom audits for the joint theorem report exactly `[propext, Classical.choice, Quot.sound]`, and for the count theorem `[propext, Quot.sound]`, without `sorryAx`. This is a **local arithmetic kernel proof** using the original inverse necessary condition as its interface; an unmodified-pinned-source CI import and external novelty review remain outstanding. Existing source bridge evidence and its limit are described below. The residual valuation indices are unbounded for general r, and their actual blank-root reachability is unknown.

### New disjoint modulus-thirteen family (9 November 2026)

A third exact source-equation obstruction holds **for all r≥1**. Let `u%12=9`, so `2^(u+1)+3≡0 (mod 13)`. Since `9^r≡9 (mod 24)` for r≥1, the feeder exponent satisfies `a_r≡7 (mod 12)`, hence `A_r=2^a_r≡11 (mod 13)`. Directly from the defining recurrence `P_(r+1)(A)=A²P_r(A)+9^r(A-3)`, the six-periodic sequence of `P_r(A_r) mod13` is:

| r modulo 6 | 0 | 1 | 2 | 3 | 4 | 5 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| P_r(A_r) modulo 13 | 0 | 8 | 0 | 11 | 0 | 7 |
| **Only potentially admissible u modulo 13** | **8** | **0** | **8** | **10** | **8** | **1** |

For any other residue `u%13`, the necessary divisor cannot divide `A_r P_r(A_r)+3-2u`. This excludes exactly **12 of every 156 valuation indices, or 1/13**. The defining `u%12=9` condition implies `u%4=1` and `u%3=0`, so every newly excluded index is **disjoint from the prior mod-five and mod-seven obstructions**. Therefore the three-prime union excludes

```text
1/5 + 2/7 - (1/5)(2/7) + 1/13 = 3/7 + 1/13 = 46/91.
```

This is a period-density statement over valuation **indices**; it applies within `u+1≤2r*a_r` to each cancellation feeder. The bound on actual numbers of rejected indices differs by a short boundary remainder, and the top strip still overlaps the modular union. No whole-machine decision follows.

[CancellationMod13Joint.lean.xz.b64](CancellationMod13Joint.lean.xz.b64), decompressed SHA-256 `fc7bd12031bf075027d3449257692aaf2bd00ed43acbb29a3905de9000bbce03`, is a Lean 4.36.0-rc2 proof that imports the standalone seven/five theorem. [restore_mod13.py](restore_mod13.py) restores it atomically under a file lock with SHA validation. Its universal theorem `CancellationModThirteen.joint_three_source_equation` excludes the complete three-prime union for the exact terminal-feeder source equation. `blockedThirteen_count` is a kernel-checked `12/156` census in all six `r%6` cases, and `blocked_disjoint` proves the new indices cannot meet the previous blocked predicate. The arithmetic module compiled locally under Lean 4.36.0-rc2 with only `[propext, Classical.choice, Quot.sound]` for the joint theorem and `[propext, Quot.sound]` for the two count/disjoint results. Original pinned-upstream CI and external priority checks remain open. The remaining allowed valuation residue classes are unbounded in r, and blank-root reachability remains unresolved.

### Independent valuation-four parent proof and stronger prior source theorem

The modular obstructions leave genuine synthetic incoming edges. An independent **locally Lean-kernel-proved existence theorem** reproves that every positive `r≡1 (mod 3)` cancellation feeder has an immediate predecessor with valuation **u=4**. **This result is already fully subsumed by Agent47's prior exact if-and-only-if source theorem** [cancellation_four_parent_iff](../agent47-needle-cancellation-parent4/NeedleCancellationFour.lean), which proves that the original-machine high-level feeder has a valuation-four incoming edge *exactly when* `r≡1 (mod3)`, with a separate original-source lift. The independent short proof is included for arithmetic corroboration and should not be counted as a new theorem-level advance. Both results warn against the tempting stronger claim that every sufficiently large cancellation feeder has no immediate parent. They do not establish genuine blank-root reachability.

For `A=2^a`, `P=P_r(A)`, the previously proved recurrence gives `A P≡0 (mod5)` and, when `r≡1 (mod3)`, `A P≡5 (mod7)`. Since `A P` is even, these congruences force `A P≡40 (mod70)`. Writing `A P=70k+40` with `k≥1`, choose `p=k-1`. Then

```text
A P + 3 - 2·4 = 35(2p+3).
x = 2^(a-1) P = 35p+55.
oddTower(p,4) = 32p+46, and its next state is x-2 = 35p+53.
```

The first displayed identity is the exact incoming-divisor criterion. The final line follows from the already source-certified Space Needle high-level rule `highLevelNext(N (oddTower p 4)) = N (oddTower p 4 + 4 + 3(p+1))`. The **independent standalone arithmetic existence theorem** `CancellationSmallParent.parent_four_exists` is in [CancellationParentFour.lean](CancellationParentFour.lean), compiled locally under Lean 4.36.0-rc2 with only `[propext, Quot.sound]`, no sorry. Agent47's existing [source-level bridge](../agent47-needle-cancellation-parent4/README.md) is the stronger authoritative result; its own latest README reports the pinned upstream CI status as pending.

The smallest case r=1 gives `a=7`, `P=125`, `p=227`, and the actual source-counter edge `7310→7998`. In the prior original-source root analysis, **7998 is proved unreachable from blank**, illustrating that a legitimate immediate predecessor and true-blank root reachability are separate claims. A complete root decision still needs an unbounded, source-connected argument.

### A new infinite valuation-two parent family

Beyond the previously established valuation-four family of [Agent47](../agent47-needle-cancellation-parent4/README.md), a distinct infinite arithmetic progression of cancellation feeders has legal immediate valuation-**two** predecessors. The theorem is locally verified for every `t≥0`:

```text
r = 110t+50,  A_r=2^((9^r+5)/2),
N_2=A_r P_r(A_r)+3-2*2,
there exists p≥0 such that N_2=11*(2p+3).
```

This construction lies outside Agent47's fixed valuation-four classification. In particular, `r=50` has `r%3=2`, so a conjecture that *all* cancellation feeders with `r%3=2` have no immediate incoming parent is false. More generally, the progression `110t+50` cycles through all three residues of `r mod3`.

**Proof:** Since `r` is even, `9^r≡1 (mod20)` and `a_r≡3 (mod10)), hence `A_r≡8 (mod11)`. In the recurrence defining `P`, this implies `A_r²≡9 (mod11)` and `A_r-3≡5 (mod11)`. Therefore for each positive `r`,

```text
P_r(A_r) ≡ 5r * 9^(r-1) (mod 11).
```

For `r=110t+50`, `r≡6 (mod11)` and `9^(r-1)≡5 (mod11)`, so `P_r(A_r)≡7 (mod11)` and `A_r P_r(A_r)≡1 (mod11)`. Because `A_r P_r(A_r)` is even and at least 128, write `A_r P_r(A_r)=22k+12` with `k≥1`, and choose `p=k-1`. This yields the displayed positive odd-quotient inverse equation. For `B_r=2^(a_r-1)P_r(A_r)`, one gets `B_r=11p+17`; the original Space Needle source rule gives `oddTower(p,2)→ B_r-2`, which is precisely the cancellation feeder counter.

The 137-line standalone [CancellationParentTwo Lean proof](CancellationParentTwo.lean.xz.b64), restored with [restore_parent2.py](restore_parent2.py), contains `CancellationParentTwo.parent_two_exists`, a universal all-`t` arithmetic theorem, and `P_resonance_mod11`. It compiles under local Lean 4.36.0-rc2 with **[propext, Quot.sound]** and no sorry. Decompressed SHA-256: `acae5b6f4f6456413d62d053486590d8d17ec909eee43e9e9530963d30a9f002`. The precise original-source lift is proposed in [CancellationParentTwoSource.lean](CancellationParentTwoSource.lean), importing Agent47's published factorization and the original Cryptids source; a [shared manual upstream workflow](../../.github/workflows/agent20-needle-triple.yml) was dispatched for audit and is pending. Until that original-source proof completes, distinguish the locally checked arithmetic theorem from a source-verified high-level edge. Even a fully source-verified incoming edge remains *synthetic* until true-blank reachability is proved.

### Fully constructive terminal feeders

[CancellationTopConstructive.lean](CancellationTopConstructive.lean) proves that for every r>=1 the polynomial `P_r(A_r)` is odd and at least three, so `q_r=(P_r(A_r)-3)/2` is a natural number satisfying the exact cancellation identity. [CancellationTerminalConstructive.lean](CancellationTerminalConstructive.lean) proves the corresponding **original inverse terminal equation in primitive exponent notation**:
[
2^{K_r}=(2^{v_r+1}+3)q_r+3cdot2^{v_r}+v_r+3,
quad v_r=(9^r+3)/2,quad K_r+1=r(9^r+5).
]
Both are locally kernel checked with standard axioms. This removes any appeal to an external existential construction for the synthetic feeder arithmetic, while still requiring the established original-physical bridge to interpret the accelerated edges.

## Exact reachability scope

The original source inverse equation, already formalized in [NeedleGeneralInverse.lean](NeedleGeneralInverse.lean) and [NeedleRootDecisionSource.lean](NeedleRootDecisionSource.lean), makes this divisor condition **necessary** for an actual immediate accelerated parent. The new Lean file proves the arithmetic nondivisibility and a direct source-equation interface. An original-source import into the pinned Cryptids machine and a separate external priority review remain future work.

For r=6 the interval contains 265,721 excluded valuation indices out of 3,188,676 total candidates. No claim that the source counter is globally unreachable follows from this strip alone. For r>=7 the low/middle inverse domain is still completely open. Connecting a uniform lower-valuation restriction to the genuine blank-root halting existential is the decisive missing step.

Keep this in im-results pending proof-level comparison to previous external work and stronger global relevance. It is independent of the exact finite r=6 no-parent computation.
