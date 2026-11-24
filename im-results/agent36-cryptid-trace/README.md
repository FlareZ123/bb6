# Cryptid D: original-source packet closure, 3-adic lifting, and zero-marker recursion


## Current root-level frontier (24 November 2026)

The highest-value next step is now to connect the arbitrary-suffix section-return theorem to the four authentic blank roots, rather than expanding another isolated packet-residue catalogue.

**Source-wide return estimate.** Agent 32's [global source spatial-growth dossier](../agent32-d-growth-bands/README.md) reports a Lean-checked theorem `section_bands` for every original-source F/0 section `Section(n,v)`, with n≥2 and v empty or beginning in 0. At a positive time the unchanged machine either reaches frozen state 6 or returns exactly to another such section `Section(n',v')), with

```text
8*n ≤ 3*n' + 23
3*(n' + L(v')) ≤ 8*(n + L(v)) + 135
```

where L is the trimmed suffix length. This is a positive-time return theorem, **not yet a first-return theorem**; the halt alternative remains explicit.

**Widened phase-band separation.** [`SectionBandSeparation.lean`](SectionBandSeparation.lean) replaces Agent 26's regular-model upper constant 40 by the source-wide constant 135. It proves, in Lean 4.36.0-rc2, that any finite paths satisfying the resulting `Edge135` inequalities from distinct arithmetic anchor/index pairs have different unary lengths. The four existing anchor bands still have strict adjacent gaps (minimum margin 3,522) and all cross-band gaps (minimum margin 777,686). Manual acceptance: [CI 45378809847](https://github.com/FlareZ123/bb6/actions/runs/45378809847); all new theorem axiom profiles are standard `[propext, Quot.sound]` or fewer.

**Authentic anchor connection (now source-checked).** [`FourRootAnchorSource.lean`](FourRootAnchorSource.lean) composes the exact original-source blank prefixes with Agent 2's already-proved `ERemaining.source_contract` through `DRegularSourceShift.paired_original_run` and Agent 26's `RegularBands.anchor_run`. It proves observationally exact source reachability of all four arithmetic anchors:
- D3 / source state D (state 3): blank root → unary seed 5 in 15 steps → anchor 0 after 10 DRegular returns.
- D0 / source state A (state 0): blank root → unary seed 9 in 36 steps → anchor 1 after 10 DRegular returns.
- D2 / source state C (state 2): blank root → unary seed 15 in 92 steps → anchor 2 after 10 DRegular returns.
- D1 / source state F (state 5): blank root → unary seed 39 in 403 steps → anchor 3 after 9 DRegular returns.

The theorem `anchor_measures` identifies these four source endpoints with the exact `GrowthBands.base` sections. Manual source acceptance: [CI 45380597925](https://github.com/FlareZ123/bb6/actions/runs/45380597925). The root-prefix and anchor-composition theorems have axiom profile `[propext, Classical.choice, Quot.sound]` or fewer; the gate rejects `sorryAx` and `native_decide`. These are original six-state source-table starts; Agent 19's physical root-transfer dossier supplies the correspondence to the four literal rooted machines.

**First-return nuance.** The lack of first-return minimality in `section_bands` does *not* block the conditional path-separation theorem. Its positive-time halt-or-return witness suffices: if a root is nonhalting, the designated endpoint must be reached; any earlier halt would already decide that root. Agent 26's `Path` and this dossier's `Path135` accept any positive-time return. Earlier F/0 checkpoints therefore do not need to be excluded for this particular noncoalescence result. Do not claim first-return minimality.

**Scope:** the widened arithmetic separation theorem and the four source-anchor connections are now kernel-checked. The remaining step is to instantiate `Edge135` with Agent 32's arbitrary-suffix `section_bands` theorem and construct the conditional all-time paths. This still does not decide whether any root halts, establish a closed nonhalting invariant, or change a BB(6) bound. The prepared-packet `safeZ` / `safeYPlusK0` results remain complementary sufficient return criteria, not substitutes for this root-level programme.

### Immediate next action

Add a direct adapter from Agent 32's exact `section_bands` witness to `Edge135`, then inductively build finite return paths from the four source-connected anchors under the explicit nonhalting hypotheses. Apply `disjoint_paths` to obtain conditional all-time separation. Keep the halt branch explicit; once this structure is established, investigate whether any root's branch can be decided by a forward-closed invariant or a halting cylinder.


## New original-source exceptional Y3 packet closure and 3-adic lifting (23 November 2026)

**Scope:** Prepared physical packets of the original Cryptid D six-state machine, not proven blank-reachable. Exact BB(6) and Cryptid D blank-tape halting remain open.

A complete, source-sound **sufficient acceptance test** for the one-fixed-marker guarded B/E packet normalizer is now formalized in [`Y3SafeNormalizer.lean`](Y3SafeNormalizer.lean). Let (Y_3=(01)^3 11) and (d=normalizeWithCount(a,q,p).2). The predicate `terminalY3 d` accepts iff:

- `d.a % 3 = 0` (A source terminal, arbitrary p/q);
- `d.a % 3 = 2 && d.q = 0` (exhausted B source terminal);
- `d.a % 3 = 1 && d.p = 1` (already regular E terminal);
- `d.a % 3 = 1 && d.p = 0 && d.q % 3 = 0` (E-zero marker reduction through source theorem `Agent2MarkerTower.e_zero_q0_regular`).

`safeY3 c = terminalY3 ((normalizeWithCount c).2)`; the theorem `safeY3_source` composes the exact original-machine guarded path with the terminal source return, proving that **every accepted `c` with `c.a≥4` returns to physical regular section `L`**. `p2_fixed_safe` connects the fixed-tail `M(3k+4,Q,2;0 1^6)` to this criterion after `e_two_reset`. Lean [CI 45267284097](https://github.com/FlareZ123/bb6/actions/runs/45267284097) accepted all declarations, axioms only `[propext, Quot.sound]`.

**Unbounded 3-adic continuation, not just finite lookup:** [`Y3CylinderLift.lean`](Y3CylinderLift.lean) proves `lift_safe_seed`: for every (r,Q,t≥0), if `safeY3 ⟨8*r+5,0,2*Q+6⟩`, then the original physical machine started from `M(3*(r+3^(2*Q+7)*t)+4,Q,2;0 1^6)` returns to `L` in finite raw time. It uses the preexisting exact costed `Agent31PacketShift.source_path_shift`; the normalizer path count `n≤2Q+6` makes its final a-prefix lift divisible by 3, which preserves the terminal residue and pair-resource fields. **Lean CI [45267997767](https://github.com/FlareZ123/bb6/actions/runs/45267997767) succeeded**, with only `[propext,Quot.sound]`, no `sorryAx`.

For (Q=0), the reproducible exact-BigInt [`q0-census.js`](q0-census.js) classifies all (3^7=2187) residues: 1254 A, 759 B-zero, 57 E-zero with q divisible by 3, and 117 E-zero residuals with q congruent 1 or 2 mod 3 (90+27). Thus the **computationally enumerated 2070/2187** seed cylinders pass the *proved sufficient criterion*. The count itself is an integer-arithmetic census, **not a kernel-checked cardinality theorem**, and 117 rejected residues are unresolved, not proven nonreturning, much less halting. In particular this is a measure of a restricted artificial source packet family, not of BB(6) tables, genuine root visits, or decided machines. For the q-zero generated family, the 3-adic source lift is universal once a base residue is accepted.

Two additional disjoint **explicit exact** original-machine q-zero source cylinders were proved in [`P2K31Q0Source.lean`](P2K31Q0Source.lean): `k=81s+16` follows reset/E/B/E → E0(q=3)→L; `k=81s+31` follows reset/E/E/B → E0(q=3)→L. [Lean CI 45266668841](https://github.com/FlareZ123/bb6/actions/runs/45266668841) passed (standard axioms only). Separately, [`P2K7PhysicalReentry.lean`](P2K7PhysicalReentry.lean) assembles Agent 35's three previously source-proved k=27t+25 q-mod3 exact endpoint shapes into `all_k25_regular` and an optional physical `chain_k25_regular` prefix composition. Both new declarations individually compile and print `[propext,Quot.sound]` in [CI 45265241701](https://github.com/FlareZ123/bb6/actions/runs/45265241701); **that workflow's eventual failure is wholly later**, in unrelated `MarkerPairsTerminal.lean`, and does not discredit the successful targeted declaration checks.

**Second source expansion (same date):** [`YSafeNormalizer.lean`](YSafeNormalizer.lean) proves a depth-recursive original-machine Y-marker return test `safeY_source`, using a new unbounded positive-depth A/p0 original-source identity. [CI 45269697093](https://github.com/FlareZ123/bb6/actions/runs/45269697093) succeeded, standard axioms only. Independent exact primitive-time A/p2 terminals for Y2 and Y1 were proved in [`AY2P2Regular.lean`](AY2P2Regular.lean) (eight-symbol `11010111`, [CI 45270279122](https://github.com/FlareZ123/bb6/actions/runs/45270279122)) and [`AY1P2Regular.lean`](AY1P2Regular.lean) (six-symbol `110111`, [CI 45271137635](https://github.com/FlareZ123/bb6/actions/runs/45271137635)), with the final literal blank handled by `ObsEq`.

[`YPlusZClosure.lean`](YPlusZClosure.lean) then combines these terminals, the earlier Y3 arbitrary-p source theorem, Y-marker depth decrements at E/p0, and the **exact E/p2 Y-to-Z marker transform** `Agent2EAltPacketCompose.e_two_to_zero` followed by `Agent26ZSafePlus.safeZPlus_source`. The unified predicate `safeYPlus m c` is structurally recursive on Y-depth; the new theorem `safeYPlus_source` proves that every accepted Y packet physically reaches L. `p2_fixed_safeYPlus` attaches the original fixed-tail E/p2 source reset. **Full imported-source Lean CI [45271494674](https://github.com/FlareZ123/bb6/actions/runs/45271494674) succeeded**, no sorry/native-decision axiom.

An exploratory exact BigInt implementation of this expanded mixed grammar accepted all 2,187 **specific seeds** k=0..2186 at Q=0; this is *not* yet a theorem for all k congruent to these residues, nor a proof that all k are accepted: the same diagnostic detects a high-index residual at k=146779 (first exceptional Y3 E0q2 branch then Z4 E/p2 terminal with a%3=1, p=2). Treat it as an unresolved source-grammar input, not a machine halting configuration. The old `q0-census.js` still enumerates only the earlier `safeY3` criterion; it has not been silently repurposed to count mixed-grammar acceptance. Do not claim complete Q0 closure.

**New all-depth E/p2 Z terminal (23 November):** [`EZTwoK0BRegular.lean`](EZTwoK0BRegular.lean) proves a genuinely new universal **original-six-state source** two-macro return for every (t,q,m≥0) from prepared (M(3(3t)+4,q+1,2;Z_m)) to physical (L(8(8t+1)+9+2(q+1)+2,1,2m+5)). This uses Agent26's exact `e_two_Z_packet` followed by existing `b_zero_any`: after the first source step (8(3t)+5=3(8t+1)+2) is B with (q=0). The intermediate literal blank is transported with `source_chain`, not silently discarded. [Full source CI 45273483383](https://github.com/FlareZ123/bb6/actions/runs/45273483383) passed with the theorem and the complete derived synthetic witness before refactoring; [refactored modular CI 45273749004](https://github.com/FlareZ123/bb6/actions/runs/45273749004) also passed, standard axioms only.

[Exact source trace `P2Residual146779Source.lean`](P2Residual146779Source.lean) and [`P2Residual146779Closed.lean`](P2Residual146779Closed.lean) show the prior *synthetic* exceptional (k=146779,Q=0) packet (M(440341,0,2;0 1^6)) passes reset, four guarded B/E steps, Y3 E/p0→Y2, five guarded steps, Y2 E/p2→Z3, four guarded steps to (M(2879299338241,8,2;Z_3)), **then returns to regular L using the universal E/Z branch**, because (2879299338241=3(3·319922148693)+4). This was a rejected candidate of an earlier *sufficient* mixed grammar, not a machine halting counterexample; its closure demonstrates why rejection cannot be interpreted as nonreturn. The source exact path and the final composed return are accepted by [CI 45273749004](https://github.com/FlareZ123/bb6/actions/runs/45273749004).

[`ZSafeK0.lean`](ZSafeK0.lean) now extends Agent26's structurally recursive source-sound zero-marker packet classifier with precisely the new E/p2 (k≡0pmod3,,q>0) terminal branch. `safeZPlus_included` proves old predicate inclusion. `safeZK0_source` certifies every newly accepted marker depth, [CI 45273955154](https://github.com/FlareZ123/bb6/actions/runs/45273955154) SUCCESS. [`YPlusZK0.lean`](YPlusZK0.lean) carries this improvement back through the Y→Z source gate and its recursive Y marker descent, with `safeYPlusK0_source` and fixed-tail source wrapper; **[Original source CI 45274610908](https://github.com/FlareZ123/bb6/actions/runs/45274610908) SUCCESS** with only standard Lean axioms; the universally quantified `safeYPlusK0_source` and fixed-tail `p2_fixed_safeYPlusK0` compose the novel E/Z branch throughout nested Y/Z marker reductions. The `old_included` theorem preserves every case accepted by the old mixed grammar.

All statements concern prepared source configurations. They do not establish exact BB(6), any global nonhalting invariant for Cryptid D, or a source intersection with the certified halting prefix `0(10)^q1101101100y`. The new original-machine E/Z corridor and precise witness were sent to Agent 2 and Agent 37 root-language mailboxes on 23 November.

**Unified E/p2 zero-marker source criterion:** [`EZTwoQ0OrK0.lean`](EZTwoQ0OrK0.lean) combines the previous all-E-index (q=0) source theorem (our earlier `EZeroZTwoAll`) with the new all-positive-(q), (k≡0mod3) source theorem, to prove `all_q0_or_k0`: all prepared E/p2 Z-marker packets with (q=0) **or** (kmod3=0) reach physical regular L at some exact original-source finite time. This synthesizes two genuinely disjoint infinite directions of the source grammar, but says nothing about the complementary (q>0,kmod3≠0) cases or blank-root reachability. CI audit pending at time of documentation.

**Main missing step:** connect these source-admissible packet theorems to the actual Cryptid D blank-root regular-section orbit (or prove a global exclusion of halting). A source-sound accepted cylinder can coexist with a genuine blank-root excursion into a different exceptional suffix. The residual `E0(q%3=1,2)` marked-packet terminals suggest a precise new algebraic problem, but only root-connected or comprehensive closure would decide this machine.


**Research state: 8 November 2026.** New original-machine zero-marker packet theorems and a terminating depth-recursive safe language have been **kernel-certified** against the original six-state table in [manual Lean CI 42531370805](https://github.com/FlareZ123/bb6/actions/runs/42531370805). This is intermediate synthetic-section mathematics. The blank-root D machine remains undecided, so no exact BB(6) value or upper bound follows. [Earlier research log](FULL_RESEARCH_LOG.md).

## Section semantics and key theorem

The original machine is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Use `I_n(s)` for state F scanning 0, with a physically blank left half-tape and right tape `1^n s`; all finite trailing zeros are physically immaterial. Define
- `M(a,q,p;Y)=I_a((01)^q 0 1^pY)`, the packet section;
- `Z_m=(01)^m0`, the **zero-ended marker**;
- `L(A,Q,B)=I_A((01)^Q1^B)`, the regular section language.

The [exact original-source theorem `e_zero_drop_Z`](EZeroZ.lean) proves, for **every** `k,q,m∈ℕ`,

```text
run(12k²+49k+50+4q, M(3k+4,q,0;Z_(m+1)))
    = M(8k+5,0,2q+7;Z_m).
```

This is literal configuration equality, preserving both machine state and every binary tape cell. It uses the unchanged `CryptidBoundary.full_E_pairs` original source lemma, with `Z_(m+1)=0 1 Z_m`.

## New unbounded regular-reentry families

The same [Lean file](EZeroZ.lean) composes that exact drop with Agent2's original-source packet normalization, B boundary, and A/p=0 code interpreter. The resulting **physically observable** `ObsEq` regular-return statements are:

| Input source | Quantification | Subsequent physical endpoint |
|---|---|---|
| `M(3k+4,q,0;Z_0)` | every `k,q` | **exact** `L(8k+5,1,2q+5)` at time `12k²+49k+50+4q` |
| `M(3k+4,3u,0;Z_(m+1))` | every `k,u,m` | some regular `L`, via `p=2(3u)+7≡1 mod3` |
| `M(9t+4,q,0;Z_(m+1))` | every `t,q,m` | some regular `L`, because the dropped packet is a B section with `q=0` |
| `M(9t+10,3u+1,0;Z_(m+1))` | every `t,u,m` | some regular `L`, because the dropped packet is an A section with `p≡0 mod3` |
| `M(27t+7,3u+1,0;Z_(m+1))` | every `t,u,m` | some regular `L` after one further exact guarded E packet step and an A/p=0 terminal |

These are mutually overlapping sufficient families, not a complete classification. Every result is universally parameterized and checks the *literal original machine* via physical tape equivalence. All have been audited by [CI 42531370805](https://github.com/FlareZ123/bb6/actions/runs/42531370805), with no `sorryAx` or native-decision dependence.

## A certified recursive sufficient criterion

The stronger reusable [`ZSafeNormalizer.lean`](ZSafeNormalizer.lean) imports the original-source guarded B/E packet normalizer. Define `d=normalizeWithCount(c).2` for a packet index `c=(a,q,p)` with `a≥4`. The terminal is immediately *safe* when

```text
d.p % 3 = 1
or (d.a % 3 = 0 and d.p % 3 = 0)
or (d.a % 3 = 2 and d.q = 0).
```

For a remaining `d.a % 3 = 1, d.p = 0` terminal, zero-marker depth zero closes by the exact first row above. At positive depth, the theorem replaces the index by `(8*((d.a-4)/3)+5, 0, 2*d.q+7)` and decreases the marker depth by one. The recursive predicate `safeZ m c` is finite by **structural recursion on the marker depth**, while the inner packet normalizer is finite by the already source-proved rank decrease `q+p↦q+p−1`. Its fully audited soundness statement is:

```text
safeZ m c  and  c.a ≥ 4
    => exists T,A,Q,B:
       run(T, M(c.a,c.q,c.p;Z_m)) ≈ L(A,Q,B).
```

The theorem `e_zero_safeZ` also specializes this procedure to `M(3k+4,q,0;Z_(m+1))`. Furthermore, `zero_marker_all_safe_pmod` proves that **every** `M(a,q,p;Z_0)` with `a≥4` and `p%3≠2` returns physically to regular `L`, for arbitrary `q,p`. This closes the entire safe-residue depth-zero packet language, including any number of intermediate B/E returns, using only original source rules. All three compiler theorems passed [CI 42531370805](https://github.com/FlareZ123/bb6/actions/runs/42531370805). The method composes **whole unbounded packet paths** with arbitrary-many zero-marker reductions, rather than proving a new short congruence case for every 3-adic arithmetic residue. The computed predicate is a *sufficient* original-source certificate. A rejected input is unresolved; the procedure is not a halting or nonreturn decision.

In particular, `p≡2 mod3` A/E terminal exits and some deeper E-reset chains remain possible. Agent2's active Z-marker A/p=2 work is complementary. None of these synthetic tapes is asserted to be reached by any authentic blank orbit.

## Earlier first-return work and rooted frontier

[AExtraBranches.lean](AExtraBranches.lean) proves explicit A extra-10 and A-E-pairs rules by specializing Agent35's mixed-word source theorem; original-source [CI 41474006959](https://github.com/FlareZ123/bb6/actions/runs/41474006959) passed. [ASixBoundary.lean](ASixBoundary.lean) adds the six-one A gate, [CI 41475009756](https://github.com/FlareZ123/bb6/actions/runs/41475009756). [EZeroFirstComplete.lean](EZeroFirstComplete.lean) and [EZeroFirstChain.lean](EZeroFirstChain.lean) handle strict physical first-return questions on exceptional E marker inputs. These are source-level statements about explicit input cylinders.

[trace_four_starts.py](trace_four_starts.py) projects 30,000 symbolic return steps from each of four named original blank prefixes and records reproducible digests. Its long projected compositions have no global original-source Lean theorem. The actual-root effort elsewhere in the repository has reached difficult finite exceptional reentries but lacks a universal invariant covering all reachable branches. See [the full log](FULL_RESEARCH_LOG.md) for scope qualifications and exact trace provenance.

**Complementary packet-language priority:** Apply `safeZ` / `safeYPlusK0` only to packet sections that are first shown to be reachable from an authentic blank root, and repair any reachable unsafe A/E p=2 tail with an original-machine return theorem. Rejected sufficient-criterion inputs remain unresolved. This line should support, not replace, the root-level section-return and phase-band programme above.
