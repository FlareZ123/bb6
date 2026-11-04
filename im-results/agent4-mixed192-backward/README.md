# Machine C mixed-192 source-certified backward cores and terminal gates

**Scientific status, 2026-11-04:** Both arithmetic reverse cores and all four terminal residue exclusions have now passed Lean 4.36.0-rc2 checks against the **unchanged checked-in Machine C CLine source**. A new theorem excludes 504 distinct second-halting parameter pairs modulo 192. The entire Machine C blank orbit and BB(6) remain undecided. These results stay in `im-results/` pending independent novelty review.

## Validated proof chain and theorem scope

The original accelerated blank root is `BB6CLine.Reach (5,0,1)`. For all natural `a,k`, the following source-root counter states `(a,k,0)` are mathematically unreachable whenever `(a mod192,k mod192)` equals one of

| Source core | Terminal congruence | Source theorem |
| --- | --- | --- |
| A | (35,61) | `A4Backward192.source_no_35_61` |
| A | (131,157) | `A4Backward192.source_no_131_157` |
| B | (83,13) | `A4Backward192B.source_no_83_13` |
| B | (179,109) | `A4Backward192B.source_no_179_109` |

Core A's complete all-natural backward-step closure and original-source reachability transport passed [CI 41725820375](https://github.com/FlareZ123/bb6/actions/runs/41725820375). Core B's distinct all-natural arithmetic proof in [BackwardMod192B.lean](./BackwardMod192B.lean), split without replacing proof bodies into eight source-preserving compilation modules by [agent4_split_mixed192b.py](../../tools/agent4_split_mixed192b.py), and its [SourceBridge192B.lean](./SourceBridge192B.lean) reachability transport passed [CI 41753352264](https://github.com/FlareZ123/bb6/actions/runs/41753352264). Each companion terminal is proved through the original-source, uniquely forced `c=3` predecessor, using Agent46's previously verified `reach_c0_two_parent`. No unproven enlarged-core closure is assumed.

The true second stopping-family equation from Agent15 is

```text
a = 2*j+3
k+j+3*m+5 = 2^(2*m+2)*(j+3)
```

For every `m>=2`, the power has residue 64 modulo 192. The module [StopBridge192AB.lean](./StopBridge192AB.lean) converts the four forbidden terminal cells into eight explicit `(j mod192,m mod64)` parameter conditions, with theorem names `first_core_stops` and `second_core_stops`. Both passed source [CI 41754012415](https://github.com/FlareZ123/bb6/actions/runs/41754012415).

A stronger two-core gate argument lifts each terminal input `(2*j+3,k,0)`, where `k>=4`, to its uniquely forced source ancestor `(2*j+3,k-3,3)`. [WideStop.lean](./WideStop.lean) then proves that every stopping parameter `j%12=4,m%8=4` lies in at least one excluded high-sector core. The all-natural theorem `A4Mixed192Wide.second_stop_j4_mod12_m4_mod8_excluded` passed [original-source CI 41754571383](https://github.com/FlareZ123/bb6/actions/runs/41754571383).

Finally, [SideStop.lean](./SideStop.lean) combines two further all-depth high-core sectors and the eight terminal conditions. The final **source-certified theorem** is `A4Mixed192Side.second_stop_504_mod192_excluded`: for all `j,m,k:Nat` with `m>=2`, the exact stopping equation and any of the following **disjoint** parameter conditions imply `¬BB6CLine.Reach (2*j+3,k,0)`:

| Parameter condition | Count of pairs `(j,m) mod192` |
| --- | ---: |
| `j%12=4, m%8=4` | 384 |
| `j%48=43, m%16=11` | 48 |
| `j%48=19, m%16=3` | 48 |
| `(j%192,m%64)` in `{(16,58),(112,26),(64,10),(160,42)}` | 12 |
| `(j%192,m%64)` in `{(40,2),(136,34),(88,18),(184,50)}` | 12 |

Total: **504 of 36,864** parameter residue pairs, exactly **7/512**. The independent [residue_audit.py](./residue_audit.py) exhaustively checks that the five-way parameter partition equals membership in the two source-core predicates at the forced `c=3` ancestor, for all 192 by 192 residue pairs. This finite arithmetic audit supplements, and does not replace, the universally quantified Lean proof. Final [CI 41754885154](https://github.com/FlareZ123/bb6/actions/runs/41754885154) passed on the unchanged original checked-in CLine source, and the theorem axiom audit shows only `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

**Provenance boundary:** This is a genuine blank-root all-time claim about the checked-in `BB6CLine` acceleration. Agent4's separate [upstream source bridge](../agent4-mixed96-backward/SourceUpstreamBridge.lean) was independently original-Cryptids-source checked in [CI 41696303681](https://github.com/FlareZ123/bb6/actions/runs/41696303681); it transports upstream accelerated reachability into this source. The current 504-family proof has not itself been compiled as a combined upstream-raw-machine theorem. Some eliminated parameter examples were present in older source-certified B8/M32 quotient abstractions, but a larger computational B8/M512 quotient was already reported to exclude them, so *external novelty is not established*. No complete first-family exclusion, Machine C nonhalting proof, universal BB(6) bound or exact BB(6) value follows.

## Historical experimental account and finite evidence

## Proposed mathematical statement

Use the *unchanged* original counter transition BB6CLine.nextC from im-results/agent11-c-line/CLine.lean and its actual initial triple (5,0,1). Four proposed blank-unreachable terminal residue cylinders are

- A: (a mod 192, k mod 192, c) = (35,61,0), (131,157,0)
- B: (a mod 192, k mod 192, c) = (83,13,0), (179,109,0).

Each core has seven low-counter congruence families and high-sector arithmetic clauses in BackwardMod192.lean and BackwardMod192B.lean. The currently authored Lean low predicates name one singleton residue pair per core; the exhaustive checker separately verifies a strictly stronger version including both companion pairs. Those enlarged predicates require an updated Lean source theorem, so do not infer companion cylinder certification from the current draft Lean file.

For c=0 or 1, define w=k+c. The proposed enlarged core A low predicate contains coupled special pairs (a%192,w%192)=(35,61) or (131,157) and seven (a%96,w%48) pairs:

  (0,25), (10,19), (34,7), (46,4), (48,1), (58,43), (82,31).

Core B has coupled special pairs (83,13) and (179,109), and seven (a%96,w%48) pairs:

  (10,43), (24,37), (34,31), (46,28), (58,19), (72,13), (82,7).

For c>=2, set d=(a-c)%96 and t=(a+k)%192. High A is the disjunction of

  (d,t%48) in {(7,26),(8,27),(17,33),(31,38),(32,39),
  (43,47),(45,46),(55,2),(56,3),(65,9),(79,14),
  (80,15),(86,21),(93,22)}

or (d=32,t=93) or (d=35,t%96=45).
High B is the disjunction of

  (d,t%48) in {(7,2),(8,3),(17,9),(21,10),(31,14),
  (32,15),(38,21),(43,23),(55,26),(56,27),
  (65,33),(69,34),(79,38),(80,39)}

or (d=80,t=93) or (d=83,t%96=45).

Both enlarged sets contain 11,444 of the 192*192*98 projected triples. Both omit the actual root (5,0,1). Exact reverse closure should prove that their complements contain every finite-time blank-entry state.

## Exact, independently reproducible finite check

The self-contained C++17 checker check_core.cpp reproduces the nine cases of the original map, then tests all **28,459,008 representative transitions**. The quotient is

  q(a,k,c)=(a%192,k%192,c) for c<2,
  q(a,k,c)=(a%192,k%192,2+(c-2)%96) for c>=2.

For each abstract state (a0,k0,c0), the checker enumerates a in {a0,a0+192}, k in {k0,k0+192}, and c in {c0} for c0<2 or {c0,c0+96} for c0>=2. For each actual transition from one of these representatives, it checks the contrapositive closure: if the successor belongs to the proposed bad set, the predecessor belongs too. It checks four variants: A/B, original singleton special pair or enlarged two-pair version. The observed output for each variant was PASS with 28,459,008 edges and rootBad=0; counts are 11,442 abstract bad states in the original singleton version, 11,444 in the enlarged version. The checker is deterministic and uses no finite orbit cutoff.

**Why representative enumeration should lift to all naturals:** All low/high bad clauses depend solely on q. The original transition tests exact exceptional counters 0/1/2/3, parity, and affine expressions whose quotient residues are determined by a,k modulo 192 and high c modulo 96. For residues 0/1 in a and 0 in k, taking both the small representative and one +192 representative covers the exceptional-vs-positive branch. For c residues 2/3/4, both c0 and c0+96 cover boundary-to-low versus remaining-high successors. For every larger real input, the transition's quotient successor therefore coincides with one of these checked representatives. A formal Lean proof of this soundness or an all-natural symbolic backward-closure theorem is still required before calling the result kernel certified.

The author independently simulated 12 million bounded concrete triples per singleton variant, and 6 million additional triples per enlarged version, finding no violation. Those sampled screens are secondary checks; the exhaustive finite representative graph is the primary computational evidence.

## Halting-equation intersection and comparison with earlier work

Agent15's exact immediate second stopping condition has a=2j+3 and

  k+j+3m+5=2^(2m+2)*(j+3).

For m>=2, 2^(2m+2)%192=64. Each of the four candidate terminal cylinders therefore corresponds to six residue pairs (j,m) modulo192, totaling 24. An independent B8/M16/M32/M64/M128/M256/M512 and mixed96 census found five illustrative residue pairs

  (j,m)%192=(16,122),(112,154),(88,146),(136,162),(160,170)

whose targets are absent in mixed192 while *present* in B8/M256 and B8/M32. B8/M512 also excludes them computationally; its 52,736,417-state closure was independently externally computed by Agent41 but has not been fully certified within Lean's kernel. Relative to full prior source mathematics, novelty of the proposed congruences remains to be reviewed. Agent47's valid 96-modulus C/D inverse proofs were already subsumed by fully kernel-certified B8/M32 and are **not** claimed as new here.

## Verification work and immediate next step

The Lean drafts BackwardMod192.lean and BackwardMod192B.lean reuse the existing Agent4 exact counter interpreter and attempt all-natural backwards-closure via Presburger arithmetic. Source provenance is the prior Lean-checked A4Backward.nextC_source_equal bridge to *unmodified* CLine. The manual .github/workflows/agent4-machine-c-backward.yml builds from unmodified sources. The first monolithic CI attempt 41720094304 received a runner shutdown, and the second run 41720917299 was canceled after prolonged arithmetic proof execution. A source-preserving five-module decomposition is provided by tools/agent4_split_mixed192.py, and the subsequent CI should identify the individual difficult lemma. A successful final build must independently recheck the full source, prove the enlarged four-target theorem, and audit final axioms for the absence of sorryAx or added assumptions.

No change to results/ is appropriate before the proof is validated and novelty externally assessed. This investigation has not resolved the actual Machine C halting behavior or determined BB(6).
