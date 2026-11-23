# Raw TM62-to-D0 coordinate audit

**Status:** locally kernel-checked semantic preflight. This is not yet the final imported Mathlib bridge, and it is not a new blank-root halting theorem.

## Conclusion

The proposed absolute-coordinate map has the correct sign and orientation:

`absTape(T,h)(i) = decodeSymbol (T.nth (i-h))`.

For an external right move, Mathlib gives `(T.move Dir.right).nth i = T.nth (i+1)`; taking `h' = h+1` preserves the absolute cell coordinate. For a left move, `(T.move Dir.left).nth i = T.nth (i-1)`; taking `h' = h-1` does the same. The external TM writes before moving, and `Tape.write_nth` shows that only the old head cell changes. Thus the new absolute tape is exactly `updateTape absTape h (decodeSymbol w)`.

The checked file proves, for the exact eleven live transitions and F/1 halt case:

- `table_conjugate`: the external A–F / S0–S1 table maps to the repository's six-state D0 table;
- `absTape_write_move`: the coordinate equation for both directions and the write-before-move convention;
- `absStep_commute`: the one-step commuting square, including `none` at F/1;
- `run_transport`: finite runs commute at the **same n**;
- `haltsAt_transport`: exact-`n` halting is preserved in both directions;
- `halts_transport`: existential halting is preserved;
- `absCfg_AEmptyAt`: the abstract A(n,[]) section maps to the D0 pure-unary F-section at the same absolute head coordinate.

The exact-time transport does not add a step in the six-state D0 semantics. The extra +1 applies only if the terminal F/1 configuration is represented by the separate frozen sink state in CryptidBoundary.

## What is still needed for the actual upstream source

The checked model uses a relative tape observation `Int → ExtSymbol`. The actual external source uses `Turing.Tape Symbol`. The remaining adapter is small and is directly supported by the pinned Mathlib lemmas:

- `Tape.write_nth`: observation of `T.write w` is `relWrite (observe T) w`;
- `Tape.move_left_nth`: observation after a left move is `relMove .left`;
- `Tape.move_right_nth`: observation after a right move is `relMove .right`.

Here `observe T i := T.nth i`. The external `TM.step` writes the new symbol and then calls `Tape.move`, so the adapter must preserve that order. The external `A(n,[])` definition should then be shown to have relative observation `j ↦ if 0 < j ∧ j ≤ n then S1 else S0`, using the ListBlank nth/append lemmas. Do not describe the current file as having compiled those Mathlib adapter lemmas.

## Reproducible pins

The original source citation in the Agent32 bridge note is:

- proofs commit `1929f57df4dd7afcc11c3f458e20526fd1f991e0` (2025-08-23), Lean `4.22.0-rc4`, Mathlib `713ead03620c1f6965f94050048e50e8d1878872`, original theorem-file blob `3bdada95ae94bd1198c16bb3d32dfe724c59579c`.

The CI-compatible upstream snapshot already used by the repository's manual workflow is:

- proofs commit `b77dda5c79fb196d67ce35669e172ad632401c1b` (2026-10-20), Lean `4.36.0-rc1`;
- Mathlib commit `dfbc15ea6605db241da9cfd0632bbaf69b67e513`;
- theorem-file blob `973efd0efef1a415b58c49930d1f1a3233c75f49`;
- Mathlib Tape file blob `87c9df7aea22fe00eba77d179cc8449e6e04ac9d`.

I compared the external TM table, A definition, `reach_9_nil`, and the full `halts_A_mod_3_pow_108` declaration/proof between the two source snapshots: those extracted sections are byte-for-byte identical. The Mathlib 4.36 snapshot retains the same `Tape.move_left_nth`, `Tape.move_right_nth`, and `Tape.write_nth` statements, under the moved path `Mathlib/Computability/TuringMachine/Tape.lean`. Prefer the b77/dfbc15 snapshot for the repository's Lean 4.36 CI reproduction; the old 1929/713ead source is not the compatible CI pin.

## Local check and axiom profile

Compiled locally with Lean 4.36.0-rc2 using:

```sh
lean im-results/agent4-cryptid-d0-review/HeadRelativeFunctionAudit.lean
```

The printed axiom profiles contain no `sorryAx`. The checked transport theorems depend only on the standard `propext` and quotient soundness machinery; the section equality additionally reports `Classical.choice` from the local arithmetic/decision procedure. This is an abstract semantic preflight, not an axiom audit of the full upstream proof.

## Scope boundary

The upstream theorem proves halting from `A(3^108*k + C, [])`, where `C = 1975700577069254261393123959451562008800234946348086`. It does not prove that the authentic blank orbit reaches this cylinder. The separate `reach_9_nil` result reaches `A(9,[])`; the authentic-root hit problem remains open. This audit only removes the raw-step semantic translation as a source of uncertainty.


---

## Authentic-root reachability and A-section bridge

The external @-d Lean development proves that the cylinder `A(C+3^108*k, [])` halts for every natural k, with `C=1975700577069254261393123959451562008800234946348086`. The unresolved question is whether the authentic blank-root orbit reaches this or another certified halting cylinder. The repository's concrete Mathlib `TM62`-to-D0 adapter remains uncompiled; the separate abstract `HeadRelativeFunctionAudit.lean` is a checked semantic model, not a substitute for that adapter.

### Root section at index 31,777

`Root13Shadow.md` and `Root13Section.lean` record the strongest current local connection to the external cylinder. In the DRegular arithmetic model, authentic-root section index 31,777 is `L(a,0,0)` with:

- `(a-C) mod 3^14 = 3^13`;
- `p=(a-C)/3^13` satisfies `p mod 2187 = 205`;
- `a mod 3^20 = 2863782241`;
- `a` has 44,970 bits.

`Root13Section.lean` extracts the 4,484-step prefix from `Agent25SixthRoot.seed` and attempts to source-certify the section, its exact residue, and its ten-step link to the sixth exceptional input. **That file is still uncompiled.** The separate `First10AffineBridge.lean` arithmetic theorem was locally checked with Lean 4.36.0-rc2; this does not validate the root-section extraction.

The first ten external A-macro suffixes are canonical DRegular states. The root's corresponding sections at indices 31,777 through 31,787 have a descending exact 3-adic shadow, with valuations 13 through 3. The raw replay then matches external macros 11–13 (arguments 35,21,5; branches E,E,B; exact output suffixes), reducing the parameter-difference valuation to 2,1,0 before diverging at macro 14. Root-specific raw prefixes m=23 and m=26 then return to suffix `(01)^3 11`. This suffix also occurs at external prefix j=2, but the later root reentry at index 31,792 is not in that cylinder: its parameter is 0 mod 3, while external `C_2=14049426325825808081017770378322218729246115174030817` is 2 mod 3 (`v3` difference 0).

The endpoint `(32768*v+28577,3,2)` is not a new unverified q4 result: Agent 36's original-source checked `five_return` and `blank_sixth_reentry` theorems already certify the sixth q4 input's return to exactly this state (CI [41753103349](https://github.com/FlareZ123/bb6/actions/runs/41753103349) and [42139587484](https://github.com/FlareZ123/bb6/actions/runs/42139587484)). The alternative `BlankSixthQ4Rejoin.sixth_q4_root_rejoin_original` was not accepted; its audit was cancelled. The macro-by-macro replay remains computational, but the physical q4-to-q3,b2 endpoint is source-certified.

### Finite comparison with the halting cylinders

`root20_suffix_cylinder_screen.mjs` compares 82,605 modeled DRegular sections and explicit reentry endpoints through episode 20 with all canonical states among the first eleven external A-macro prefixes. For each external prefix j=0,...,10, the unique largest `v3(a-C_j)` occurs at root index `31777+j` and equals `13-j`; no state is an exact lift `C_j+3^(108-j)*8^j*k` for natural k.

The same screen tests Agent 32's extended final-tail suffix candidates `(q,b)=(1,0),(1,1),(3,1),(4,1)`. None reaches even the necessary modulus `a ≡ C (mod 3^10)` in the modeled section set. A `(4,0)` state at index 27,282 is a separate 11-adic near miss, but `(4,0)` is not among the checked final-tail classes. The scan is finite and excludes intermediate primitive configurations inside exceptional packets; it is not an all-time nonreachability theorem.

### Other intermediate work and next priorities

- `AZeroOneFirstReturn.lean` is now compiled against the pinned original `CryptidBoundary` source in the 23 November A/B first-return audit (CI [45125434133](https://github.com/FlareZ123/bb6/actions/runs/45125434133)); its unary and low-A interfaces are used by `UnaryFirstReturnComplete.lean`.
- `HeadRelativeFunctionAudit.lean` proves the abstract whole-tape coordinate conjugacy, exact-n run transport, and halting equivalence. The concrete Mathlib tape adapter and transitive axiom audit remain open.
- The local Lean 4.36.0-rc2 toolchain is now available; the local repository checkout remains blocked by shell DNS resolution for `github.com`. The Root13 section and two-return source composition are now verified in pinned CI [45130375240](https://github.com/FlareZ123/bb6/actions/runs/45130375240) and [45131667374](https://github.com/FlareZ123/bb6/actions/runs/45131667374). The highest-value remaining bridge is the concrete pinned TM62/Mathlib adapter and continuation of the authentic root beyond the current nineteenth exception. Avoid larger blind arithmetic scans and do not promote finite exclusions to all-time claims.

All of this work remains intermediate. `results/` is unchanged; no exact BB(6) value or universal upper bound has been established.

## Verified low-E first physical return, including canonical blank padding (23 November 2026)

The all-parameter original D-start machine E-on-zero low row has now been **kernel checked** against the restored original `CryptidBoundary` transition table.  Its physically blank-left F/0 section is defined using the half-tape equivalence `TapeEq c.l []`, not the representation-sensitive equality `c.l=[]`.  For every `k,q≥0` the canonical source input

```text
I_(3k+4)((01)^q)
= init (replicate (3k+2) true ++ oppairs q)
```

has **no positive physical F/0 return** at any `0<t<T`, where `T=12k²+49k+50+4q`.  The source endpoint at exactly `T` is provided by Agent31's preexisting `DRegularELow.e_zero_suffix`, modulo physically irrelevant tape padding. Taken together, these are the exact one-return clock and no-earlier-physical-return properties needed for the low-E row of the root grammar; they do **not** imply global nonhalting or a BB(6) upper bound.

The proof is in [ELowPhysicalFirstReturnRepair.lean](ELowPhysicalFirstReturnRepair.lean) and [ELowCanonicalBlankFirst.lean](ELowCanonicalBlankFirst.lean), using [BoundaryPadding](../agent32-cryptid-padding/BoundaryPadding.lean). The first file proves `ePairs_first_physical` and `full_E_pairs_first_physical` for explicitly padded inputs. The second file proves the stronger `canonical_E_low_no_early_blank` for the original implicit-blank source, via a mathematical predicate invariant under `ObsEq`.

**Decisive correction:** `PairsFirstReturn.cBase_noF` from Agent2's draft was *mathematically false* (and failed CI on 21 November). The four-step C/1 close encounters state F at time two, but its left half-tape still contains a one. Our checked lemma `cBase_internal_F` establishes this for every parameter, and our corrected proof forbids only **physical** first returns in that bridge. The machine-wide experimental regression [low_e_physical_trace.mjs](low_e_physical_trace.mjs) checks 169 low-E inputs and 13 internal C-base cases independently. This regression is corroboration, not a universal proof.

The CI is [45111455597](https://github.com/FlareZ123/bb6/actions/runs/45111455597) (canonical input theorem, **success**, original Lean 4.36.0-rc2); the earlier explicit-padding source theorem is [45111145554](https://github.com/FlareZ123/bb6/actions/runs/45111145554) (**success**). The printed axiom profiles contain only `propext` and `Quot.sound`, **no `sorryAx`**, for the final source first-return theorems.

This closes an important intermediate proof gap. The implicit right-padding quotient is essential; a bare `IsPhysicalReturn` predicate based on literal `l=[]` is too representation-specific to transfer through `BoundaryPadding.source_init_pad`.



## Canonical DRegular first-return partition (23 November 2026)

The Critic's E-zero/E-one-zero coverage objection is resolved by a source-level partition. Write the canonical language as
`L(a,q,b)=I_a((01)^q1^b)`, with `a≥2` and `q=0 ⇒ b=0`; the three arithmetic residues are `a=3k+2` (B), `a=3k+3` (A), and `a=3k+4` (E). The existing `BB6.ERemaining.source_contract` supplies the exact original-source `ObsEq` endpoint for every successful `DRegular.next` branch (all eleven rows; original-source CI [41712102615](https://github.com/FlareZ123/bb6/actions/runs/41712102615)). The following independent strict-return theorems fill the no-earlier-physical-F/0 side:

| Canonical branch | Source first-return coverage |
| --- | --- |
| A, `q=0,b=0` | `BB6.Agent4UnaryFirstReturnComplete.unary_source_first_return` |
| A, `q>0`, any `b` | `BB6.Agent4ACanonicalAllFirst.all_A_positive_first`; internally covers all three `b mod 3` tails |
| B, `q=0,b=0` | `BB6.Agent4UnaryFirstReturnComplete.unary_source_first_return` |
| B, `q>0`, any `b` | `BB6.Agent4BCanonicalAllFirst.all_B_first`; internally covers all three `b mod 3` tails |
| E, `q=0,b=0` | `unary_source_first_return`, using the canonical low-E no-early-blank theorem |
| E, `q>0,b=0` | `BB6.CryptidELowCanonicalFirst.canonical_E_low_no_early_blank`, with endpoint from `ERemaining.source_contract` |
| E, `q>0,b≥2` | `BB6.CryptidETriplePairsFirstReturn.full_E_triple_pairs_noF`, with `ys=replicate (b-2) true` and endpoint from `ERemaining.source_contract` |
| E, `q>0,b=1` | `BB6.EExceptionalFirstPhysical.source_exception_first_physical`: a separately handled physical F/0 packet; `DRegular.next` exits the regular language here rather than returning a successor |

The E-low source input is exactly `sourceSection ⟨3k+4,q,0⟩ = init (replicate (3k+2) true ++ oppairs q)`, so it covers both the pure E-zero case and the q-positive one-pair/zero-tail case without a guessed conversion to `EZeroFirst` or `EOneZeroFullFirst`. The theorem is formulated with `TapeEq c.l []`, so its first-return predicate survives observational blank-padding equivalence.

For E-triple, the identity
`oppairs (q+1) ++ replicate b true = false :: (pairs q ++ [true,true,true] ++ replicate (b-2) true)`
for `b≥2` puts the canonical source input directly into the E-triple first-return family. The new `full_E_triple_pairs_noF` theorem exposes the stronger fact already available in the boundary proof: **no state-F visit at all** occurs in the open interval, not merely no literal-empty-left return.

The A/B/unary/low-E source closure compiled successfully in pinned Lean 4.36.0-rc2 CI [45125434133](https://github.com/FlareZ123/bb6/actions/runs/45125434133); the strengthened E-triple no-F theorem compiled in the exact-source E-triple audit [45125832960](https://github.com/FlareZ123/bb6/actions/runs/45125832960). The E-exception theorem compiled cleanly in [45125992109](https://github.com/FlareZ123/bb6/actions/runs/45125992109); that overall run failed only at the new Root13 canonicality proof. Run [45130375240](https://github.com/FlareZ123/bb6/actions/runs/45130375240) compiled `Root13Section` and its authentic source lift cleanly (no `sorryAx`). The namespace correction in `Root13TwoReturn` was then verified by the successful full-composition run [45131667374](https://github.com/FlareZ123/bb6/actions/runs/45131667374), which also enforces the workflow's forbidden-axiom gate.

This is a complete first-return *coverage map* for the canonical DRegular language plus its one E-exception packet. It is not a proof that the blank root never halts, nor a BB(6) upper bound. The finite cylinder screen above has not been extended.
