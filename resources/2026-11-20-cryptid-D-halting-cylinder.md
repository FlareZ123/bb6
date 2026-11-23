# Cryptid D: formal halting cylinder and unresolved blank-root reachability

**Retrieved:** 2026-11-20  
**Machine:** `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`  
**Normalized start:** `A(9, [])` in the @-d high-level notation.

## Exact external formal results

Two independent Lean formalizations are relevant:

1. [Google DeepMind, `cryptids`, commit `3647718b5df22e1a61462dec0376bd204526285a`](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/Accelerations/M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean) proves `HasStackReduction` for this exact machine. The file identifies it as machine #85 restarted from state D and mirrored, transports #85's closed pair-stack system, and proves a seven-raw-step blank-tape entry into that system. This is a closed-system reduction, **not** a proof that the machine halts or does not halt.
2. [@-d, `int-y1/proofs`, current adapter pin `b77dda5c79fb196d67ce35669e172ad632401c1b`](https://github.com/int-y1/proofs/blob/b77dda5c79fb196d67ce35669e172ad632401c1b/BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.lean) directly defines the exact six-state transition table in a separate `TM62` semantics. It proves:
   - `reach_9_nil : c₀ ⊢* A 9 []` (36 raw steps);
   - `halts_A_mod_3_pow_108 (k : Nat)`: every `A(3^108*k + C, [])` halts, where
     `C = 1975700577069254261393123959451562008800234946348086`.

   This b77 snapshot is the CI-compatible pin used by the repository adapter: its `lake-manifest.json` pins Mathlib `dfbc15ea6605db241da9cfd0632bbaf69b67e513` and Lean 4.36.0-rc1. The earlier `1929f57df4dd7afcc11c3f458e20526fd1f991e0` snapshot used Lean 4.22.0-rc4; Agent 4 compared the transition table, `A` definition, `reach_9_nil`, and the complete `halts_A_mod_3_pow_108` declaration/proof between the two snapshots and found those relevant sections byte-for-byte identical. Use b77/dfbc for the concrete adapter's dependency closure.

Thus the *halting cylinder itself* is formally proved in an independent Lean development, and the repository now has an accepted exact transport into its own D0 semantics. The adapter `TM62MathlibD0Adapter.lean` compiled in [CI run 45174638945](https://github.com/FlareZ123/bb6/actions/runs/45174638945), proving `BB6.CryptidD0Bridge.D0_halts_on_A_cylinder` with exact primitive-step preservation and transitive axiom profile `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or `native_decide` was detected. The pinned dependency closure is the b77 source and dfbc15 Mathlib revision above. This still does **not** establish that the blank-root orbit reaches the cylinder.

## Explicit 108-step branch word

The BusyBeaverWiki analysis by @-d gives the following E/B branch word of length 108:

`EEBBEBEEBEEEBBEBBEEBBEBEEBBEBBEEEBBEBBEBBEEBBEEEBBEBEEEBBEBBEEBBEBEEBBEBBEEEBBEBBEBBEEBBEBEEBBEBBEEEBBEBBEBE`

It contains 53 E and 55 B symbols. Its corresponding residue class is the `A(3^108*k+C, [])` cylinder above. The word is a concrete halting route, not a proof that the blank-root orbit follows it.

Primary community analysis: [BusyBeaverWiki #85 / #490 page](https://wiki.bbchallenge.org/wiki/1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA). The page records that:
- #490 is the D-start normalized machine and starts at `A(9, "")`;
- @-d's BFS over roughly 235,000 suffix words found the length-108 E/B path;
- the open question is whether the orbit from `A(9, "")` reaches `A(3^108*k+C, ""));
- a simulation through 2,728,570 A-states did not complete the path; its closest reported attempt matched 21 of 108 letters.

These simulation counts and the estimated expected halting time (roughly (10^{10^{38.1}}) raw steps) are **empirical/heuristic**, not formal bounds or a halting proof. The page also reports many possible length-108 paths, but the cited Lean theorem above certifies the one residue cylinder it states; do not silently promote the broader path count to a formal theorem.

## Consequence for this repository

The D objective should be framed as a **halting-reachability problem**, not as a presumed all-time nonhalting problem. The existing source-certified DRegular sections and exceptional reentries remain useful finite-prefix machinery, but their value is measured by whether they can be connected to the high-level `A(n,r)` orbit and ultimately to a halting cylinder.

The initial configuration correspondence is already present. `DRegularSource.sourceSection` is `init (List.replicate (a-2) true ++ oppairs q ++ List.replicate b true)`; the source definition explicitly notes that `init` supplies two leading unary bits. `BlankRegular8394.source_seed` proves `sourceSection (9,0,0) = init (List.replicate 7 true)`, so the physical section has nine consecutive ones and matches the external `A(9, [])` configuration after the Bool/S0-S1 symbol encoding. The external `reach_9_nil` proves the same normalized blank prefix in its own semantics, while `CryptidBoundary.blank36` and `BlankRegular8394` establish the repository's corresponding source section. A substantial transition-level result is also already proved on the canonical regular suffix language. For `s=⟨a,q,b⟩`, the suffix is `r=(01)^q1^b`; `DRegular.Canon s` requires `q>0 ∨ b=0`, so `r` is empty or begins with 0, exactly the side condition in the wiki's `A(n,r)` notation. `DRegularShift.run_shift` proves that if a `k`-step DRegular run succeeds from `s`, then the same `k`-step itinerary succeeds from the `3^k*p` lift and the endpoint is shifted by `8^k*p`. The model theorem also synchronizes first exits. `DRegularSourceShift.lifted_original_run` and `paired_original_run` transport successful runs to the original machine. These results were locally/CI verified with only standard axioms: DRegular shift, run [41872704046](https://github.com/FlareZ123/bb6/actions/runs/41872704046); source shift, run [41872968993](https://github.com/FlareZ123/bb6/actions/runs/41872968993); underlying eleven-row source contract, run [41712102615](https://github.com/FlareZ123/bb6/actions/runs/41712102615). The new `ARegular3AdicBridge.lean` wrapper exposes this theorem in explicit `ASection(n,r)` notation, but the wrapper itself is not yet preflighted.

This establishes the same affine 3-adic shift pattern for DRegular source-certified section paths on the canonical regular suffix family, not for arbitrary suffixes or all exceptional exits. It is the natural regular-language analogue of the wiki's suggested A(n,r) shift law, but the exact first-return identification of `DRegular.duration` with the external A-macro is not asserted by these theorems. The remaining task is to extend the synchronization/source-return mechanism across arbitrary evolving `r` (or prove the 108-step target is covered by the regular family plus existing exceptional reentries), establish the macro correspondence where needed, and then prove the orbit-hit theorem. The [target-C DRegular probe](../im-results/agent2-root-language-exit/halting-cylinder-DRegular-probe.md) records the exact first two external A-macro checkpoints: the first ten land on `L(D1,4,1)`, while the next ten produce the nonregular suffix `01011101010111`; the q=4 E/E source closure is a later return, not the next A-macro step. Do not confuse start-state identification or a local source-path shift law with full dynamics equivalence or eventual halting.

Highest-value next work:
1. Treat the raw TM62-to-D0 transport and the 36-step blank-prefix theorem as closed dependencies; do not spend further work on rechecking the same initial-state or tape-coordinate correspondence.
2. Prove a source-exact transition/preimage relationship between the authentic root trajectory and the external `A(n,r)` cylinder, especially across arbitrary suffixes and exceptional reentries.
3. Use the existing DRegular 3-adic shift and root-return theorems to determine whether the root reaches the certified cylinder or another halting set.
4. If reachability fails, establish a genuine all-time invariant excluding every applicable halting class. The 2.7-million-state scan and 21/108 match remain empirical only; they cannot prove eventual avoidance or reachability.

This result concerns one BB(6) holdout and does not determine the global Busy Beaver value.
