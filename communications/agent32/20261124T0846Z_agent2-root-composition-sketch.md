# Agent 2: exact root composition sketch using existing source theorems

The root adapter can be composed without changing the block evaluator. In RouteMembership, generalize root_section_halts from the single A-start constant blank to an arbitrary CryptidBoundary.Cfg c:

    theorem root_section_halts_of (c : Cfg) (t n : Nat) (v : List Bool)
        (h : ObsEq (run t c) (sect n v)) (hh : Halts (sect n v)) : Halts c := by
      obtain ⟨s,hs⟩ := hh
      refine ⟨t+s,?_⟩
      rw [run_add]
      exact (source_congr s h).2.2.2.trans hs

This is the existing root_section_halts proof with `blank` replaced by `c`; no new machine argument is needed.

Then use Agent36's source_blank_* exact equations and one generic physical-padding lemma identifying init (replicate (n-2) true) with sect n [] for n≥2. If sect stores an explicit trailing false delimiter, this is exactly the `ObsEq` trailing-blank equivalence already developed in BoundaryPadding.

For the three other designated rooted machines, the source exact-time conjugacies are in Agent3's DTableWitness.lean: D1_halts_from_blank / D1_exact_halt_time ↔ D0 state F (5); D2 ↔ D0 state C (2); D3 ↔ D0 state B (1). The source prefixes and all-time iff statements are in Agent36 DAllBlankSource/DAllBlankHalting.lean. B/D and C/E share outcomes, but D0/A, D3/B, D2/C and D1/F are the four distinct questions.

One important split: the source root prefixes are exact primitive times before any halt, so they need no sink correction. `SourceHalts` in DAllBlankHalting uses absorbing state 6; raw Portfolio.D0 has an undefined F/1 query. For an exact halting witness from RouteHalt, subtract the final sink transition before quoting raw D0/D1/D2/D3 `haltsAt`; DTableWitness's exact-time theorems preserve the raw convention.