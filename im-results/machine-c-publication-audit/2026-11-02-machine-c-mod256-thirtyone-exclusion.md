# Agent 29: Machine C reset index 31 modulo 256, symbolic exact exclusion

**Status: kernel-verified all-time theorem, independently source-compiled.**
This proves nonreachability of one infinite family of necessary Machine C halting reset gateways. The family was already excluded by Agent 41's finite-quotient experiment; the contribution is a complete source-checked symbolic inverse proof, eliminating reliance on the 18-million-state computational closure for this family. Machine C remains undecided. No new accepted global BB(6) bound is claimed.

## Exact theorem

The original six-state two-symbol machine is
`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`.
Agent 21 has already certified its published Cryptids accelerator against the raw Turing machine. The unchanged local `BB6CLine.nextC` begins from `(5,0,1)`, and `BB6CLine.Reach` denotes arbitrary finite blank-entry reachability.

Our theorem, compiled under precisely this unchanged reachability definition, is:

```lean
BB6.Agent29C31.reset_mod256_thirtyone_unreachable (t : Nat) :
  ¬BB6CLine.Reach (512*t+63,768*t+97,0)
```

This excludes all reset gateways `(2j+1,3j+4,0)` with `j=256t+31` and `t≥0`.

## Inverse calculation

The main reusable lemma `hub_cases` exhausts *all* reachable high-sector hub predecessors when `A≥5,C≥4`:

```text
Reach(A,2,C) implies at least one:
  even portal  Reach(0,k,C+3), k even, A=2k+2;
  odd portal   Reach(0,k,C+2), k odd,  A+2=2k+3;
  reset        Reach(A+3,k,0), C=2k.
```

It is derived by composing `reached_two_split`, `reached_one_high_or_reset`, and `reached_high_kzero_prev` from the original Agent 21 source, with no new assumptions. All three cases remain exhaustive at every depth.

The target reset first forces hub `(1280t+155,2,768t+95)`. Symbolic inverse expansion either contradicts divisibility/parity at a hub or reaches one of the forbidden reset families:

```text
Reach(1872t+220,88t+9,0)  => sum mod 4 = 1
Reach(552t+63,748t+87,0)  => sum mod 4 = 2.
```

Both second counters are odd and ≥5, so each contradicts the all-time invariant `reached_odd_zero_mod4_hole`, requiring sum mod 4 in `{0,3}`. The proof's entire finite branching is explicitly written as Lean named lemmas, not trusted to an external search algorithm or finite cutoff.

## Verification

- Full Lean source: `C31.lean.xz.b64`, decoded with `reconstruct.py` into `C31.lean`; uncompressed SHA-256:
  `dd79b36e6288787f2f83d3b3be40061323790735369e78c3d3be437594d154e6` (12,035 bytes).
- The reconstruction script checks the hash and writes atomically under a file lock.
- Manual-only CI workflow `.github/workflows/agent29-c31-mod256.yml` compiles complete **unmodified** sources `CLine.lean`, `CReachBridge.lean`, `CRange.lean`, `CBack.lean`, `CHubSplit.lean` before `C31.lean`. No mocks or temporary axioms are present.
- **Successful GitHub Actions verification:** [run 41409650653](https://github.com/FlareZ123/bb6/actions/runs/41409650653), SHA `bb86bf2d196c32d08d199ac668616aafdd933498`; final axiom report:
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.
- The original-machine semantic bridge was separately established by Agent 21 in [run 41389979481](https://github.com/FlareZ123/bb6/actions/runs/41389979481). Our theorem directly uses its exact local counter map.

## Scope

This is a genuine infinite-family *formal proof*, rather than a new quotient-excluded class. It strengthens certificate portability and demonstrates a reusable three-way inverse hub rule. Many reset and side-gateway classes survive. Full Machine C nonhalting and BB(6) are open.
