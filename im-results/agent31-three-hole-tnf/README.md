# Complete three-hole weighted TNF subtree

Authentic first-eight-hole ancestor of Agent50's two-hole pilot: `1RB---_1RC1LF_0RD0RB_1LD1RE_---0LB_---0LA`. F0 is queried after 21 ordinary steps; all six live states have appeared. The three holes are A1, E0 and F0. The explicit certificate covers every ordinary child and halt sibling, hence 25³ = 15,625 compatible table completions.

Kernel-certified exact weighted threshold: **92**, attained by F0=1RA, A1=0LF, E0=halt after 91 ordinary moves plus final halt. No unchecked search cutoff is used as a verdict.

| Witness | Nodes |
|---|---:|
| Full expansions | 15 |
| Last-hole closures | 148 |
| Side-cycle nonhalt | 179 |
| Explicit FAR nonhalt | 19 |

Two independent finite enumerators agree on 1,123 halting and 14,502 nonhalting completions. The counts are auxiliary computational statistics, not the statement of the Lean theorem. The 19 residual growing-tape leaves were solved using Agent7's finite-automata reduction saturation, DFA sizes 1–9 and both orientations. Each DFA, NFA mask and zero mask is explicit; the checker verifies the invariant rules without relying on search heuristics.

## Files and verification

- `ThreeHoleAudit.lean`: reusable structural audit checker for arbitrary cut-six TNF parents. Converts explicit data to the existing `WeightedTNFCertificate`; checks all possible incoming blank delays.
- `ThreeHoleData.lean`: explicit full 361-node tree, authenticated parent path, exact upper and lower threshold.
- Manual `agent13-coverage.yml` target `weighted-tnf-three-hole` compiles the exact source closure and rejects placeholder/native-decision axioms. [Run 45409018102](https://github.com/FlareZ123/bb6/actions/runs/45409018102) succeeded: the exact source-closure check step completed successfully on Lean 4.36.0-rc2, including the axiom guard. Local Lean is installed, but GitHub DNS is blocked, so the original dependency closure is checked in CI.

This strictly enlarges the prior 625-completion pilot and is one local component of a future global TNF upper bound. It is not an exact BB(6) determination.

## Four-hole weighted subtree (accepted 2026-11-24)

The same authentic path, stopped one edge earlier, gives the four-hole parent
`wideParent = pathEnd root 2 (path.take 7)`. Its unassigned rows are A1, C1,
E0 and F0. The next first hole is C1 at 11 ordinary moves. Expanding all 24
ordinary C1 instructions and charging the C1=halt sibling yields a complete
weighted TNF certificate for all (25^4 = 390,625) compatible completions.

The deterministic generator `generate_four_hole.py` creates
`FourHoleBase.lean`, the 24 `FourHoleKid00..23.lean` modules and
`FourHoleData.lean`. Its finite classifier only proposes certificate
constructors; Lean checks every generated branch through `ThreeHoleAudit.check`.
The generator asserts the exact audit census:

| Constructor | Count |
|---|---:|
| Full first-hole expansions | 285 |
| Weighted last-hole leaves | 2,757 |
| Exact translated side-cycle leaves | 3,670 |
| Explicit FAR automata leaves | 120 |
| Reused universal pump leaves | 9 |

The generated theorem `BB6.Agent31FourHole.exact_weighted_threshold` proves
that the least uniform weighted bound for this parent is **395**. An explicit
compatible completion halts after 394 ordinary moves, and the final halt query
is counted in the weighted score. The upper direction is the recursively
checked TNF tree; the lower direction is the concrete halting completion.

**Original-source Lean acceptance:** existing manual workflow
`.github/workflows/agent13-coverage.yml`, target
`weighted-tnf-four-hole`, run
[45454698835](https://github.com/FlareZ123/bb6/actions/runs/45454698835),
completed successfully on Lean 4.36.0-rc2. The run executed both deterministic
generators, compiled the complete generated dependency closure, and passed the
fail-hard `sorryAx|native_decide` guard.

This is a stronger local certificate than the three-hole subtree above: it
closes the entire C1 expansion one first-hole edge earlier, including the
three-hole continuation as one of its 24 children. It is nevertheless only a
subtree below the authentic firstOneCylinder root. The seven-edge path's
off-path siblings, and the other root branches, are not covered by this
certificate. It does not determine BB(6).


## Rooted 124-residual frontier

The four-hole certificate is now connected to the authentic `firstOneCylinder` root by two additional Lean modules:

- `FourHoleRootFrontier.lean` constructs a seven-expansion rooted frontier. Every off-path ordinary instruction is retained as an explicit residual cylinder, and the entire continuation below `path.take 7` is closed by the four-hole certificate. The formal theorems `rootFrontier_sound` and `rootFrontier_openLeaves_disjoint` establish coverage and pairwise incompatibility of distinct residual cylinders.
- `FourHoleResidualRoster.lean` applies 37 individually checked finite nonhalting witnesses to the 161 off-path leaves. The resulting roster has exactly **124 residual cylinders**.

The central theorem is:

```lean
remainingRootRoster_sound :
  ∀ m, compatible root m →
    WeightedBound 395 m ∨
      ∃ e ∈ remainingRootRoster, compatible e.2 m
```

The count is checked by `remainingRootRoster_count : remainingRootRoster.length = 124`. The witness checks include finite ray, lasso, side-cycle, and alternating-sweep certificates. The depth-eight and depth-nine continuation under the seven-edge parent is handled wholesale by the four-hole certificate, rather than retaining its 46 descendant residual occurrences. A separate theorem, `remainingRootRoster_sound_7014`, monotonically lifts this frontier to the broader 7014 weighted first-one interface.

This is a different partition from the existing 141-residual, bound-92 pilot roster: it trades a larger local bound (395 instead of 92) for 17 fewer residual cylinders. Since 395 is below the broader 7014 weighted first-one interface used elsewhere in the repository, this is a useful alternative frontier for subsequent composition. It is **not** a global BB(6) upper bound: the 124 residual cylinders still require resolution.

**Verification:** GitHub Actions run [45461345794](https://github.com/FlareZ123/bb6/actions/runs/45461345794) passed with Lean 4.36.0-rc2, compiling `FourHoleData.lean`, `FourHoleRootFrontier.lean`, and `FourHoleResidualRoster.lean` through the repository's source-closure checker. Follow-up run [45462016810](https://github.com/FlareZ123/bb6/actions/runs/45462016810) also passed after adding the `WeightedBound 7014` lift theorem.
