# TM63 counted source macros and root-prefix candidates

**Scope.** This dossier collects original-table TM63 counted sweeps, the S1 binary-decrement/drain interface, and root-connected reset-prefix candidates. It does not establish that TM63 halts, a complete primitive-step score, or a universal six-state upper bound. All uncompiled compositions remain in `im-results/`.

## Strongest established components

### Original-machine counted sweeps

`CountedSweep.lean` proves `counted_left_sweep` and `counted_right_sweep` for the original TM63 transition table and the repository's infinite-tape `BB6Coverage.run` semantics. The theorems quantify over arbitrary tapes and preserve the complete tape outside the swept interval. The source workflow passed in [CI 42735925396](https://github.com/FlareZ123/bb6/actions/runs/42735925396); its axiom audits contain no `sorryAx`.

The local physical micro-branches are also source-certified:
- `CountedOddUnary.lean`: `counted_odd_counter`, cost `48+12*c`, for the valuation-zero local decrement pattern and arbitrary right-unary counter, with arbitrary exterior tape. [CI 42739466365](https://github.com/FlareZ123/bb6/actions/runs/42739466365); axiom audit excludes `sorryAx`.
- `CountedOneZeroUnary.lean`: the one-trailing-zero branch, cost `60+12*c`, also for an arbitrary right-unary counter. [CI 42740367928](https://github.com/FlareZ123/bb6/actions/runs/42740367928).

These are local physical templates, not yet the all-parameter S1 decrement theorem.

### Binary carry-pattern arithmetic

`CountPattern.lean` proves the carry-pattern identities and the closed form
[
\operatorname{drainPattern}(b)+12b+48
=6\cdot4^b+42\cdot2^b.
]
The theorem `BB6ChampionArithmetic.drainPattern_closed` is kernel-checked with axiom set `[propext, Quot.sound]`. This is arithmetic about the proposed sequence of valuations; it does not by itself prove that the TM63 source run realizes that sequence.

## Main source proof candidates

### Parity-complete S1 decrement

`S1CountedInc0.lean` proposes the uniform source theorem `s1Config_counted_decrement`: for every positive encoded counter `z<2^a`, the original machine decrements `z` to `z-1`, increments the unary counter `b) to `b+1`, and takes
[
48+12v_2(z)+12b
]
successful transitions.

The proof combines the source-certified valuation-zero odd branch with the existing positive-valuation carry-prefix/suffix branch. The theorem and its exported `#print axioms` gates are present, but the complete repository import closure has not passed compilation. Earlier local interface harnesses used deliberately axiomatized imported source interfaces; they are not a source-closure proof.

### All-ones S1 drain

`S1CountedDrain.lean` instantiates the generic CountedReset drain using the parity-complete S1 decrement candidate. Its intended theorem is
[
\operatorname{run}\ tm2\ (\operatorname{drainCost}(2^k-1,c))\
\quad(\operatorname{s1Config}\ L\ n\ m\ a\ (2^k-1)\ c\ h)\
=\operatorname{some}(\operatorname{s1Config}\ L\ n\ m\ a\ 0\ (c+2^k-1)\ h).
]
For `c=0`, the proposed exact cost is
[
6\cdot4^k+42\cdot2^k-12k-48.
]
The source module, the generic prefix-then-drain adapters, and their axiom gates are present, but the complete original-import workflow has not yet passed. Treat the drain as a proof candidate until the full transitive audit succeeds.

### Conditional champion adapter

`S1ChampionCountedReset.lean` specializes the terminal composition interface and removes its generic `hInc0` premise, conditional on a genuine blank-root run and a source reset-prefix run. It does not prove either machine-specific run. Its local interface checks used stubs; the repository source closure still needs its manual workflow and `sorryAx` audit.

## Authentic-root reset-prefix candidates

The initial root itself is established separately: [`RootSourceBridge.lean`](../agent48-root-witness/RootSourceBridge.lean) kernel-checks the original-machine run of 27,959 moves from blank to `s1Config 3 7 2 6 0 63 29`, with a full infinite-tape embedding and no `sorryAx`. That theorem is only the initial prefix.

The following later compositions remain candidates:

| Module | Intended source transition | Current evidence boundary |
| --- | --- | --- |
| `TM63RootQ4Drain.lean` | Compose the 27,959-move root witness, the 332-move q4 prefix, and the 63-bit all-ones drain. The candidate endpoint is `s1Config 3 6 1 71 0 (2^63-1) 223`; the candidate successful-move count is `6*4^63 + 42*2^63 + 27487`. | The complete original-import composition and transitive axiom audit have not passed. This is not a halt proof or an attained BB(6) lower bound. |
| `M1EvenQ4Prefix.lean`, `M1EvenQ4Suffix.lean`, `TM63M1EvenRootComposition.lean` | The next `(m,n)=(1,6)` reset row, followed by the counted drain, to `(m,n)=(0,5)`. | The old focused CI run 43397674787 failed before downstream suffix modules. Subsequent source repairs have not passed a fresh complete compile/axiom audit. |
| `M2EvenSixQ4Prefix.lean`, `M2EvenResidueSix.lean` | For every admissible `n=16k+6`, prove the `m=2` reset prefix to `m=1,n=16k+5`, with counter `2^b-1` ready for the counted drain. | The old targeted run 43659498187 predates the current repairs. The base finite-boundary/index repairs are at commit `58906b7b7a45ea7c309ec61996c5163ce3238e03`; the lifted residue-six boundary repairs are at `88754f3885817f13924aa68459d3e98384a29bc9`. Neither current file has passed compilation. Agent 42 owns the leaf acceptance check; do not edit these files concurrently. |
| `M0EvenFourQ4Bridge.lean`, `M0EvenResidueFour-bridge-candidate.md` | The next row after the proposed middle-11 endpoint: `m=0,n=16r+4 → m=2,n=16r+3`, with the general residue parameter `n=8k+4`. | The 51-step finite bridge and base-input match are now present as Lean drafts. They have not been compiled, lifted to arbitrary `L,k`, composed with the M0-specific q4 suffix/drain, or integrated into the root theorem. |

For the M2 residue-six row, the current theorem `m2Even_residue6_q4_reset_prefix_source` has endpoint
`S1(L,16k+5,1,a+b+2,2^b-1,0,h+5+3b)`
and prefix cost `83+12a+3b`. Composing the generic all-ones drain would yield
`S1(L,16k+5,1,a+b+2,0,2^b-1,h+5+3b)`.
This exact counted/root composition is not yet kernel-checked. The next root row is `m=1,n=8q+5` with `q=2k`; Agent 24 owns the existing M1-odd prefix mechanism.

## Critical unresolved obligations

1. Pass the full original-import Lean 4.36.0-rc2 compile and transitive `sorryAx` audit for `S1CountedInc0.lean` and `S1CountedDrain.lean`.
2. Validate the current M0 residue-seven and Rst1Prime/Bridge8 dependency closures. The first Rst1' instance is wired into the root source path, but the post-patch Bridge8→Bridge30 chain still needs its source/axiom gate.
3. Validate the M2 residue-six leaf, then compose its prefix with the counted drain and the authentic root endpoint; validate the M1 residue-five successor.
4. Prove the M0-even residue-four source row described above, then append it to the root countdown. The present 51-step bridge is not yet a general source theorem.
5. Prove the original-machine primitive-step count for the entire halting itinerary, including the final halting-query convention. Independently, prove a universal six-state upper bound.

The Coq macro formulas and the arithmetic score candidate are not substitutes for these original-source run proofs. No exact BB(6) value, complete champion halt certificate, or global maximality theorem is claimed here.

## Historical material

The former chronological dossier is preserved at [`history/README-chronology-20261115.md`](history/README-chronology-20261115.md). Use it for detailed derivations and superseded attempts.
