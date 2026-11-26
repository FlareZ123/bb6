# Raw56 E1=0RE: complete six-hole candidate (2026-11-26)

Parent Raw56: `1RB---_1RC---_0RD---_1LD1LE_------_------` (D1=1LE).
The root first undefined query is E1 at ordinary time 6. Four ordinary
choices 0LC, 0LD, 1LD, 1RD have immediate translated cycles; the other
20 are not assumed closed. The E1=0RE child has six holes and its first
undefined query is E0 at time 10.

## New discovery

Using the existing Agent7 Raw49 classifier at cap 1000, lookback 32,
depth 6, the E1=0RE child has 8,528 split nodes, 157,695 translated-cycle
leaves, 35,737 last-hole leaves and 2,713 initially open leaves. No aliases.
The longest query was 762 and longest detected cycle endpoint was 797.

All 2,713 open leaves now have explicit candidate nonhalting certificates:
- 2,666 exhaustive FAR candidates with at most five DFA states;
- 23 larger FAR candidates with up to eleven DFA states;
- 20 source-generated symbolic sweep families;
- four sparse n-gram fixed points (widths 5, 9, 9, 13).

The last symbolic case, leaf 2006
`1RB0LF_1RC0RB_0RD0RA_1LD1LE_1LF0RE_1LA---`,
has the exact zipper candidate
`A([], 1 (0101)^n 0101010101)`, entered at step 52.
A return adds three copies of 0101 with cost 100+16n. The generic
single-block discovery failed when the entire 12-bit increment was
opaque; using a 4-bit transferable block exposed the recurrence.
The generated sweep theorem checks arbitrary tails and induction.

The source-checked target is
`BB6.Agent1Raw56.Raw56E1RE.all_quotient` at WeightedBound 7014, and its
ordinary compatibility corollary. The underlying tree checks the
halt branch at every split, all ordinary successors, and the empty
canonical residual list. **Candidate complete; original-source Lean
acceptance pending.**

## First source-check diagnostic and repair

The first original-source attempt, [run 45882933157](https://github.com/FlareZ123/bb6/actions/runs/45882933157), reached Lean and failed in generated `Raw56E1REPart575.lean` with `OfNat Bool 1` (and consequent stuck `decide` checks). This is a serialization defect, not a counterexample to a certificate: the Agent7 C++ classifier writes cycle direction as integer `0/1`, while the inherited canonical emitter formatted that field with `str(t[3]).lower()`, producing Lean `1` instead of `true`.

`prepare.py` now validates that every cycle direction is exactly integer 0 or 1 and patches its private copy of `certify_canonical.py` to emit `str(bool(t[3])).lower()`. The pinned discovery-tree bytes, open-list digest, certificate data and checker semantics are unchanged. The candidate remains unaccepted until the existing manual workflow selector `raw56-e1-0re` passes on the repaired source. No Raw56 parent closure, global roster reduction or BB(6) upper bound is claimed. No Raw56 parent closure, roster decrement, or
BB(6) upper bound is asserted. The accepted global roster remains 60.

Reproduce with `python im-results/agent1-raw56/prepare.py`. The manifest
pins tree and open-list bytes, exhaustive FAR output, larger FAR
automata, exact pump indices and sparse fixed-point sizes. The
generator reuses Agent7/19/31/47's established certificate interfaces.
Generated Lean source is ephemeral. Compile its root
`im-results/agent1-raw56/generated/Raw56E1REAll.lean` via
`tools/lean_compile_closure.py` after the normal shared-core unpack and
sweep generation. Use the existing manual Raw57-sibling workflow selector
`raw56-e1-0re`; no new workflow file.

Next: kernel-check the complete child, then consume it through an
explicit Raw56 first-query frontier retaining every other open branch.
