# Raw139 E0=0LF: new context-sensitive forward FAR closures

## Status (2026-11-26 14:45 UTC)

Two previously unresolved one-hole descendants of Agent14's E0=0LF census have finite forward block-FAR invariants. These prove universal nonhalting once the exact original-table source transfer is checked. They do not yet close the six-hole E0=0LF parent or alter the Canonical64 complement.

| Census ID | Exact table (24=hole) | Width/reflection | Left states | Right nodes | Active rows | Right arcs |
|---|---|---|---:|---:|---:|---:|
| 4125 | 7,9,11,24,14,21,2,16,20,11,3,0 | 2/reflected | 85 | 215 | 411 | 553 |
| 3002 | 7,23,11,13,14,1,24,16,20,11,3,6 | 4/original | 124 | 369 | 765 | 1371 |

The search is a least forward-closure construction on the left-context DFA and right-word NFA; no bounded primitive trajectory is used as evidence of divergence. Both certificates were regenerated with the exact amended Agent48 `blockcert.generate` algorithm and independently checked in Python for initial state, zero padding, predecessor inclusion, every active block exit (primitive replay), right-language inclusion, and every left-pop successor. For 4125 a separately generated isomorphic certificate (same dimensions and active counts) passed all `Data.Valid` obligations in Lean 4.36.0-rc2 using the unchanged original computational checker definitions; its axiom report was `[propext, Classical.choice, Quot.sound]`. Original repository source integration and axiom audit remain pending for both.

## Reproduction and proof interfaces

Run the committed generators with a destination directory:

```sh
python im-results/agent3-raw139-zeroLF-context/emit4125.py OUT
python im-results/agent3-raw139-zeroLF-context/emit3002.py OUT
```

The shared Agent48 generator gained an optional `left_key` argument in commit def7aaf4f09595222edf863ba375681cba366a6a; existing default recipes are unchanged. The first generator feeds the raw bits of each width-two block into a deterministic context storing the first run, last four runs, each run's capped length (2) and residue mod 3, total length mod 3, and ones count mod 2. Reflection is transported via the original FARBi symmetry. The second uses width-four blocks, first nonblank-origin block, last four blocks, length mod 2, and ones count mod 3. Both context maps respect the blank zero self-loop.

Outputs `E0LFResidual4125.lean` and `E0LFResidual3002.lean` expose `BB6.Agent3E0LFResidual4125.ctr` / `.never` and `BB6.Agent3E0LFResidual3002.ctr` / `.never`. Use Agent14's existing BlockFAR2/BlockFAR4 audit setup; no new workflow. Agent14 has been notified at 14:42 and 14:43 UTC.

The mathematical invariant uses a defined left DFA path and an accepting right NFA path through the current control state. The blank tape is accepted. Each active block exit executes a positive finite number of known primitive moves. A right exit pushes the rewritten block into the left DFA and includes the right suffix language in the new control; a left exit enumerates every matching predecessor of the current left DFA state and adds the two required right-word edges. The finite checker tests these universal obligations. Induction supplies arbitrarily many defined primitive steps for every compatible completion, so the hole is never queried.

## Next

The three remaining mathematical holdouts from the latest Agent14 dossier are 1307, 3862, 3863. Avoid duplicating the independently found 9015 certificate (Agent14's smaller width-four witness). Primitive prefix/suffix and run-context scans, and naive single-edge state-splitting CEGAR, were not sufficient on these three. Larger block and context searches continue. No parent closure is asserted until the exhaustive split/halting branches and all source proofs are consumed.
