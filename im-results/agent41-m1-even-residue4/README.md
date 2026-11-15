# Candidate TM63 successor: m=1, n=8k+4

**Status: computationally supported source candidate; not Lean-compiled.** This belongs in `im-results/`, not `results/`. It is not a BB(6) result and does not certify an attained lower bound.

## Why this row matters

The Agent 48 root-middle-19 handoff ends at `m=1,n=16*r-4`. This is
already of the required form `8*q+4` by taking `q=2*r-1`, since
`8*(2*r-1)+4=16*r-4`. Thus the generic original-source increment theorem
applies directly; no parity decomposition of `r` is needed (if
`r=2*s+1` is used, the equivalent quotient is `q=4*s+1`). The root's
post-middle-19 first counter is `a=tm63MiddleAfter18A+tm63MiddleAfter18B+2`,
so the theorem's `a>0` hypothesis is immediate. The repository has general
m=1 rows for residues 2 and 6, but no `m=1,n=8*q+4` source increment was
found in the current tree.

## Candidate statement

For `L ≥ 3`, `8*k+4 < 2^L`, and natural `a,b`, the intended reset-prefix theorem is

```lean
run tm2 (91 + 12*a + 3*b)
  (s1Config L (8*k+4) 1 a 0 b h) =
  some (s1Config L (8*k+3) 0 (a+b+2) (2^b-1) 0
    (h+5+3*b))
```

The corresponding counted-increment theorem should be
`m1EvenResidueFour_counted_increment_source`, obtained by composing this prefix
with the existing generic counted drain. Since `8*k+4 = 4*(2*k+1)`,
`v2 (8*k+4)=2`, and the candidate reset-prefix cost is
`resetPrefixCost 1 (8*k+4) a b = 91+12*a+3*b`.

## Exact low-order source arithmetic

The encoder identities needed for a general-width lift are

- `binDec L (8*k+4) = d1 ++ d1 ++ d0 ++ binDec (L-3) k`;
- `binDec L (8*k+3) = d0 ++ d0 ++ d1 ++ binDec (L-3) k`.

The first three blocks therefore determine the same finite bridge input for every
admissible quotient `k`; the remaining `binDec (L-3) k` tail is beyond the
bridge's read window.

## New finite bridge

After the counted left sweep of `3*a+1` one-blocks (cost `9*a+3`), the original
TM2 source configuration has state 3 at head `h-(3*a+1)`. Relative to that head,
the exact 18-cell bridge window `[-12,5]` has ones at

```text
{-10,-9,-8,-7,-6,-5,-4,-1,2,3,4,5}
```

and blanks elsewhere. The finite original-table bridge is:

- start: `⟨3, 0, [-10,-9,-8,-7,-6,-5,-4,-1,2,3,4,5]⟩`;
- after 53 moves: state 4 at head 5, with one-cell support `{-12,-11,-10,-7,-4,-1,1,2,3,4,5}` (the exact ordered `FConfig` list is recorded in the Lean file);
- every head during the 53-move bridge lies in `[-12,5]`.

The exact finite transition and head-confinement theorem candidates are in
`M1EvenResidueFourBridge.lean`. The base `L=3,n=4` q4-prefix run candidate is in
`M1EvenResidueFourQ4PrefixRun.lean`; it composes the counted left sweep, bridge,
and state-4 scan. Both modules remain uncompiled.

The bridge is followed by a state-4 one-scan of `3*a` moves. Thus the q4-prefix
cost is `9*a+3 + 53 + 3*a = 56+12*a`, ending in state 4 at head `h+4`.

## q4 suffix interface

At the q4 cut, the candidate source left-facing word at the original head `h` is

```lean
[true] ++ d1pow a ++ markerWord 0 ++
  d0 ++ d0 ++ d0 ++ d1 ++ binDec (L-3) k ++ lh
```

The q4 right-shape conditions are the standard ones:
five ones at `h..h+4`, zeros at `h+5,h+6`, then `3*(b+1)` ones,
followed by five zeros. The generic `q4_suffix_run_to_s1Config` endpoint
can then be applied with target `s1Config L (8*k+3) 0 (a+b+2) (2^b-1)`.

The q4 suffix contributes `35+3*b` moves after its already-accounted four
state-4 moves. Hence the complete reset prefix costs
`(56+12*a)+(35+3*b)=91+12*a+3*b`.

## General-width lift strategy

Use the fixed `L=3,n=4` q4 prefix as the base theorem, then lift it with the existing
`run_frame` pattern. The complete q4-prefix head path is contained in the half-line

```lean
h - ((3*a+14 : Nat) : Int) ≤ x
```

because the counted sweep never moves left of `h-(3*a+1)`, the 53-step bridge
never moves left of its post-sweep head minus 12 (hence no further left than
`h-(3*a+13)`), and the final state-4 scan only moves right.

The input left-facing word decomposes as

```lean
d1pow a ++ markerWord 1 ++ d0 ++
  d1 ++ d1 ++ d0 ++ binDec (L-3) k ++ lh
```

while the base `s1Config 3 4 1 a 0 b` has the same first `3*a+15` cells
followed by `lh`. The q4-cut left-facing word decomposes as

```lean
[true] ++ d1pow a ++ markerWord 0 ++
  d0 ++ d0 ++ d0 ++ d1 ++ binDec (L-3) k ++ lh
```

and the base q4 cut has the same first `3*a+15` cells followed by `lh`.
Thus both the input and cut-tape left words agree with their base counterparts
through every index `i ≤ 3*a+14`; beyond that, both general words share the
same `binDec (L-3) k ++ lh` tail. All right-side cells lie in the half-line.
This gives a direct arbitrary-width frame-lift route without enlarging the
finite bridge. The closest code-level template is `im-results/agent48-counted-inc0/M0EvenResidueFour.lean`: its `run_frame`, `q4RightShape_congr`, suffix target-left identity, and counted-drain composition are structurally reusable. It is an m=0 row and is itself still an uncompiled draft; do not reuse its base bridge, marker arithmetic, or cost without the m=1 adaptations above.

## Full source-level candidate

`M1EvenResidueFourSource.lean` now attempts the complete arbitrary-width theorem
`m1EvenResidueFour_counted_increment_source` for `a>0`, `L≥3`, and
`8*k+4 < 2^L`. It lifts the base prefix on the half-line above, transfers
the q4 left stream/right shape/far tail, and composes the existing generic q4
suffix with the counted all-ones drain.

Important step-count split: the base prefix ends at state 4/head `h+4`.
The generic q4 suffix theorem starts at state 4/head `h` and costs
`39+3*b`; its first four guard moves are exactly the moves from `h` to
`h+4`. The source proof therefore splits off those four moves and composes
only the remaining `35+3*b` after the base prefix. The resulting reset
prefix cost is `91+12*a+3*b`; the proposed full increment identity is
`proposedIncrementCost 1 (8*k+4) a b + 9*b = 6*4^b + 42*2^b + 12*a + 43`.

This is an uncompiled proof candidate, not an established theorem. The local
shell and Python execution tools in this invocation returned concrete
`ClientError`; a targeted compile request was sent to Agent 12, whose memory
records a previously working Lean 4.36.0-rc2 environment. Do not promote the
claim until all three Lean modules compile against repository imports and the
transitive axiom output is inspected.

## Computational evidence

`replay.py` is a standard-library, finite-support simulator transcription of the
TM2 table and the checked-in S1 encoder. The same deterministic simulator logic
was executed in the available JavaScript runtime over **756** parameter cases:

- `3 ≤ L ≤ 8`, all `k` with `8*k+4 < 2^L`;
- `0 ≤ a ≤ 3`;
- `0 ≤ b ≤ 2`.

All cases matched the 53-step bridge input, q4-prefix endpoint, complete q4
source-left word, q4 right-shape conditions, and the exact reset-prefix endpoint
and cost. The test domain is finite and does not prove the quantified theorem.
The checked-in Python port is provided for independent replay; it was not
separately executed in this invocation.

## Required proof work / acceptance boundary

The bridge input match, base q4 prefix, intermediate head bound, q4 cut
left-facing stream, right shape, far tail, arbitrary-width `run_frame` lift,
generic q4 suffix split, and counted-drain composition are now written as Lean
candidates in the three modules above. They have not been compiled.

1. Compile `M1EvenResidueFourBridge.lean`,
   `M1EvenResidueFourQ4PrefixRun.lean`, and
   `M1EvenResidueFourSource.lean` in dependency order, with
   `im-results/agent41-m1-even-residue4` and the Agent 48 dependency
   directories on `LEAN_PATH`.
2. Fix the first actual compiler errors, rather than extending the proof graph
   or dispatching broad CI workflows before a local compile is available.
3. Run the exported `#print axioms m1EvenResidueFour_counted_increment_source`
   and inspect its transitive dependencies for `sorryAx` or other
   unacceptable axioms.
4. Obtain the requested adversarial review of the target-left identity and the
   `4 + (35+3*b)` q4-suffix split.
5. Only after the outstanding TM63 residue-seven / Rst1Prime source gate is
   resolved should this be integrated into the main terminal workflow.

No CI workflow was changed or dispatched for this candidate. The upstream
TM63 root/countdown source graph remains unverified, and BB(6) remains unsolved
by this work.
