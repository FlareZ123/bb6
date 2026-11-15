# Candidate TM63 successor: m=1, n=8k+4

**Status: computationally supported source candidate; not Lean-compiled.** This belongs in `im-results/`, not `results/`. It is not a BB(6) result and does not certify an attained lower bound.

## Why this row matters

The current Agent 48 root-middle-19 handoff identifies the next genuine-root state as
`m=1, n=16*r-4=32*k+12=8*(4*k+1)+4`. Thus a general original-source increment for
`m=1, n=8q+4` would close the next explicit TM63 root successor by specializing
`q=4*k+1`. The repository has general m=1 rows for residues 2 and 6, but no
`m=1,n=8q+4` source increment was found in the current tree.

## Candidate statement

For `L ≥ 3`, `8*k+4 < 2^L`, and natural `a,b`, the intended reset-prefix theorem is

```lean
run tm2 (91 + 12*a + 3*b)
  (s1Config L (8*k+4) 1 a 0 b h) =
  some (s1Config L (8*k+3) 0 (a+b+2) (2^b-1) 0
    (h+5+3*b))
```

The corresponding counted-increment theorem should be
`m1Even_residue4_counted_increment_source`, obtained by composing this prefix
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

The exact finite transition is recorded as a `decide` theorem candidate in
`M1EvenResidueFourBridge.lean`.

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
finite bridge.

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

1. Compile `M1EvenResidueFourBridge.lean` against the unchanged repository
   `ChampionRootBridge` and confirm the bridge/head-confinement declarations
   have no `sorryAx`.
2. Formalize the exact post-sweep frame match on `[-12,5]`, including the
   three-block `binDec` decomposition and all `a,b,h` parameters.
3. Lift the 53-step bridge; prove the `3*a` state-4 scan, q4 left word,
   right shape, and far-tail obligations.
4. Compose the existing generic q4 suffix and counted drain, then audit
   transitive axioms for the exported counted-increment theorem.
5. Only after the outstanding TM63 residue-seven / Rst1Prime source gate is
   resolved should this be integrated into the main terminal workflow.

No CI workflow was changed or dispatched for this candidate. The upstream
TM63 root/countdown source graph remains unverified, and BB(6) remains unsolved
by this work.
