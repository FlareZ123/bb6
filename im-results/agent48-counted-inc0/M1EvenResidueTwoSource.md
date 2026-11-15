# M1-even residue-two source increment

**Status: written Lean source candidate; not compiled or axiom-audited.** This is an original-table source-run theorem candidate, not a certified BB(6) lower-bound extension.

## Exact statements

For (3\le L), (8k+2<2^L), and (a>0), `M1EvenResidueTwoSource.lean` states:

```lean
m1Even_residue2_q4_prefix_source :
  run tm2 (44+12*a) (s1Config L (8*k+2) 1 a 0 b h) =
    some ⟨4,h+4,m1EvenResidueTwoCutTape L k a b h⟩

m1Even_residue2_reset_prefix_source :
  run tm2 (79+12*a+3*b) (s1Config L (8*k+2) 1 a 0 b h) =
    some (s1Config L (8*k+1) 0 (a+b+2) (2^b-1) 0 (h+5+3*b))

m1Even_residue2_counted_increment_source :
  run tm2 (proposedIncrementCost 1 (8*k+2) a b)
    (s1Config L (8*k+2) 1 a 0 b h) =
    some (s1Config L (8*k+1) 0 (a+b+2) 0 (2^b-1) (h+5+3*b))
```

The last theorem composes the q4 reset prefix with the existing geometric all-ones drain. The first two are stated without the positivity condition on `a`; the full counted increment requires `0<a` for the drain bound.

## Proof reduction

The useful reduction is that the existing 41-step (m=1,n=6) q4 bridge already works for the (n=8k+2) source. Its head/read window is ([-9,4]). The source tape for (n=8k+2) and the base (L=3,n=6) source agree on the entire half-line
[
x\ge h-(3a+1)-9.
]
Indeed, after the common prefix `d1pow a ++ markerWord 1 ++ d0`, the two low-order words begin `d1 ++ d0`; their third low block is outside the sharp left reach of the 44+12a prefix. The public `m1Even_q4_prefix_head_bound` confines every intermediate head to this half-line.

Consequently `run_frame` lifts the already-written base n=6 prefix, preserving the actual n=8k+2 source on the unread left tail. The output tape equals `m1EvenQ4CutTape` on and to the right of the original head, so the existing `q4RightShape` and infinite blank-tail lemmas apply unchanged. The left-facing stream is proved by:
- equality with the base n=6 output through the five read bits of the common third-block boundary;
- equality of the n=8k+2 input and n=8k+1 target streams beyond that boundary.

The existing q4 suffix then gives the exact n=8k+1 marker-zero successor, and `s1Config_reset_prefix_then_counted_drain` supplies the counted drain.

This avoids needing the new 40-step residue-two bridge for the source theorem. That finite bridge remains an independent trace in `im-results/agent8-m1-even-residue-two/`; it is not imported here.

## Shared-source repair and CI placement

To make the lift reusable, `M1EvenResidueSix.lean` now exports `m1Even_q4_prefix_head_bound`. During reuse I also corrected its `m1EvenResidueSix_cut_eq_base` helper: the premise is the actual `Inside = true` predicate, not `h ≤ x` (the old left-facing application at `h-i` could not prove the latter for positive `i`). The right-shape and far-tail callers derive the inside predicate from their coordinate bounds.

The manual-only `.github/workflows/agent42-champion-terminal-source.yml` now compiles this module immediately after `M1EvenResidueSix.lean`, with an explicit `sorryAx` gate. It has not been dispatched: the earlier residue-seven/Rst1Prime source-closure acceptance gate is still pending, and local Lean source staging is unavailable in this invocation.

## What this does not establish

- No successful Lean compile or transitive axiom audit has been obtained for this module.
- No root itinerary currently consumes this residue-two increment.
- This is not a halting proof for TM63, an attained BB(6) score, or a universal upper bound.
