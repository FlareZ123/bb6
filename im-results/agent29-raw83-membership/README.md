# Raw83 membership preflight

This directory contains membership-only Lean checks for Agent10's source-accepted Raw83 four-hole parent Cover. It does not define a competing global roster and does not itself remove any Canonical64 representative.

## Exact parent

`1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RA`

The definition is copied from Agent10's generator expression:

```lean
refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨false,true,0⟩)
```

The table has four undefined transitions (A1, C1, E0, F0), hence 25^4 = 390,625 compatible completions. Agent10's exact parent Cover is source-accepted at weighted maximum 514, with a 513-move attaining run plus halt tick (run 45755362807, artifact 15087730774; see `results/2026-11-26-raw83-parent-exact-agent10.md`).

## Membership checks

- `Raw83Canonical59Membership.lean`: checks the root transition, unique membership in roster64, unique membership after the five proposed cuts p58/p59/p108/p115/p119, and pairwise distinction from those five.
- `Raw83Canonical58Membership.lean`: checks unique membership after the six existing cuts p58/p59/p108/p113/p115/p119, and pairwise distinction from all six. This is the relevant prerequisite for a possible seventh parent / 57-residual consumer.

The first preflight (run 45824051367) rebuilt the Canonical64 base successfully and compiled `p83_root`, `p83_count64`, and `p83_count59`. Its job failed only because the new five-parent distinctness theorem had an ambiguous unqualified `parents`; Agent10 corrected it to `BB6.Agent31Canonical59Membership.parents` in commit 70bac442f2ce2fc7d03ec3e86e0cfd1eef0c2ed0. The post-six theorem uses the fully qualified Canonical58 parent list.

Runs 45825342699 (five-parent retry) and 45825498585 (five- and six-parent preflight) are the current source-acceptance attempts. The latter is the stronger run and compiles both membership modules against the pinned Canonical64 source closure.

## Integration status

Membership alone is not a global reduction. A seven-parent Canonical57 consumer must also import the six-parent integrated Cover theorem and Agent10's accepted Raw83 Cover, lift the 514 bound to the common 6,766,859 threshold, prove pairwise distinction, and pass the source/kernel closure gate. Agent10 owns the separate Canonical57 draft; Agent31 remains the shared integration owner.
