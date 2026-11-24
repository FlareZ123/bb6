# Full-output MSB profiles and optimal per-block affine budgets

For the original #623 six-state machine, the exact drain output is
represented by a finite exceptional prefix and a constant affine tail.
For each block count b the representation contains all first-counter
values a, including zero-budget branches; no survival assumption is
imposed. The source adapter also implements the entire highLevelNext
map, including the axis, diagonal, odd-first and right-even cases.

## Construction

A profile P stores a pair (J,E) and a finite list of optional signed
pairs relative to (J,E). Read entry a if present; otherwise read (0,0).
A missing outcome means failure. A present relative pair (u,v) means
exact output D(a+J+u, d+3b+E+v) for any initial third counter d.
The proof establishes nonnegativity of both rendered counters and the
excess, so no natural-number clipping changes the result.

The base P(0) is the empty list with tail (0,0). Define:

- Up(P): pop the first exception (if any), add (1,0) to its affine tail.
- Left(P): add (-1,4) to the tail, then prepend a fatal outcome.
- Right(P,Q): take Q with tail shifted by (-1,2), and prepend P's
  normalized zero-budget outcome shifted by (0,1).

Every prepend is expressed relative to the new tail. If the old prefix
is empty and the new entry equals the tail, omit that redundant entry.
Consequently a shift shares the entire list, and push/pop take constant
list operations. The exact flat drain equations establish

    P(3q)   = Up(P(q-1))     for q>0
    P(3q+1) = Left(P(q))
    P(3q+2) = Right(P(q),P(q+1)).

Use three neighboring profile registers (P(max(q-1,0)),P(q),P(q+1)).
Appending one ternary digit selects the corresponding three consecutive
profiles from P(3q-1) through P(3q+3). At q=0 the saturated predecessor
and P(0) use the empty profile. Each step uses a constant number of
signed integer operations and persistent-list push/pop operations.
For b<3^n, every register has at most n+1 exceptions. The actual bit
complexity includes ternary digit conversion and arbitrary-precision
operations; no claim of linear bit complexity is made.

## Exact sharp affine threshold

Let k(b) be the canonical middle profile's prefix length. There exist
signed constants J,E such that for every a>=k and every d the drain
succeeds with D(a+J,d+3b+E) **if and only if k>=k(b)**.

The canonical list never ends with an entry equal to its tail, so its
last exception differs (either failure or a different normalized
output). Every larger a uses the same tail. Any competing universal
affine formula must agree with the tail at a sufficiently large a and
therefore cannot begin before that last exception. This improves a
uniform sufficient budget to a sharp per-input threshold; k(b) can be
zero even when the block count is large.

## Formal evidence and use

DrainProfiles.lean proves profiles_correct, drain_exact, profile_valid,
normalized_exact, profiles_length and sharp_affine_threshold. The
module compiled locally on Lean 4.36.0-rc2, with only propext,
Classical.choice and Quot.sound. DrainProfilesSource.lean instantiates
the six existing Agent49 source flat-drain laws, proves original_profile
and original_sharp_affine, and gives section_exact and root_run_exact
from D(0,7), with the identical source branch partition. The adapter
also compiled locally against a definition-identical arithmetic excerpt
of the pinned Cryptids definitions and rechecked source flat equations,
with no axiom stubs. The complete original-source dependency closure passed focused pinned Lean CI [45467805135](https://github.com/FlareZ123/bb6/actions/runs/45467805135), at 1ca59340fcc8b0689d78edf2f2f99bfdac1eb32c. The focused workflow compiles the original accelerator, flat-drain lemmas, fatal masks and complete profiles with their source adapters and axiom audits.

This is a complete digit-profile representation of the return map, not
an all-time nonhalting theorem. It permits future root arguments to use
the actual exceptional outputs whenever an old sufficient affine budget
fails, rather than treating every visit to that corridor as a terminal
event. The missing quantifier is still a root-specific all-time closure
or an actual terminal witness. No BB(6) bound is asserted.
