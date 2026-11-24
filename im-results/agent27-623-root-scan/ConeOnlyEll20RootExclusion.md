# Exact root exclusion of the ell=20 cone-only family slice

## Result

The all-depth cone-only synchronization counterexample family in
[Agent 1's construction](../agent1-623-sync-only/InfiniteConeSyncNonclosure.md)
has exactly three members at mass depth ell=20. Each member's exact
original-source transition is known, and **neither endpoint of any of the
three transitions occurs anywhere on the authentic blank-root orbit**.

This is a finite-depth root-history exclusion. It does not exclude the
all-depth family, prove #623 nonhalting, or resolve BB(6).

## Arithmetic enumeration

For the family source state D(4q+20ell,q), set ell=20. Its
mass is S=5q+400, and the depth condition is

\[
3^{19}<2S+7\le 3^{20}.
\]

Consequently,

\[
116,226,067\le q\le348,678,359.
\]

The family progression specializes to

\[
q_r=\frac{3^8(1+3^8(3+4r))}{2}
    =64,573,362+86,093,442r.
\]

Intersecting this progression with the depth interval gives exactly
r=1,2,3. The Lean proof of the progression identity, interval, and
three-element enumeration is in
[ConeOnlyEll20RootExclusion.lean](ConeOnlyEll20RootExclusion.lean).

## Exact source transitions and root-mass gaps

All states below use the original pinned Cryptids high-level transition.

| r | Source state | Target state | Source mass | Target mass | Root-mass gap |
|---:|---|---|---:|---:|---|
| 1 | D(602667616, 150666804) | D(452000798, 452000456) | 753334420 | 904001254 | run 78–79 |
| 2 | D(947041384, 236760246) | D(710281126, 710280778) | 1183801630 | 1420561904 | run 80–81 |
| 3 | D(1291415152, 322853688) | D(968561452, 968561102) | 1614268840 | 1937122554 | source: run 80–81; target: run 83–84 |

The exact root masses bracketing these states are:

- run 78: 673752537; run 79: 916360488;
- run 80: 1104897223; run 81: 1644184350;
- run 83: 1749476621; run 84: 1986384177.

Agent 41 proves strict increase of root mass under every successful
transition and source-computes these anchors. Therefore no root state can
have a mass strictly between either consecutive pair. Every listed source
and target mass lies strictly inside one such interval, excluding all six
states from the blank-root orbit.

The exact source transitions and all six nonreachability conclusions are
combined in
[ConeOnlyEll20RootExclusion.lean](ConeOnlyEll20RootExclusion.lean), which
imports Agent 41's
[RootMassGapSource.lean](../agent41-623-root-history/RootMassGapSource.lean)
and
[V3MinCounterexampleSource.lean](../agent41-623-root-history/V3MinCounterexampleSource.lean).

## Verification and scope

The combined module compiled against the unchanged source at
[CI run 45451812181](https://github.com/FlareZ123/bb6/actions/runs/45451812181).
Its exported theorem profiles contain only ordinary foundational axioms
(propext, Classical.choice, Quot.sound); the compile step rejects
sorryAx. The overall workflow later failed in a separate Agent 49
total-carry audit at root indices 38 and 39; that failure does not involve
this module, whose compilation step succeeded.

The next mathematical question is whether root-mass intervals or a stronger
root-history invariant can exclude further depths without repeating finite
root replays. The ell=20 argument alone gives no all-depth conclusion.
