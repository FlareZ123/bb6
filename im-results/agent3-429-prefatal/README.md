# #429: exact two-parent physical pre-fatal gate

## Strongest statement and limits

For the original six-state two-symbol blank-tape machine
`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`, write `R(n)`
for its complete bi-infinite-tape configuration after `n` successful primitive moves.
Let `A/0001` mean state A scanning zero, with the next three consecutive
rightward cells `0,0,1`; let `C/1001` mean state C scanning one with
the next three rightward cells `0,0,1`.

**Original-source Lean-verified exact gate theorem:**
the genuine blank run halts if and only if some `R(n)` is `A/0001`
or `C/1001`. More precisely, a B/001 visit at `R(n+1)` is equivalent,
for **each** `n`, to one of those two visits at `R(n)`. This enumerates
the exact two incoming original transition rows of B, including their
right moves and unchanged right tape. A genuine halt also requires an
earlier scan of the position exactly three cells to the right of the
pre-fatal event. These are infinite-time original-physical-machine theorems with a successful source audit.

This is a *reformulation of the existing exact B/001 halt gateway*
proved by Agent 32, with the two disjoint source predecessor cases exposed.
It does **not** decide #429, improve a BB(6) bound, or establish a fresh
blank-run reachability exclusion. The causal rightward scan is a
coordinate-translated form of Agent 32's earlier right-neighbor frontier
obstruction and is not claimed to be a stronger nonhalting theorem.
Unbounded original-root avoidance of both pre-fatal patterns remains open.

## Source and verification

[`BB429PreFatal.lean`](BB429PreFatal.lean) imports **unmodified**
[`BB429FatalB.lean`](../agent32-429-raw-parent/BB429FatalB.lean)
and the original tape causal lemma in
[`FreshCell.lean`](../agent32-429-raw-parent/FreshCell.lean).
It proves `preFatal_iff_next_fatalB`,
`halts_iff_root_preFatal`, and
`halt_requires_prior_head_three_right`.
Original-source Lean 4.36.0-rc2 checking **succeeded** at [CI 42583819585](https://github.com/FlareZ123/bb6/actions/runs/42583819585), job 129048687075, commit 524c7a91de0a60f992056707f2909444565a78a0. All three theorem audits print exactly `[propext, Quot.sound]`, with no `sorryAx`. The run rebuilds the original physical source and imported predecessor proof with the official SHA-256-authenticated Lean release archive.

The preceding attempts [42583161408](https://github.com/FlareZ123/bb6/actions/runs/42583161408), [42583241824](https://github.com/FlareZ123/bb6/actions/runs/42583241824), and [42583468410](https://github.com/FlareZ123/bb6/actions/runs/42583468410) failed at GitHub's `elan/releases/latest` HTTP 504 download before running Lean. The existing workflow now pins the official Lean 4.36.0-rc2 archive and validates SHA-256. No separate per-commit workflow was created.

## Root-sensitive next step

A genuine blank-origin proof must exclude both `A/0001` and
`C/1001` at *all* times, or produce a genuine witness. In the existing
source grammar, A/0 can be entered from E/0, F/1 or B/1; C/1 can be
entered only from B/0. Thus the two classes expose distinct obligations
at the entry to the exact B/001 gateway. A promising approach is to
transport whole-tape frontier/last-writer invariants across the already
proved unbounded ordinary and exceptional Junc returns, then show every
actual blank-origin entry belongs to the covered grammar. Arbitrarily
prepared source J tapes do not establish the required reachability.

No material belongs in `results/` until a frontier-advancing all-time
machine decision, bound, or general mathematical advance is established.
