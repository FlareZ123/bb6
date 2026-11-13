# Rst1' counted reset-core investigation

## Candidate itinerary

Input family: `s1Config L 0 1 a 0 b h` in the source S1 encoding.

The observed TM63 trace has ten phases:

| Phase | Operation | Steps |
|---|---|---:|
| 1 | left sweep of `3a+1` | `9a+3` |
| 2 | fixed bridge | `8` |
| 3 | left sweep of `3L+5` | `9L+15` |
| 4 | fixed bridge | `20` |
| 5 | right sweep of `L+1` blocks | `3L+3` |
| 6 | fixed bridge | `9` |
| 7 | right sweep of `a+1` blocks | `3a+3` |
| 8 | fixed bridge | `6` |
| 9 | right sweep of `b` blocks | `3b` |
| 10 | fixed bridge | `30` |

Total primitive steps: `97 + 12*(L+a) + 3*b`. The endpoint head is `h+5+3*b`.

The candidate target family is the source S1 configuration with parameters `L+a+2`, `R=(2^(L+2)-1)*2^a-1`, marker `2`, right unary parameter `b`, value `2^b-1`, and final right parameter `0`, at head `h+5+3*b`. This endpoint equality is not yet formally proved in this directory.

## Fixed bridge traces

All windows and marks below are head-relative. Each start configuration has state D (state index 3) and head 0. `CountedRst1Prime.lean` gives finite traces and a generic source-connected frame lifting theorem.

| Steps | Window | Start marks | End head/state | End marks |
|---:|---:|---|---|---|
| 8 | `[-3,0]` | `[-1]` | `-2 / D` | `[0,-2,-3]` |
| 20 | `[-5,3]` | `[-3,-2,-1,2,3]` | `4 / D` | `[1,0,-1,-3,-4,-5]` |
| 9 | `[-2,2]` | `[0,2]` | `3 / D` | `[0,-1,-2]` |
| 6 | `[-1,3]` | `[2,3]` | `4 / D` | `[1,0,-1]` |
| 30 | `[-3,5]` | `[-3,0]` | `-4 / D` | `[-2,-1,0,3,4,5]` |

The local windows are parameter-independent in the raw simulator. The finite `fRun` computations are intended to be checked by Lean `decide`; the generic `bridgeAt` lifts them through `run_frame` and `shift_run` once the actual tape agrees on the window.

## Current proof status

The source-connected ten-phase chain is now formalized through the final
bridge30 endpoint in two intermediate modules:

- `CountedRst1Prime.lean` contains the finite bridge traces, generic
  frame-lifting machinery, source sweep preservation lemmas, exact
  three-cell right-sweep block behavior, and the head-facing `d0pow`
  segment composition. The latest shared edits are being repaired against
  targeted Lean CI by Agents 24 and 42; the most recent reported run
  `43426490117` failed, so these lemmas are **not yet certified green**.
- `Rst1PrimeBridge6Source.lean` extends the source-connected prefix through
  bridge9 with the bridge6 source-tail identification, final b-block sweep,
  exact bridge30 input window, bridge30 run, final head/right-facing word,
  preservation of the left tail, three d0-counter segment proofs, marker2
  and d1 cells, the full left-facing target word, and the candidate exact
  equality `rst1PrimeAfterBridge30_eq_s1Successor`.
- The intended endpoint is exactly
  `s1Config (L+a+2) (2^(L+a+2)-2^a-1) 2 b (2^b-1) 0 (h+5+3*b)`.
  The endpoint proof is a source-level Lean proof attempt, but has not yet
  been compiled. Do not report the universal ten-phase theorem as proved
  until the full module and all dependencies pass kernel verification.
- The manual champion-root workflow remains manual-only. Do not restore
  push triggers or create per-commit workflow fan-out.

## Next steps

1. Obtain the exact post-`4e21fa6` CountedRst1Prime diagnostics from
   Agent 24/42, repair the shared sweep/segment lemmas without overwriting
   concurrent changes, and get that dependency green.
2. Run the existing targeted Rst1' workflow on the current
   `Rst1PrimeBridge6Source.lean`; fix concrete Lean diagnostics in the
   bridge6/bridge30 composition, left-facing segmentation, and final
   `Config` equality.
3. Once the endpoint equality is kernel-verified, compose the counted runs
   from the earlier Bridge9 source module through bridge30, then prove the
   ten-phase total cost `97+12*(L+a)+3*b`.
4. Coordinate with Agents 24, 42, and 46 for root integration. Keep this
   result in `im-results/` until the complete rooted argument and novelty
   review justify promotion.
## 2026-11-13: universal ten-phase reconstruction

The ten-phase itinerary has now been replayed against the literal 12-entry
TM63 transition table, with every phase boundary checked. A V8 replay over
all 729 triples `0 <= L,a,b <= 8` passed:
- each left-sweep input condition and right-boundary zero;
- each right-sweep three-one-block condition;
- all five fixed bridge input windows and exact output windows;
- the final state, head, and complete finite marked-tape set.

The reproducible standalone script is [rst1prime_replay.js](rst1prime_replay.js).
This remains finite computational evidence, not a universal proof.

### Exact source theorem target

For every natural `L,a,b` and every absolute head `h`, the intended theorem is

```lean
run tm2 (97 + 12*(L+a) + 3*b)
  (s1Config L 0 1 a 0 b h)
=
some (s1Config (L+a+2) R 2 b (2^b-1) 0 (h+5+3*b))
```

where

```lean
R = 2^(L+a+2) - 2^a - 1
```

The endpoint's source words simplify exactly to

```text
left-facing:
  d0pow b ++ markerWord 2 ++ d0 ++ d0pow a ++ d1 ++ d0pow (L+1) ++ lh

right-facing:
  [0,1,1,1,0,0] ++ d1pow 1
```

The two counter identities needed for this normal form follow directly from
the source `binDec` recursion:

```text
binDec b (2^b-1) = d0pow b
binDec (L+a+2) (2^(L+a+2)-2^a-1)
  = d0pow a ++ d1 ++ d0pow (L+1)
```

For the second identity, the complemented recursion argument is
`2^(L+a+2)+2^a`: it emits `a` even/d0 branches, one odd/d1 branch,
then `L+1` even/d0 branches.

### Absolute head ledger

Starting from head `h`, the successive D-head positions are:

| Phase | Operation | Steps | End head |
|---|---|---:|---:|
| 1 | left sweep of `3a+1` ones | `9a+3` | `h-(3a+1)` |
| 2 | bridge 8 | `8` | `h-(3a+1)-2` |
| 3 | left sweep of `3L+5` ones | `9L+15` | `h-3a-3L-8` |
| 4 | bridge 20 | `20` | `h-3a-3L-4` |
| 5 | right sweep of `L+1` three-one blocks | `3L+3` | `h-(3a+1)` |
| 6 | bridge 9 | `9` | `h-3a+2` |
| 7 | right sweep of `a+1` three-one blocks | `3a+3` | `h+5` |
| 8 | bridge 6 | `6` | `h+9` |
| 9 | right sweep of `b` three-one blocks | `3b` | `h+9+3b` |
| 10 | bridge 30 | `30` | `h+5+3b` |

The costs sum to `97+12*(L+a)+3*b`.

### Uniform hypotheses to discharge

The source left word at the input is

```text
d1pow a ++ [1,0,1] ++ d0 ++ d1pow L ++ [1,1,0,1,1,1].
```

The right word is `[0,1,1,1,0,0] ++ d1pow (b+1)`. These give the first
left-sweep run of `3a+1` ones and its zero right boundary. Bridge 8 then
supplies two leading ones; together with the remaining `d0` tail,
`d1pow L`, and the first two `lh` bits, they give the second left-sweep
run of `3L+5` ones and its zero right boundary.

After the second left sweep, the interval from `h2+2` through `h1+1`
is all ones. Bridge 20 overwrites its local `[-5,3]` window with the
fixed frame; the untouched remainder supplies the `L+1` right-sweep
blocks. Bridge 9 converts the final one of those blocks into the `d1`
boundary and exposes the next `a+1` three-one blocks. The first left sweep
and the source right separator provide the `a+1`-block run. Bridge 6
converts its last block into marker 2 and exposes the `b` right-counter
blocks. The source `d1pow (b+1)` suffix supplies the final `b`-block run.

### Endpoint tape decomposition

The output's repeated d0 blocks arise by the same nested boundary mechanism:

- `d0pow (L+1)` consists of the bridge-20 left boundary plus the first
  `L` blocks of the `L+1` right sweep; bridge 9 turns the last block into
  `d1`.
- `d0 ++ d0pow a` consists of the bridge-9 left boundary plus the first
  `a` blocks of the `a+1` right sweep; bridge 6 turns the last block into
  marker 2.
- `d0pow b` consists of the bridge-6 left boundary plus the first
  `b-1` blocks of the final `b`-block sweep; bridge 30 consumes the final
  block together with the following separator and fixes the right-facing word.

This is the exact tape-alignment proof plan. It remains to encode these
cellwise interval identities and all ten run compositions in Lean. The
current `CountedRst1Prime.lean` still contains only the finite bridge
frames and arithmetic cost identity; it does **not** yet contain the
universal ten-phase theorem. No BB(6) score or upper bound follows until
that formal source theorem and the downstream root/terminal chain are proved.
