# Exact 3-adic residue cylinders for the cryptid_9 S counter

Status: **intermediate and source-derived**, no decision of the original six-state machine and no BB(6) bound improvement.

Machine: `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`, [DeepMind's certified acceleration](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean). In the S section set `q=b+16`. The q-only projection is `f(q)=4(q/3)` for q%3=0, `4(q/3)-3` for q%3=1 and `4(q/3)+1` for q%3=2, with integer division. It applies at q>=16. At S(q-16,0) with q divisible by 3 the physical accelerated machine **transfers to T**, whereas the q-only projection extends f mathematically beyond that transfer. Do not confuse this extension with an actual S orbit.

Lean 4.36.0-rc2 checks source-branch arithmetic identities and the following theorems, for every 16<=x<=y and n>=0:

* `matched_digits_affine`: equality of the first n residue choices implies `3^n * (f^n(y)-f^n(x)) = 4^n * (y-x)`.
* `digital_cylinder_exact`: the first n residue choices agree **if and only if** `3^n | (y-x)`. Thus any finite residue word is exactly one congruence class modulo `3^n` among eligible starting counters.
* `no_eventually_periodic_residue_stream`: for any q>=16, the residue word of the **q-only extension** is never eventually periodic. This does not imply the physical machine remains in S indefinitely.

All `#print axioms` for these central theorems report only `[propext, Quot.sound]`; no `sorryAx`. The latest complete source, including the transfer-density extension, is [DigitalAperiodic.lean.gz.b64](./DigitalAperiodic.lean.gz.b64); decode base64 then gzip to obtain `DigitalAperiodic.lean`, with SHA-256 `ba274e252f787e20b14fe6cf08e3ddf30ae9bad629676e41baa49f836e6bda4f`; if compressed, restore base64+gzip before invoking Lean. The proof uses a standalone restatement of the source's q-only map, plus three source-branch cross-check lemmas, rather than importing the complete original Turing-machine module.

Implication: a finite-prefix residue sieve is an exact 3-adic cylinder query, and periodic-residue hypotheses for the unrestricted counter map are false. Neither fact settles the blank S-entry q=141. Future work should seek a nonperiodic reachable-set invariant incorporating the c counter and the T-transfer guard.

No claim of novelty beyond existing generalized Collatz symbolic dynamics is made. Keep this under im-results pending a genuinely closure-capable consequence.

## Stronger result verified 2026-11-02

The compressed Lean source above additionally contains fully verified `affine_lift`, `liftZero_target`, `growZeros_zero_run`, `dense_transfer`, and `dense_transfer_progression`. For every eligible q>=16, any n,c, there exists y>=q with `3^n |(y-q)` that transfers S to T within `H=n+(c+6*n+1)` attempts. In fact every starting counter `y+3^H*t` (natural t) also transfers within H. All `#print axioms` print only `[propext, Quot.sound]`, with no sorry. This is a constructive obstruction to proving non-transfer uniformly over any finite 3-power congruence class. The actual blank-derived q=141 remains undecided. The source is a standalone arithmetic restatement of the certified acceleration and must be composed with the original-machine bridge before asserting a property of the raw machine.
