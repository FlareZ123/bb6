# Sparse halting-target reduction for an open BB(6) counter machine

**Status:** Mathematical derivation from the published, machine-certified accelerated map, independently checked in the stated local branches. The full global equivalence has not yet been encoded as a Lean theorem; it is presented for adversarial review. No decision of the blank-tape machine is claimed.

Target: `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, one of the 663 BB(6) holdout representatives dated 2026-10-16.

Base: Google DeepMind, `BusyBeaver/BB6/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean` in https://github.com/google-deepmind/cryptids . Its machine-level Lean proof supplies the transition rules for hub `P1(a,c)` and shows that the blank tape reaches `P1(2,1)` after six machine transitions. Define `T` from this source. `GParity.lean` and `Packet.lean` in this repository formally check the auxiliary arithmetic branches.

## The finite even-counter excursion

Call a hub `(a,c)` an **even-phase hub** when both coordinates are even and `c>0`. An even phase begins at such a hub, continues through an intermediate odd-first, even-second hub, and ends when the second coordinate becomes odd, zero, or the accelerated system halts.

From even `a` and positive even `c` the cases are exhaustive:

* `c=2`: `T(a,2)=(a+3,0)`. The phase exits.
* `c=4`: `T(a,4)=(a+3,2)` and `T(a+3,2)=Halt`.
* `c>=6`: the first transition is `(a,c)->(a+3,c-2)`. The second uses `G(k,c-4)`, where `k=a/2+2`.
  * If `c>=a+10`, then `c-4>=2k+2` and `G` takes its high-counter exit, giving `(2a+12,c-a-10)`. Both resulting coordinates are even, and the right counter has strictly decreased by `a+10>=10`.
  * If `6<=c<a+10`, the even input `c-4` lies below `2k+2`. In this region, `G` returns an odd second coordinate. The phase exits. The last statement is independently proved in `Packet.lean` as `G_small_even_returns_odd` and `T_even_small_exits_odd`.

The recursion in the continuing case terminates because `c` decreases. Define the sparse critical set for even `a`:

```text
H(a,0)=4
H(a,n+1)=a+10+H(2a+12,n).
```

The excursion halts **if and only if** its initial second counter is `H(a,n)` for some natural `n`. Proof: if it halts, it must reach the `c=4` case, so trace its deterministic decreasing affine high branches backward. Base case is `H(a,0)`; each backward branch prepends `a+10` and updates the first coordinate to `2a+12`, exactly the recursion above. Conversely the recursion gives a valid high branch `n` times followed by `c=4`. The latter direction is kernel-certified by `Packet.lean` (`critical_gate`, `critical_halts_at`). Its identity `H(a,n)+2n=(a+12)(2^n-1)+4` is kernel-certified as `critical_closed_form`.

## Global blank-tape criterion

**Claim for independent scrutiny:** The accelerated orbit starting at `P1(2,1)` halts if and only if it ever visits `P1(2,H(2,n))` for some `n>=0`. Equivalently, it must visit a hub with first counter 2 and second counter

```text
14*2^n - 2*n - 10,  n = 0,1,2,...
= 4, 16, 42, 96, 206, 428, 874, 1768, 3558, 7140, ...
```

**Forward direction:** The only halting rule for `T` is at odd `a`, `c=2`. Its immediate predecessor must be an even-first hub with `c=4` (kernel-proved `T_danger_predecessor`). This gate is inside a positive even-counter phase. The orbit starts at odd `c=1`. For any transition from an odd second counter, its successor also has an odd second counter, except `c=1` which produces second counter zero: for even first counter the positive odd successor is `c-2`, and for odd first counter the successor is produced by `G` on an odd second-counter input (`G_preserves_odd_second`). Thus, the first positive even second counter of a new phase must be created by `c=0`, whose rule is `T(a,0)=(2,a+1)`. An even phase therefore starts at `(2,c)`, with even positive `c`. The finite phase classifier proves that a halting phase starts at `(2,H(2,n))` for some `n`.

**Reverse direction:** From `(2,H(2,n))`, `critical_gate` and `critical_halts_at` establish finite halting after precisely `2n+2` accelerated actions. The published source validates each macro action as a positive finite sequence of original machine steps, so the original machine halts from this synthetic hub if it is reached.

This reduction isolates the outstanding blank-orbit question: does the orbit from `(2,1)` ever hit this exponentially sparse family? It does **not** show that the family is unreachable. It does not imply nonhalting, prove an upper bound for BB(6), or settle any remaining holdout.

## Tests and evidence boundary

A direct raw-TM simulator and an independent implementation of `T` agreed on 100 hub transitions from the blank-tape entry, covering 112,669 ordinary transitions. An accelerated 1-million-step run from `(2,1)` observed four entries to the positive-even phase: right-counter values 82, 5882, 12114, 29562. None coincided with the critical family; this is a finite observation. The raw simulator confirmed halting from synthetic `P1(2,H(2,n))` for `n=0..8`, up to 4,270,921 defined raw transitions.

The original published machine-to-map bridge is outside this repository and should be audited or imported for any standalone end-to-end formal certificate. The full biconditional about the global blank orbit is currently an informal deductive theorem; its branch lemmas and sufficient direction are kernel-checked. Future agents should formalize the global entry argument, classify prior art, and attempt modular/number-theoretic exclusion of the critical sequence from reachable entries.
