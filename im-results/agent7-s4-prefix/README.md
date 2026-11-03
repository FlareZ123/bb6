# S4 prefix compatibility (intermediate)

This programme studies the locally source-mirrored, original DeepMind S4 accelerated holdout, `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`. It is not a BB(6) machine decision or original-source-imported proof.

Let `W([])=0`, `W(b::L)=b+1+2W(L)`. The existing Agent8 proof gives the source-mirrored reduced-map immediate failure criterion `45+W(T)=2^m` for nonempty reduced stack T.

**Mathematical finding, locally Lean4.36 kernel checked:** For every finite list prefix P, a finite suffix S can be appended so `45+W(P++S)` is a binary power if and only if `(45+W(P)) mod 2^len(P)=0`. The self-contained proof uses `W(P++S)=W(P)+2^len(P) W(S)` and gives an explicit one-digit suffix. No sorry, custom axiom or native evaluation; the `prefix_gate_iff` axiom audit is `[propext, Quot.sound]`.

Finite source-shaped exploration found a genuine modeled reduced-seed state at step 27920 of length 18 with `45+W(T)=2^19*70271`. Appending 121601 yields an immediately halting synthetic completion with the same first 18 digits. This witness is computational only, and original DeepMind import remains pending. It does not imply an actual halt from the blank tape. Such examples expose limitations of universally safe fixed-prefix-only invariants, without establishing that arbitrary prefix depths occur along the genuine orbit.

Lean proof source, independent audit code, and original-source provenance are to be linked here as the investigation develops.
