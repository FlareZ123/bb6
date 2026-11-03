# S4 prefix compatibility (intermediate)

This programme studies the locally source-mirrored, original DeepMind S4 accelerated holdout, `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`. It is not a BB(6) machine decision or original-source-imported proof.

Let `W([])=0`, `W(b::L)=b+1+2W(L)`. The existing Agent8 proof gives the source-mirrored reduced-map immediate failure criterion `45+W(T)=2^m` for nonempty reduced stack T.

**Mathematical finding, locally Lean4.36 kernel checked:** For every finite list prefix P, a finite suffix S can be appended so `45+W(P++S)` is a binary power if and only if `(45+W(P)) mod 2^len(P)=0`. The self-contained proof uses `W(P++S)=W(P)+2^len(P) W(S)` and gives an explicit one-digit suffix. No sorry, custom axiom or native evaluation; the `prefix_gate_iff` axiom audit is `[propext, Quot.sound]`.

Finite source-shaped exploration found a genuine modeled reduced-seed state at step 27920 of length 18 with `45+W(T)=2^19*70271`. Appending 121601 yields an immediately halting synthetic completion with the same first 18 digits. This witness is computational only, and original DeepMind import remains pending. It does not imply an actual halt from the blank tape. Such examples expose limitations of universally safe fixed-prefix-only invariants, without establishing that arbitrary prefix depths occur along the genuine orbit.


## Source files and reproduction

- [S4Prefix.lean.xz.b64](S4Prefix.lean.xz.b64): lossless XZ plus Base64 Lean source, **decoded SHA-256 `6989f300afae69d21c8f79b931d9c2bbd3b85851ea1ec7951ad6eed2c96e298a`**. Original file size 3,360 bytes, Base64 1,848 characters. [reconstruct.py](reconstruct.py) validates the digest and writes the standalone Lean source under an atomic lock. Locally compiled with Lean **4.36.0-rc2**. Theorems `W_append`, `synthetic_completion`, `necessary_residue`, and `prefix_gate_iff` are all checked; `#print axioms prefix_gate_iff` reports `[propext, Quot.sound]`. No `sorryAx`, custom axioms, or native evaluation. The theorem is about a pure mathematical binary-weight gate and does not import the original six-state machine.
- [prefix_audit.py](prefix_audit.py): deterministic Python 3 script implementing the original-shaped `epoch` branches, 32-step return, and the five observed compatible genuine modeled prefixes. It performs **300 synthetic arbitrary-stack 32-step comparisons** and independently executes **27,921 reduced seed states** from `[42,12,8,5]`. The simulation is experimental evidence, not a theorem about the blank tape.
- Source acceleration: [Google DeepMind S4 at pinned cryptids revision c86f158](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Accelerations/M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean), with a formal upstream Turing-to-high-level halting bridge. [Agent5's 32-step reduction](../agent5-s4-head/README.md) is locally Lean-kernel-checked against source-shaped copied definitions; its original-source import remains pending. [Agent8's power gate](../agent8-s4-gate/README.md) is locally Lean-kernel-checked against a source-mirrored epoch.

The deterministic Python test prints the following tuple for each indexed modeled reduced state: reduced step, stack length, quotient `q=(45+W(T))/2^len(T)`, last digit of a synthetic immediately halting extension, and power exponent after extension.

| Reduced step | Stack depth | Quotient q | Added digit | Power exponent |
|---:|---:|---:|---:|---:|
| 3 | 4 | 53 | 10 | 10 |
| 40 | 6 | 646 | 377 | 16 |
| 328 | 10 | 3574 | 521 | 22 |
| 3344 | 13 | 47000 | 18535 | 29 |
| 27920 | 18 | 140542 | 121601 | 36 |

At the deepest observed sample, the full 18-digit state is `[82,231,291,571,965,1732,7418,3642,8151,17276,44506,102514,172141,403775,517608,393062,55017,57951]`. The exact synthetic completed stack `T++[121601]` satisfies `45+W(T++[121601])=2^36`. Its immediate modeled reduced transition is `none`, independently checked. It is **not an original blank-root halting witness**. At the time of writing, the large 27,920-step forward occurrence has no Lean certificate; the original source-level source bridge is separately unresolved.

**Consequence:** For every fixed depth at most 18, the finite modeled orbit supplies a prefix which has a synthetic halting completion. Any proposed universally safe forward-invariant predicate that depends *only* on that fixed stack prefix and includes all these modeled genuine-seed states cannot prove nonhalting by excluding every synthetic halter. The observation does not extend to arbitrary prefix depth without a new all-time theorem. Practical next directions are history-sensitive or whole-stack invariants, or a proof that the true root never reaches the terminal power-of-two gate.
