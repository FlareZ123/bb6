# Agent 12: exact backwards certificates and an infinite mod-8 barrier

## Machine and scope

Machine `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`. The `G` and `T` maps are identical to those in [DeepMind's formally verified P1 acceleration](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean). Initial accelerated state `(2,1)`.

The stand-alone Lean development independently **restates** the map. It does not import the upstream machine-to-map semantic bridge. Thus the proofs are kernel-checked statements about the stated acceleration, and the TM interpretation relies on that upstream bridge.

### Kernel-checked results, Lean 4.36.0-rc2

1. `blank_ne_fourth_critical`: no path from `(2,1)` to `(2,206)`. This is index n=4 of the known infinite critical halting family.
2. `blank_no_four_mod_eight`: **for all d >= 28 with d % 8 = 4**, no path from `(2,1)` reaches `(2,d)`. This is an infinite all-time blank-entry property.
3. `blank_no_critical_one_mod_four`: **for every n >= 5 with n % 4 = 1**, no path from `(2,1)` reaches the halting-critical hub `(2, 14*2^n - 2*n - 10)`. Infinite excluded subfamily.
4. `G_to_200_3` proves the complete inverse of one significant recursive drain output, used in the n=4 proof.
5. `T_to_mult4_even` proves the complete universal predecessor equations when the output is positive even on the right, divisible by 4 on the left.

All compiled with `lean` 4.36.0-rc2, using `import Std` and no `sorry`. `#print axioms` for the three highlighted theorems returned `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

### Reconstruct the source

GitHub connector size limitations led to checked source stored as deterministic XZ + base64. `InfiniteMod8Barrier.lean.xz.b64` decompresses to the complete stand-alone source `NoFourthTarget.lean`. On any Python 3 system, use:

```python
from pathlib import Path
import base64
import hashlib
import lzma

packed = Path("im-results/agent12-backwards/InfiniteMod8Barrier.lean.xz.b64").read_text()
source = lzma.decompress(base64.b64decode(packed.strip()))
assert hashlib.sha256(source).hexdigest() == "ea708a402104f1b333ba1e50cda8fe889ada6c01f1b5c4d997b4586d30d08501"
Path("NoFourthTarget.lean").write_bytes(source)
```

Compile `NoFourthTarget.lean` with Lean 4.36.0-rc2. An earlier snapshot `NoFourthTarget.lean.xz.b64` has only the fourth-target exclusion, already separately compiled.

### Mathematical proof sketch for the infinite barrier

The established modular invariant says every reachable `(a,c)` with positive `c` and even `a` satisfies `a=2` or `a%4=0`. Suppose `(2,d)` is reachable, `d>=28`, `d%8=4`:

* The unique predecessor is `(d-1,0)`. Its two possible predecessors are `(d-3,1)` and `(d-4,2)`.
* `(d-3,1)` forces the earlier hub `(d-6,3)`, impossible by the modular invariant because `d-6 ≡ 2 (mod 4)` and `d-6>=22`.
* For `(d-4,2)`, the `G` even-output inversion gives a predecessor `(z,t)` with `d-4=2z+6` and `t=z+7`. The residue forces `z≡1 (mod4)`. Since `z` is odd and `t>0`, any preceding hub is `(z-3,t+2)`, where `z-3≡2 (mod4)`, `z-3>=6`: also impossible by the modular invariant.

This backward decomposition is exhaustive, proved symbolically within Lean. For n>=5 congruent 1 modulo 4, the critical right coordinate is `4 mod 8` and at least 28.

### Significance and limits

The n=1 critical target is excluded by Agent 4's existing `NoSecondTarget.lean`; this new infinite theorem excludes **all** later critical n congruent 1 mod 4. The other residue classes, including n=2,3,4 mod 4 (and the special n=1 proof), still demand work. The P1 machine's blank-tape behavior and BB(6) remain unsolved. No claim of new BB(6) bound or a decided holdout.

The exploratory backwards predecessor enumeration (distinct from these proved Lean theorems) saw finite forbidden-only backward closures for indices 0 through 285 except a 100k-node cap at n=286, and many further indices. This observation is not a proof: a complete verified inversion procedure or symbolic invariant would be needed to promote those computations.

### Reproducibility SHA256

`InfiniteMod8Barrier.lean.xz.b64`: decompressed source SHA256 `ea708a402104f1b333ba1e50cda8fe889ada6c01f1b5c4d997b4586d30d08501`; compressed text Adler-32 `b0dd6af9`. Both the file length (4160 base64 characters) and the Adler checksum were verified against the pushed GitHub blob.

## Second infinite residue barrier, n ≡ 3 (mod 8)

The separate, **plain-text**, Lean module `InfiniteMod16Barrier.lean` imports `NoFourthTarget` (reconstructed from `InfiniteMod8Barrier.lean.xz.b64`) and contains two more fully checked theorems:

- `blank_no_zero_mod_sixteen`: for every `d≥64` with `d % 16=0`, the original reachable set from `(2,1)` excludes `(2,d)`.
- `blank_no_critical_three_mod_eight`: for every `n≥3` with `n % 8=3`, the critical target `(2,14*2^n-2*n-10)` is unreachable. In particular the formerly unresolved n=3 target `(2,96)` is ruled out.

These results were independently compiled with Lean 4.36.0-rc2, with the audit `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. Reconstruct the packed baseline module according to the Python recipe above, compile it into `NoFourthTarget.olean`, and then run `LEAN_PATH=<module-directory> lean InfiniteMod16Barrier.lean`. In the working local setup both compiled successfully in that order.

The mod16 proof unrolls two additional layers of alternating odd-output and `G` direct even-output inverse transitions. Every possible branch either contradicts the global even-left reachable invariant or is ruled out arithmetically. These are genuine all-time reachability exclusions but do not classify all critical-index residue classes and do not decide BB(6).

Potential research: analogous short symbolic inverse trees for the `d%16=8` class (critical `n%8=7`), then `d%8=6` (critical `n%4=0`) and `d%8=2` (critical `n%4=2`).

## Third critical target n=2, d=42, now rigorously excluded

The plain Lean module `RankCutoff.lean` imports the reconstructed `NoFourthTarget.lean` and proves `blank_ne_third_critical : ¬BlankReach 2 42`. This settles the previously open target equivalent to Agent 4's gateway (36,3).

The proof establishes that every nonhalting T transition strictly increases rank a+c. A complete 24-state initial prefix has a kernel-verified Boolean one-step closure: all next states are within the prefix or have rank at least 45. By induction every reachable state is either on this prefix or has rank>=45. The critical target (2,42), rank44, is not in the prefix. `earlyValid_true` uses `decide +kernel`, and the axiom audit for the final theorem reports only `[propext, Classical.choice, Quot.sound]`; no sorryAx.

To reproduce, compile `NoFourthTarget.lean` from the packed baseline, then compile `RankCutoff.lean` with `LEAN_PATH` set to its olean directory.
