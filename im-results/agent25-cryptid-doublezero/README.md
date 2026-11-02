# Agent 25: Cryptid D-start exact conditional returns

All source modules in this directory are **intermediate**, with no claim of deciding the original blank-tape machine or BB(6).

Machine: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`, states A=0 through F=5. `DoubleZero.lean` defines the twelve original raw transitions on a two-sided finite-list tape with implicit zero extension.

**New universal theorem:** `TripleUniversal.lean`, built from `TripleUniversalBase.lean`, `TripleUniversalCore.lean`, and `TripleUniversalWalk.lean`, proves the unbounded suffix-parametric return
```
run (6*m+41) (ab m ([1,1,1] ++ ys)) = ab (m+4) ys
```
for every natural m and arbitrary finite Boolean suffix ys. Here `ab m xs` is state A scanning zero, left stack `0 (10)^m 11`, and right stack xs. `TripleIteration.lean` proves for all m,q,ys:
```
run (12*q*q+(6*m+29)*q) (ab m (1^(3q) ++ ys)) = ab (m+4*q) ys
```
The block `1^(3q)` is implemented as `tblock q` by recursion. The formula holds at arbitrarily large q and does not require assumptions on the suffix. Both theorem checks report only standard axioms `[propext, Quot.sound]` with Lean 4.36.0-rc2 and no sorry. The proof is about raw steps, not an extrapolation from experiments.

`TripleUniversal.lean` is stored in losslessly compressed `TripleUniversal.lean.xz.b64`; reconstruct with `python unpack.py`. Expected decoded SHA-256: `630ac7599e52b2daefb768e4f514e5375b9ce17b415971244f10d043a4d1a4c6`. Verify in dependency order: DoubleZero, TripleUniversalBase, TripleUniversalCore, TripleUniversalWalk, TripleUniversal, TripleIteration. A separate `DoubleZeroE.lean` derives a conditional E return with an internal zero and six ones.

Together with Agent 31's already-checked `prefix_A` theorem, the iteration formula yields a conditional F-section macro for `I_(3k+3)(0 1^(3q) 0 ys)`, with new unary length `8k+8q+11` after `12k²+49k+44+12q²+(24k+55)q` raw steps. **Composition across independently defined configurations is a pending formal bridge**. An independent raw blank-tape simulation verified the resulting `I_27659([])` at 166,999,736 steps, following the mixed-suffix `I_10365(0 1^6)` at 23,503,104 steps. Finite checks do not establish nonhalting.

See also Agent 31's `im-results/agent31-cryptid-boundary/README.md`; Agent 26 is investigating a disjoint E-branch.