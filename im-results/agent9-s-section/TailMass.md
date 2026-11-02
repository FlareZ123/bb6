# Source-certified exponential bounds for cryptid_9 transfer histories

**Agent 9, 2026-11-02. Status: intermediate combinatorial theorem; not a BB(6) decision.**

## Scope and mathematical statement

For the published high-level S section of the six-state machine `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`, the transformed counter `q=b+16` has a ternary residue digit at every call. Its height `c` decreases by 1 at residue 0 and increases by 4 or 6 at residues 1 and 2, respectively. The machine transfers from S to T only when height is zero and the next digit is zero. This is a *transfer*, not necessarily Turing-machine halting.

For `n,c : Nat`, let `C(n,c)` be the number of length-`n` ternary words with digit counts `z,u,v` satisfying `z+u+v=n` and `z=c+4u+6v`. It counts all words whose unrestricted S-height after `n` actions is exactly zero; some are not physically valid S prefixes because they would have transferred earlier, so the count is a valid overestimate.

**New standalone Lean 4.36.0-rc2 certificates** in [TailMass.lean.gz.b64](./TailMass.lean.gz.b64) establish for *all* natural `n,c`:

```lean
Agent9Tail.critical_count_bound (n c : Nat) :
  2^(6*n+c) * criticalCount n c ≤ 133^n

Agent9Tail.critical_count_bound32 (n c : Nat) :
  (3^c*1458^n) * criticalCount n c ≤ 2^c * 2603^n
```

The source contains executable `words n` and `criticalCount n c`, a complete enumerator of all 3^n ternary words; it proves by induction that every enumerated word has the right length and that the weighted tree mass has the claimed exact closed form. **Both decisive `#print axioms` report only `[propext, Quot.sound]`, with no `sorryAx`.** The source defines a standalone exact residue-word model and relies on the preexisting exact-cylinder bridge described in [DigitalAperiodic.md](./DigitalAperiodic.md) to apply it to physical S entries. It does not import the original Turing-machine formalization.

## Proof idea

For the first inequality, assign weights `128,4,1` to ternary digits `0,1,2`. The total weight of all length-`n` words is exactly `133^n`. Each zero-height word has exactly weight `2^(6n+c)`. Its contribution to the nonnegative sum gives the counting bound.

For the sharper inequality, use digit weights `2187,288,128` with total branching weight `2603`. The weights equal `1458` times the factors `3/2,(2/3)^4,(2/3)^6`. For each zero-height word `w`, Lean proves the integer identity

```
2^c * weight(w) = 3^c * 1458^n.
```

Summing over zero-height words and bounding by the full tree yields the sharp rational-tilt inequality. This improves the earlier factor `133/192 ≈ 0.6927083` to `2603/4374 ≈ 0.59510745` for the exponential rate, with a changed `c` prefactor. The optimizer over real tilts is around 1.46676, so 3/2 is close to optimal while preserving integer arithmetic.

## Statistical corollary (derived outside Lean)

The earlier exact 3-adic cylinder theorem says each length-`n+1` ternary residue word occurs in exactly one congruence class modulo `3^(n+1)` of eligible S inputs. A transfer on attempted call `n+1` requires zero height after `n` actions and a final zero digit. Thus the fraction of initial `q` classes with that event is at most

```
(1/3) * (2/3)^c * (2603/4374)^n.
```

By the union bound, the fraction transferring for the first time on or after call `N+1` is at most

```
(2/3)^c * (1458/1771) * (2603/4374)^N.
```

This uses a bound on all unrestricted height-zero histories, so is valid without any assumption of stochastic independence of steps along a *fixed* natural-number trajectory. Uniformly sampled residue cylinders do have independent ternary digits by the already-proved cylinder bijection. The probabilistic inequalities are elementary corollaries, **not additional Lean-certified theorems**. They bound the tail of transfer times among varying starting counters and say nothing certain about the single blank-derived `q=141,c=3` trajectory.

## Reproduction

The full Lean source is stored as one base64-encoded gzip UTF-8 file at `TailMass.lean.gz.b64`. Decode base64 and gzip and compile the resulting `TailMass.lean` using Lean **4.36.0-rc2**. Uncompressed source: **9,529 bytes**, SHA-256 **`78d1d2a481aa3e7b7c1d14d08f9e325f751f5181e5f243836858ae9bd966020f`**. Local compilation finished with no errors; nonfatal linter/deprecation warnings do not affect the kernel proof. No Mathlib required, only `import Std`.

These are reusable finite-word counting certificates and exponential probabilistic tail estimates. They neither prove nontransfer for `q=141` nor decide this six-state machine or BB(6). Hence all work is deliberately in `im-results/`.
