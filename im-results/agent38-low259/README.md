# Machine C: infinite first-stopping class m ≡ 83 (mod 512) excluded from the genuine blank orbit

**Status, 9 November 2026: exact original-source Lean 4.36.0-rc2 kernel-certified intermediate result.** Manual [successful CI run 42576007333](https://github.com/FlareZ123/bb6/actions/runs/42576007333) compiled the unchanged repository `BB6CLine.nextC`, the original `BB6.Agent46.secNext`, complete original section inverse grammar, exact blank-derived section seed, and this entire proof, including explicit `#print axioms` audits. It establishes an infinite authentic-blank reachability exclusion and a first stopping-index obstruction. It does **not** resolve Machine C halting or BB(6).

## Main theorem

```lean
BB6.Agent38Low259.blank_no_first_259 (q : Nat) :
  ¬ BB6.Agent3.CReach 1 (512*q+259)

BB6.Agent38Low259.first_stop_m83_mod512 (m k : Nat)
  (hm : m%512=83) (hstop : k+3*m+4=2^(2*m+3)) :
  ¬ BB6.Agent3.CReach 1 k
```

Here `CReach` is the original, authentic blank Machine C section orbit rooted at `(5,1)`, defined using the source's `secNext`. The first-family stopping equation is the exact original-source criterion. For `m ≡ 83 (mod 512)`, its power term vanishes modulo 512, forcing `k ≡ 259 (mod 512)`. Thus the first result eliminates the entire index class, without an upper bound on `m`, `k`, or return count.

## Source-exact, complete inverse tree

For arbitrary `q ≥ 0`, write

```text
T = (1,512q+259)
P = (256q+128,384q+192)
F = (40q+18,492q+239)
Q = (160q+78,432q+212)
D = (640q+318,192q+95)
R = (592q+288,216q+105)

T <- P
     P <- F          forbidden odd-image
     P <- Q <- R     forbidden odd-image
     P <- D          forbidden odd-image
```

The genuine original-source `oddodd_lowval_blank_reach_iff` shows that any blank reach to `T` necessitates a blank reach to `P`. The newly proved `p_parent_source` shows that any genuine section input returning `P` is one of `F,Q,D`; it invokes the *complete* original source `complete_section_inverse`, including exceptional zero/one-left inputs and all recursive bounce depths.

The source arithmetic for `P` is controlled by `x+y=640q+320=64(10q+5)`. The nonzero-left bounce depth is forced to `n=1` or `n=3`: parity excludes even depths and exact 2-adic valuation excludes `n≥5`. The exceptional zero-left branch would require a power of two divisible by five, which the local Lean proof rules out for every exponent. The direct branch contributes `D`. All other original-source branches are excluded.

For `Q`, the previously certified original-source `section_even_sum_two_mod4_inverse` forces the unique direct parent `R`. Every one of `F,D,R` has an odd right counter ≥5 and coordinate sum congruent to **1 modulo 4**. The original `BB6.Agent3.blank_section_odd_image` theorem prohibits precisely that class at every positive blank-orbit return. The time-zero seed `(5,1)` is handled separately, so the obstruction is valid for the genuine blank run, not merely for abstract nonzero times.

## Reproduction

All checked-in proof modules are human-readable, and none use `sorry`, `admit`, `native_decide`, bounded execution fuel, or private replacement transition rules.

- [Low259Arithmetic.lean](Low259Arithmetic.lean): universal power-of-two congruences and unique bounce-depth arithmetic. Standalone module tested locally with Lean 4.36.0-rc2.
- [Low259Inverse.lean](Low259Inverse.lean): exact three-candidate original-section inverse theorem `p_parent_source`, certified with ordinary Lean foundational axioms by CI.
- [Low259Reach.lean](Low259Reach.lean): authentic blank-root exclusions and stopping-index result.
- [Manual source CI workflow](../../.github/workflows/agent38-low259.yml): copies unchanged repository source and dependency theorems, compiles every module, prints all available axiom audits. The first attempt identified two superfluous tactics after solved branches; the successful second attempt made no mathematical change.

The source theorem identifies an entire infinite class that the established `m % 4 ≠ 1` and `m % 16 ≠ 7` tests do not eliminate. Its strength relative to the full independent finite M512 quotient and every other recently added parametric sieve remains an open novelty/subsumption question. It belongs in `im-results` until an academically independent advance is established.

## Research next steps

The adjacent target `(1,512q+3)`, corresponding to a second half of the index class `m ≡ 83 (mod 256)`, has a different predecessor family `(256q,384q)` and variable 2-adic depth. A uniform obstruction there would double this first-stopping exclusion; the current theorem does not cover it. Other unsolved stopping-index families and the complete Machine C nonhalting proof remain open.
