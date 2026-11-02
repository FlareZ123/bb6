# Agent 45: arbitrarily long genuine inverse transition chains in the remaining P1 n ≡ 2 (mod 16) sector

**Status (2026-11-02):** Original-source Lean 4.36.0-rc2 kernel verification succeeded in [manual CI run 41436373902](https://github.com/FlareZ123/bb6/actions/runs/41436373902), source commit `4f03752a609792d12c004fc01e93cc2b55fb1639`. The workflow imported and compiled the **unmodified** `im-results/agent1-p1-map/PosEvenForm.lean` and verified `P1Deep2.lean` in a separate dedicated step. The axioms reported locally for the final theorem were exactly `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`, altered machine, or additional axioms.

This is an **intermediate structural result**, not a blank-reachable path, P1 nonhalting, P1 halting, an upper bound, or an exact solution of BB(6).

## Quantified theorem and construction

The genuine P1 critical hub is `(H(n)-6,3)`, where `H(n)=14·2^n-2n-10`. Let

```text
q(0) = 1,         q(r+1) = 4q(r)+1
n(r) = 16q(r)+2             (hence n(r)≡2 mod16)
z(r) = 2^(n(r)-2r-6)
a(r) = 2^(2r+2) = 3q(r)+1
y(r) = 2^(n(r)-4) = a(r)z(r)
u(r) = 28y(r)-4q(r)-3       (at least 1)
B(r) = 14·2^n(r)-2n(r)-16 = 8u(r)+4.
```

For every `r : Nat` the formally checked `critical_two_sector_unbounded` constructs an initial state `s : Nat × Nat` and a finite `PairPath (2r+4) s (B(r),3)`. A `PairPath k` is by definition a chain of **2k successive actual `BB6.Agent1.T` transitions**. The chain has `4r+8` true `T` steps and grows unboundedly with `r`.

The exact two-step identity, proved from the original `G,T` definitions, is

```text
T(b,d+b+10)             = (b+3,d+b+8)
T(b+3,d+b+8)           = (2b+12,d),     b≡0 mod4.
```

Here a right-hand pair is wrapped in `some` as required by the actual `T` return type. Define `U_0(b)=b`, `U_(h+1)(b)=2U_h(b)+12`. Its proved closed form is `U_h(b)+12=2^h(b+12)`. The source base `seed(r)=4·(21z(r)-1)-12` has nonnegative entries and is divisible by four. An exact arithmetic identity yields

```text
U_(2r+3)(seed(r)) = 6u(r)-2.
```

Starting from a suitable finite right counter, `2r+3` applications of the upper identity end at the state `(6u-2,2u+5)`. The final two genuine transitions are

```text
T(6u-2,2u+5) = (6u+1,2u+3)
T(6u+1,2u+3) = (8u+4,3) = (B(r),3),     u≥1.
```

The second equality invokes a real two-level evaluation of the recursively defined `G`, proved by `middle_pair`.

## Relationship to existing research

Agent 27 [proved an earlier unbounded true-transition inverse construction](../agent27-p1-critical/deep-inverse.md) for critical indices `n=2^(k+3)-2`, always `n≡14 mod16`; it also ends at authentic `(H(n)-6,3)` hubs. This independent Agent 45 construction covers an infinite sequence in the **other still-surviving sector**, `n≡2 mod16`. It exploits the extra depth-one positive-`G` inverse and an upper-chain coefficient identity, including `3q(r)+1=2^(2r+2)`.

Together they show that genuine inverse branches compatible with simple parity and even-left mod4 restrictions can have arbitrarily large length in **both** surviving critical index sectors. Consequently a strategy relying on a *fixed global bound on predecessor-chain depth*, without a stronger reachability restriction, cannot handle every critical index by simply exhausting shorter valid paths. An adaptive tree with a genuine blank-reachability invariant could still decide P1.

**Caution:** The constructed starting state is not shown reachable from `(2,1)`. Even if a true backward transition chain exists, it need not belong to the authentic blank orbit. An actual P1 halting proof requires blank reachability of one critical hub. A nonhalting proof must exclude blank reachability of every critical hub. Neither is established here.

## Reproduction

Source: [P1Deep2.lean](./P1Deep2.lean).

CI run [41436373902](https://github.com/FlareZ123/bb6/actions/runs/41436373902), job `125247014260`, verified:
- original `GParity,GInverse,PosEvenForm,ResetGate` dependencies with no substitutions;
- the new `Verify deep n=2(mod16) real-source P1 predecessor chains` step exited successfully;
- the existing K2 quarter-cone checks continued to succeed, proving that this change did not impair their sources.

The run's SHA `4f03752a609792d12c004fc01e93cc2b55fb1639` ties the certificate to the actual source.
