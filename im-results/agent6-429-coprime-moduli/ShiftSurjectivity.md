# Kernel-checked modular affine-shift principle

**Agent 6, 2026-11-06 00:05 UTC. Intermediate formal infrastructure; no BB(6) decision.**

[Lean source](ShiftSurjectivity.lean) contains the generic theorem
`ShiftSurjectivity.dense_all_moduli`, locally compiled with **Lean 4.36.0-rc2** against `Lean.Elab.Tactic.Omega`, with printed axioms exactly `[propext, Quot.sound]`. No `sorry`, external definitions, `native_decide`, or assumed number-theory results. The source is self-contained.

**Precise statement.** Given any `f : Nat → Int`, suppose for every modulus `m>1` there are `p>0`, a threshold `C`, and the eventually valid relation

```
p % m ≠ 0
∀n≥C, (f(n+p)+p) % m = f(n) % m.
```

Then for every modulus `m>0`, integer residue target `t`, and lower bound `L`, there exists `n≥L` with `f(n)%m=t%m`.

**Proof insight.** Rather than reducing from `m` to `gcd(m,p)` and solving a general linear congruence as in [the existing all-mixed-moduli proof](AllMixedModuliZeroSector.md), reduce to the **positive remainder** `r=p%m<m`. By induction choose a sufficiently late `n` with `f(n)≡t (mod r)`. Thus `f(n)-t=rq` for some signed integer `q`. Choose the nonnegative shift count `k=q mod m`. Since `kp≡qr=f(n)-t (mod m)`, iteration of the given shift shows `f(n+kp)≡t (mod m)`. The formal proof covers signed `q`, arbitrary cutoffs, and the base modulus one.

**What remains for Machine #429.** The exact source-certified synthetic halting family uses `H(c)=4·2^(4·2^c+c−10)−8·2^c+13−c` (`c≥2`). The paper proof [AllMixedModuliZeroSector.md](AllMixedModuliZeroSector.md) supplies a candidate shift period `p=lcm(φ(m),φ(φ(m)))` and proves `m∤p` by largest-prime-divisor valuations. **Those H-specific period and valuation facts have not been kernel-checked by this file** and must be formalized before claiming that the universal modular saturation of the actual H family is fully Lean-certified. The source-certified individual halting family and its true blank-root inaccessibility question are separate.

**Reproduce.** Run `lean ShiftSurjectivity.lean` with the local Lean 4.36.0-rc2 binary. At creation the local source had SHA-256 `20b0daed9579163790850195ebd5fffd9a16f53bde8bec47e6d821ec955758f2` and the axiom printer reported `[propext, Quot.sound]`. The source was pushed through the GitHub Contents API, preserving the full Lean text. Original-source CI is unnecessary for a self-contained pure arithmetic lemma.

**Interpretation.** This verifies the abstract induction engine, independently of the unverified machine-specific period construction. It does not establish root reachability, root nonhalting, or the exact BB(6) score.