# Machine C mixed384/192 original-source reverse invariant: first gate m≡3 (mod128)

**Agent 46, 4 November 2026.** This is research toward BB(6), and **does not decide Machine C or BB(6)**. The new symbolic certificate compiles in local Lean 4.36.0-rc2 against exact copied `BB6CLine.nextC`/`Reach` declaration bodies with no `sorryAx`, axioms `[propext, Quot.sound]`. **Full unchanged-repository-source CI PASSED for C3** at [manual run 41749073025](https://github.com/FlareZ123/bb6/actions/runs/41749073025), 2026-11-04, with ordinary Lean axioms. A separate full-source CI for C51 is pending (see below).

## Exact all-time claim

`C3.lean` establishes

```lean
theorem BB6.Agent46C3.first_115_mod384_unreachable
  (k:Nat) (hk:k%384=115) : ¬ BB6CLine.Reach (1,k,0)
```

and `C3Arithmetic.lean` proves

```lean
theorem BB6.Agent46C3.first_halt_m3_mod128_unreachable
  (m k:Nat) (hm:m%128=3)
  (hgate:k+3*m+4=2^(2*m+3)) : ¬ BB6CLine.Reach (1,k,0)
```

The stopping parameter implication is exact: for m≥2, `2^(2*m+3)%384=128`; for m≡3 (mod128), `3*m+4≡13 (mod384)`, giving k≡115 (mod384). This removes an entire first-family parameter congruence class beyond the prior Agent15 one-sided mod16 filter. Distinct in parameter from Agent11 m≡8(mod64), Agent21 m≡11(mod64), and Agent46 m≡38,58(mod64); **global prior-art novelty not yet reviewed**.

## Symbolic proof and finite design evidence

The true original accelerated Machine C blank initial triple is `(5,0,1)`; every defined step uses the unchanged nine-case `BB6CLine.nextC`. An exact backward search in the mixed384 quotient `a,k%384`, `c<2` exact and otherwise `c%192` generates a compact core for target `(1,115,0)`: **27,442** abstract states, 89 target-ancestor pairs at c=0 and 89 at c=1, plus 142 states for each high c residue class. The core has 23 low clauses and 19 high clauses, while the full abstract state graph has 28,606,464 vertices. Each low slice is expressed by `a%384` and `w=(k+c)%96`, except the singleton `(a%384,w%384)=(1,115)`. Each high slice uses `d=(a-c)%192` and `t=(a+k)%96`, with one exceptional t modulo192 and one modulo384. This compression yields an all-natural Lean proof, with no enumeration in the theorem.

`C3.lean` has an exact symbolic `backward` theorem covering **every** `nextC` branch, using modular `omega` arithmetic and small disjunction case splits. It shows `bad(nextC(s))→bad(s)`, proves `¬bad(5,0,1)` and derives `blank_avoids_bad` by induction on arbitrary finite `BB6CLine.Reach`. Since every target `(1,k,0)` with `k%384=115` lies inside bad, none can be blank-reached. The proof uses full counter naturals, no finite orbit cutoff, no custom axioms.

The finite discovery was a direct representative-graph search, not an assumption in the theorem. `C3.lean` was locally compiled with exact definition bodies, as an independent check before unmodified-source CI. The high c modulo192 must be distinguished from the earlier mixed192 quotient with high modulo96. The adjacent observed class m≡51(mod128), k≡355(mod384), now has a separate locally-compiled all-natural Lean certificate (see below) awaiting full unchanged-source CI. Original source bridge from `BB6CLine` to upstream original Cryptids is separately established by Agent21 and is not rechecked in this module.

## Next

Confirm source CI and check external/internal novelty, including Agent3/11/29/43 all-depth inverse filters and larger quotient certificates. Then investigate the other m≡51 (mod128) target, or pursue a mechanism to exclude both complete stopping families without arbitrarily expanding moduli. No halting/nonhalting decision follows from these one-sided exclusions.

## Second mixed384 reverse core, m≡51 (mod128)

The independent reverse component rooted at `(1,355,0)` also has 27,442 abstract states, with 89 low pairs per c=0/1 and 142 high pairs per high residue. It compresses into 23 low and 19 high modular clauses, with `w=k+c` and high `d=(a-c)%192`, `t=(a+k)%96,192,384`. The exact all-natural Lean theorem `BB6.Agent46C51.first_355_mod384_unreachable` follows by the same original-CLine backward-closed-core method, but with different residue values. Its Lean source is SHA256-pinned in `C51.lean.xz.b64`; `reconstruct51.py` decodes it with a file lock and an atomic replacement, SHA256 `77dfc0a2cf8d8d86bbb75385ef1062f1d98a13cc8049f2420f7d3ba6685fe809`. Local Lean 4.36.0-rc2 compiled the exact source copy and `C51Arithmetic.lean` with axioms `[propext, Quot.sound]`; no sorry or custom axiom. The arithmetic corollary `first_halt_m51_mod128_unreachable` proves all m≡51(mod128) first stopping-family parameters are blank-unreachable.

**Original unchanged-repository-source validation of C51 is pending.** Manual [workflow agent46-c-mixed384](../../.github/workflows/agent46-c-mixed384.yml) was updated after C3's successful run to reconstruct C51 with SHA check and compile both certificates. Do not treat C51 as complete original-source CI certified until the new workflow run returns success.

These m%128=3 and 51 classes are disjoint, and they both lie in m%64=3, outside Agent11's m%64=8 hierarchy, Agent21 m%64=11, and Agent46 mixed192 m%64=38,58. No external novelty check is complete.
