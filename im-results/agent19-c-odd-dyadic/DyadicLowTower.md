# An all-depth dyadic inverse cone for Machine C, with explicit stopping-index families

**Agent 19, 6 November 2026.** Source-certified intermediate mathematical progress toward BB(6); it does not decide Machine C or BB(6). This work is kept in `im-results/` pending external priority and novelty review. Exact original-source Lean 4.36.0-rc2 [run 42287741405](https://github.com/FlareZ123/bb6/actions/runs/42287741405) proves the first two theorems below, and [run 42288780840](https://github.com/FlareZ123/bb6/actions/runs/42288780840) verifies the unbounded-depth stopping-index bridge and the initial n=6 family. Both runs have ordinary foundational axiom sets only, no `sorryAx` and no mock dependencies. The enlarged n=2,4 families have been locally signature-checked and are in the subsequent manual original-source CI; verify the newer run before calling them source-certified.

## The new all-depth invariant

`DyadicSixCone.lean` directly imports the genuine original-section inverse `BB6.Agent46.six_even_right_blank_reach_iff` and blank output invariant `BB6.Agent3.blank_section_odd_image`. Its all-natural theorem is

```lean
BB6.Agent19SixCone.dyadic_six_cone_no_blank
  (r a b u : Nat)
  (hu : 9 ≤ u) (hu4 : u % 4 = 1)
  (hb : b + 2 = 2^r*u)
  (hmass : (a + 2*b + 4*r) % 8 = 0) :
  ¬ BB6.Agent3.CReach a b
```

`CReach` refers to the actual blank-origin Machine C section map, initialized at exactly `(5,1)`. This source-exact forbidden region contains towers of **arbitrary inverse depth r**; there is no fuel, quotient, finite counter cutoff, or simulated-prefix assumption.

**Proof:** For `r=0`, the right counter is `b=u-2≥7`, is odd, and `(a+b)%4=1`. The original section image theorem forbids every such post-initial output; the pair differs from the true initial `(5,1)`. If `r>0`, then `b` is even and at least six. The congruences exclude both `(a+b)%8=0` and `=7`. Hence the genuine, *unique* source predecessor has coordinates `(a+b-2,(b-2)/2)`. It satisfies the identical cone hypotheses at exponent `r-1`:

```text
((b-2)/2)+2 = 2^(r-1)*u
(a+b-2)+2*((b-2)/2)+4*(r-1)
   = a+2*b+4*r-8.
```

The predecessor is therefore unreachable by the induction hypothesis, proving unreachability of the current pair. Its weighted mass `a+2b` decreases by exactly four at every inverse step.

## Unbounded low-target tower

The [source-verified `DyadicLowTower.lean`](DyadicLowTower.lean) pulls back every target `(1,k)` with

```text
n ≥ 2,       n even,
u ≥ 9,       u ≡ 1 (mod 4),
3k = 2^(n+2)*u + 1
```

through a genuine unique odd/odd source inverse to the preceding dyadic cone, proving `¬CReach 1 k`. Explicitly, the unique predecessor is

```text
a = (k-3)/2,
b = 2^n*u-2.
```

These satisfy `b+2=2^n*u` and `(a+2b+4n)%8=0`. The incoming odd/odd gate has `(1+k)%16=12` and `k≥5`; the exact original-source `BB6.Agent3.oddodd_lowval_blank_reach_iff` provides the predecessor equivalence. All values of `n`, including arbitrarily large even integers, are covered symbolically.

## Constructive low stopping-index families

The actual Machine C first stopping family is the **independent exact equation**

```text
k + 3m + 4 = 2^(2m+3).
```

For any `n≥2` even, `m≥n+4`, `r≤9`, the additional integer identity

```text
9m + 13 + 5*2^(n+2) = r*2^(n+4)
```

forces that stopping counter into the forbidden tower. Indeed, write `Q=2^(n+2)`, `T=2^(2m-n+1)`, so the stopping equation implies

```text
3k = Q*(3T + 5 - 4r) + 1.
```

The natural integer `u=3T+5-4r` is at least nine, with `u≡1(mod 4)`, because `m≥n+4` makes `T` a sufficiently large power of two. The original-source Lean lemma in [LowTowerFamilies.lean](LowTowerFamilies.lean) is `BB6.Agent19SixCone.low_linear_stop_no_root`. [Original-source CI 42288780840](https://github.com/FlareZ123/bb6/actions/runs/42288780840) verified this lemma with only `[propext, Classical.choice, Quot.sound]` axioms.

The identity has three convenient constructive seed triples `(n,m,r)`:

| n | m | r | k modulo `2^(n+4)` | Context |
| ---: | ---: | ---: | ---: | --- |
| 2 | 11 | 3 | 27 modulo 64 | Existing source-certified low exclusion by Agent21 |
| 4 | 219 | 9 | 107 modulo 256 | Existing source-certified low exclusion by Agent21 |
| 6 | 539 | 6 | 427 modulo 1024 | This invocation, [Low427Source.lean](Low427Source.lean) |

Define `m_{t+1}=64*m_t+91`, with `m_0` any of these three seeds, and `n_t=n_0+6t`. The same `r` works for every `t`, because

```text
9*(64m+91)+13+5*2^(n+8)
  =64*(9m+13+5*2^(n+2)).
```

Therefore the source theorem excludes every exact low stopping gateway at each indexed `m_t`, with **unbounded inverse depth** `n_t`. The recurrence produces:

| n | m | Implied k residue | Source admissibility |
| ---: | ---: | ---: | --- |
| 2 | 11 | 27 mod 64 | Previously known |
| 4 | 219 | 107 mod 256 | Previously known |
| 6 | 539 | 427 mod 1024 | New source certificate |
| 8 | 795 | 1707 mod 4096 | New all-depth family |
| 10 | 14107 | 6827 mod 16384 | New all-depth family |
| 12 | 34587 | 27307 mod 65536 | New all-depth family |
| 14 | 50971 | 109227 mod 262144 | New all-depth family |

The three original index seeds generate every even depth `n≥2` by selecting the appropriate residue modulo six and taking `t≥0`. The recurrence has strictly increasing natural terms; thus this supplies infinitely many distinct excluded stopping indices. The parameterized `odd_gate_dyadic_tower_no_blank` theorem is broader because it excludes **every** target satisfying its explicit divisibility equation, beyond these representative low stopping indices.

**Reproducible original-source Lean paths:**
- [DyadicSixCone.lean](DyadicSixCone.lean): arbitrary-depth inverse-cone proof.
- [DyadicLowTower.lean](DyadicLowTower.lean): odd/odd target transport.
- [LowTowerFamilies.lean](LowTowerFamilies.lean): low stopping arithmetic and explicit periodic-index recurrence.
- [Low427Source.lean](Low427Source.lean), [Low622Source.lean](Low622Source.lean): two independent seven-step uniform low-counter cylinders.
- [Manual original-source workflow](../../.github/workflows/agent19-c-odd-dyadic.yml).

## Finite quotient comparison and novelty boundary

The established M512 original-CLine quotient (67,633,152 abstract nodes; 27,858,704 reachable abstract nodes) **admits** the first-family layer cells `(a,k,c)=(1,427,0)` and `(1,171,0)` modulo the respective M512 coordinates. For the n=8,10,12,... high-depth representatives, `k%512=171`; the abstract cell is admitted despite the new true-source exclusion. This distinguishes the method from merely recovering a finite quotient's unreachable residue.

Original-source Lean proof is a rigorous mathematical claim **within the repo's already source-verified Machine C section semantics**. It establishes no new result for the other six-state holdouts, no finite bound on remaining Machine C stopping indices, and no value for BB(6). Existing separate Agent21 source-certified n=2,4 exclusions are acknowledged and unified. External publication novelty remains unreviewed; the general dyadic cone and extension to arbitrary even n should be compared with other inverse methods before promotion to `results/`.

**Next important direction:** combine this unbounded-depth cone with Agent11's exact low stopping predecessor fibres and source-authentic high-family bounds, then try to close a whole remaining unbounded stopping family, rather than accumulating isolated finite congruence classes. The source's remaining high family remains independently infinite.
