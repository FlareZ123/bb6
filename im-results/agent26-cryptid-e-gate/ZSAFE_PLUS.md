# All-depth zero-ended marker A/p=2 closure and recursive source certificate

**Author:** Agent 26, 9 November 2026. **Classification:** intermediate mathematics, not a determination of BB(6), a new BB(6) lower bound, or a blank-origin nonhalting theorem.

## Original six-state machine and notation

Machine (A through F, tape symbols 0/1): `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.
Use Agent31's unmodified `CryptidBoundary.run`, where F/1 transitions to frozen halt state 6. Write `I_n(w)` for F scanning 0 with empty left tape and right `1^n w` followed by implicit zeros. The packet and regular section grammars are:

- `M(a,q,p;Y) = I_a((01)^q 0 1^p Y)`;
- `Z_m=(01)^m0`;
- `L(a,q,b)=I_a((01)^q 1^b)`.

Outputs are physically observationally equivalent (ObsEq), allowing implicit versus explicit rightmost blank zeros. This distinction is mathematically essential: finite right-hand lists differing by an extra terminal zero are not definitionally equal.

## New original-source theorem for every A/p=2 zero-ended marker depth

Source [`ZMarkerATwo.lean`](ZMarkerATwo.lean), theorem
`BB6.Agent26ZMarkerATwo.a_two_Z_regular`, proves **for all nonnegative integers** `k,q,r,m`:

```text
M(3k+3,q,3r+2;Z_m)
  --[T(k,q,r,m) primitive original transitions]-->
L(8k+7+2q+8r, 1, 2m+5)

T = 12k^2 + 49k + 54 + 4q + 4m
    + 12r^2 + (24k+55+6q)r.
```

The Lean theorem uses `twoCost` defined by Agent25's authenticated `wordCost` and `twoUnary` defined by the authenticated `wordInc`; the displayed polynomial is their algebraic expansion. Its exact output is observational, and the input's terminal zero is the *actual physical blank*. The proof factors the A input into `q` instances of code `10`, `r` instances of code `111`, and the terminal `110(10)^m`. Agent37's `complete_A_word_two_one_pairs` supplies the all-parameter exact source transition for the explicitly padded `110(10)^m0` section. Agent32's `source_init_pad` transfers the result to the actual implicit blank tape. No finite enumerative assumption is used.

This uniformly extends Agent36's original-source `a_two_z0_regular` (marker depth zero) to **arbitrary** marker depth. The underlying mixed-token A and `110(10)^m0` rules predate this composition and are credited to Agents35, 37 and 32, rather than claimed as new original primitive rules.

## Expanded terminating regular-reentry criterion

[`ZSafePlus.lean`](ZSafePlus.lean) extends Agent36's depth-recursive `safeZ` criterion to `safeZPlus`. Let `d = (normalizeWithCount c).2` be the original-source guarded B/E rank normalizer endpoint, starting from `c.a >= 4`. Existing `terminalSafe d` accepted:

```text
d.p % 3 == 1
OR (d.a % 3 == 0 AND d.p % 3 == 0)
OR (d.a % 3 == 2 AND d.q == 0).
```

The new `terminalSafePlus d` additionally accepts **all** terminal `d.a % 3 == 0 AND d.p % 3 == 2`. At zero marker depth, E with `p=0` has the already-certified regular return; at positive depth this E case consumes one marker level by Agent36's original-source `e_zero_drop_Z` and recursively tests the successor index. The combined rule is a terminating sufficient predicate; its proof uses induction on marker depth together with the existing well-founded packet normalizer.

`safeZPlus_source` establishes:

```text
c.a >= 4 AND safeZPlus(m,c)
  => exists T,a,q,b:
       run(T,M(c.a,c.q,c.p;Z_m)) ≈ L(a,q,b).
```

The theorem `old_safe_included` proves every earlier `safeZ` acceptance remains accepted. The strict extension is witnessed by `safeZPlus(1,(6,0,2))` and `NOT safeZ(1,(6,0,2))`. The more involved previously rejected example `safeZPlus(3,(52,1,0))` is kernel-reduced, and `residual_52_regular` composes its acceptance into a physical original-source regular reentry.

### Entire new infinite E branch

The previous E/p=0 drop has exact source equality:

```text
M(3k+4,q,0;Z_(m+1))
  --[12k^2+49k+50+4q]-->
M(8k+5,0,2q+7;Z_m).
```

When `k=3t+2`, the successor has index `24t+21`, divisible by three. The strengthened `all_A_Z_regular` now proves every A-index packet with `a >=4` and every `p` residue returns to regular L for arbitrary zero-marker depth. Therefore `e_zero_k2_all_Z_regular` certifies:

```text
For all t,q,m >= 0:
  M(9t+10,q,0;Z_(m+1))  -->  some L(a,Q,b).
```

This removes the earlier `q mod 3` restriction in the Agent36 E/k2 row. A stronger *explicit* two-section theorem handles the previously missing `q=3u+2` residue:

```text
M(9t+10,3u+2,0;Z_(m+1))
  --[Ecost(t,u) + twoCost(8t+6,0,2u+3,m)]-->
L(64t+16u+79,1,2m+5)

Ecost(t,u) = 12(3t+2)^2 + 49(3t+2) + 50 + 4(3u+2).
```

This is original source-level equality up to physically irrelevant terminal padding. It is a family of exact finite returns, not a global invariant.

## Certification

- Manual source-reconstruction workflow: [`agent26-zmarker-plus.yml`](../../.github/workflows/agent26-zmarker-plus.yml); restores Agent31/25 unmodified original sources and builds all imported original and bridge macros.
- [Successful full original-source Lean run 42558960146](https://github.com/FlareZ123/bb6/actions/runs/42558960146), Lean 4.36.0-rc2, checked all-depth A/p2 and safeZPlus, all A terminal cases, E/k2 unrestricted-q closure and exact E/k2 q2 composition. `#print axioms` reports only `[propext, Quot.sound]`; no `sorryAx` or native decision axiom.
- The later `residual_52_regular` wrapper is a direct theorem of `safeZPlus_source` and a checked decidable instance; independently re-running its updated end-to-end workflow is recorded separately when complete.

## Frontier and scope

`safeZPlus` is sufficient, not complete. The E-index `p=2` normalized packet remains a potentially exceptional exit, and some E/p=0 recursive tails may still reach it. This work does not prove those states halt or do not halt. It does **not** prove that the real blank-tape machine enters any covered synthetic `Z_m` section. The higher-value next step is to establish authentic blank-root reachability into this broadened invariant, or to resolve the E/p2 exceptional packet family with source-level equations that can compose to such a root.
