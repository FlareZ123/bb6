# P1: arbitrarily long authentic predecessor corridors rooted at halting-critical hubs

**Status:** universal Lean theorem, currently undergoing original-source manual CI audit. The mathematical result is a structural obstruction to a fixed-depth inverse-cone tactic, without any claim of blank-start reachability, halting or nonhalting. Three new modules: [DeepCorridor.lean](./DeepCorridor.lean), [CriticalDeep.lean](./CriticalDeep.lean), [DeepPath.lean](./DeepPath.lean). The repository's existing Rank module supplies the exact length-indexed `Iter` relation.

## Universal construction

For every requested depth `L: Nat`, define

```text
n = 2^(L+4) - 2                 (so n ≡ 14 modulo 16)
K = 7*2^(n-(L+4)) - 1
B_i = 8*2^(L+2-i)*K - 12        (0 ≤ i ≤ L)
D_0 = 3
D_(i+1) = D_i + B_(i+1) + 10
```

The Lean arithmetic theorem `critical_root_eq` identifies the first hub **exactly** with the authentic P1 critical hub:

```text
(B_0,D_0) = (14*2^n - 2*n - 16, 3)
```

Every intermediate hub has `B_i ≥ 12`, `B_i % 4 = 0`, `D_i ≥ 3`, `D_i % 2 = 1`. In addition `B_i = 2*B_(i+1)+12` and the real `BB6.Agent1.T` transitions satisfy, for every `i<L`,

```text
T(B_(i+1), D_(i+1))
  = some(B_(i+1)+3, D_(i+1)-2)

T(B_(i+1)+3, D_(i+1)-2)
  = some(B_i,D_i).
```

These equalities are kernel-checked directly after unfolding the unmodified P1 recursive `G` and `T`, not merely inferred from heuristic integer inversion. `corridor_path` composes them, and the main theorem is

```lean
theorem critical_arbitrarily_long_inverse_paths (L:Nat) :
    ∃ n a c : Nat,
      n=critIndex L ∧ 12≤a ∧ 0<c ∧
      BB6.P1Rank.Iter (2*L) a c
        (14*2^n-2*n-16) 3
```

The witness n grows doubly exponentially in L through the critical counter `2^n`. Its 2-adic index property `n+2=2^(L+4)` yields the asserted universal corridor. The construction is exact at every natural L, and does not depend on numerical samples.

## Why the construction matters

Previous agent4/45/47 P1 inverse-cone proofs close finite branches with either a **positive-left mod4 contradiction** (`a ≡ 2 mod4`) or a **positive-even-right power-shape contradiction** (`a+12 ≠14*2^j`). Our corridor's every hub has left divisible by four and odd positive right. Hence **all those intermediate hubs evade both terminal tests**. A strategy that tries to close the entire surviving `n≡14(mod16)` family by a single uniform *bounded number* of these two-step inverse expansions followed solely by those two leaf types faces arbitrarily deep valid corridor branches.

This challenges fixed-depth local-cone exhaustion, but it does **not** rule out a stronger global invariant that excludes some hub without further expansion. The synthetic starting state `(B_L,D_L)` need not be reachable from the actual blank-entry state `(2,1)`. Thus none of these paths proves that any critical gate is blank-reachable. Nothing here decides P1 or BB(6).

## Reproduction and next direction

Compile original `im-results/agent1-p1-map/PosEvenForm.lean`, then `Rank.lean`, `DeepCorridor.lean`, `CriticalDeep.lean`, and `DeepPath.lean` with Lean 4.36.0-rc2, `LEAN_PATH` containing the two corresponding directories. The workflow `.github/workflows/agent4-p1-cone2398.yml` is manual-only and compiles these against the authentic original source.

The next useful research objective is to identify a **forward blank-reachability** invariant that distinguishes these legitimate synthetic predecessors from the actual orbit. More residue-specific finite inverse enumerations alone cannot close these n values at bounded depth.
