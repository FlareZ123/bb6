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

## Formal lower bound for the two-leaf inverse-certificate calculus

`DepthBarrier.lean` now imports **the original** `BB6.P1Reduction.GAncestor` from Agent 1's `GInverse.lean`. It defines `Shallow fuel b d`, a deliberately **relaxed** depth-indexed form of the project's `Blocked` calculus: the `modLeaf` and `powerLeaf` hypotheses are identical, while `feeder` omits several additional original restrictions. This makes the shallow system **more permissive** than the existing proof strategy, so a nonderivability result for `Shallow` is a genuine lower bound for the corresponding restricted strategy.

The theorem `corridor_ancestor` proves the exact source `GAncestor.upper` witnesses at each link, matching the child coordinates `(2*k-4,v+4)` expected by the original feeder rule. The induction `corridor_requires_unbounded_depth` rules out a depth budget equal to the remaining corridor length. Budget-monotonicity `shallow_le` then gives the stronger theorem:

```lean
theorem critical_no_shallow_up_to (L fuel : Nat) (h : fuel≤L) :
    ¬Shallow fuel (14*2^(critIndex L)-2*(critIndex L)-16) 3
```

This is a **mathematical theorem about the inverse proof calculus**. It proves that no fixed depth bound works for all critical indices `n≡14(mod16)` if one uses only those two existing leaves and the complete G-feeder case. A proof using a new invariant or an entirely different constructor is outside this lower bound.

Original-source CI: [run 41440912345](https://github.com/FlareZ123/bb6/actions/runs/41440912345) verified the base depth barrier with standard Lean axioms and zero sorryAx. The stronger `critical_no_shallow_up_to` was locally Lean-verified using a definition-equivalent GAncestor import; its updated unmodified-source CI has been dispatched.

## Prior work and precise incremental contribution

**Important provenance correction after inspecting concurrent work:** Agent 27 had already source-proved authentic two-step upper inverse chains for critical `n=2^(k+3)-2`, and Agent 33 source-proved the much stronger universal upper-depth divisibility iff and all odd-modulus depth theorem (see `im-results/agent33-p1-upper-valuation/README.md`, successful [CI 41432909667](https://github.com/FlareZ123/bb6/actions/runs/41432909667)). Agent 45 independently proved arbitrarily deep **mixed-branch** inverse paths for the other unresolved `n≡2(mod16)` sector; see `im-results/agent45-p1-deep-two/README.md`. Thus the **mere existence** of our unbounded synthetic upper paths is already established prior art, and this document must not be cited as the discovery of that phenomenon.

What is distinct in this package is the all-state strict Lyapunov rank and constructive individual-state Reach decider, together with a direct, original-`GAncestor`-linked **formal lower bound on depth-indexed inverse proofs** using the project's existing modLeaf/powerLeaf/feeder architecture. The exact theorem `critical_no_shallow_up_to` establishes that for any `L` and `fuel≤L`, the root at `n=2^(L+4)-2` cannot be derived by that relaxed indexed calculus at budget `fuel`. This adds a proof-calculus nonderivability certificate to Agent27/33's stronger path-existence facts, while remaining an intermediate methodological result, not a new holdout decision.

The stronger no-shallow theorem was verified against **unmodified original source GAncestor and G,T** in [manual CI 41441274896](https://github.com/FlareZ123/bb6/actions/runs/41441274896). Kernel axiom audit reports only standard Lean axioms.

## Reproduction and next direction

Compile original `im-results/agent1-p1-map/PosEvenForm.lean`, then `Rank.lean`, `DeepCorridor.lean`, `CriticalDeep.lean`, and `DeepPath.lean` with Lean 4.36.0-rc2, `LEAN_PATH` containing the two corresponding directories. The workflow `.github/workflows/agent4-p1-cone2398.yml` is manual-only and compiles these against the authentic original source.

The next useful research objective is to identify a **forward blank-reachability** invariant that distinguishes these legitimate synthetic predecessors from the actual orbit. More residue-specific finite inverse enumerations alone cannot close these n values at bounded depth.
