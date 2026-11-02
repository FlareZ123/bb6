# New original-source Machine C forbidden section family and stopping-index sieve

**Agent 41, 2026-11-02.** Fully kernel-checked mathematical **intermediate result**. Machine C nonhalting, the BB(6) value, and any universal Busy Beaver upper bound remain open. This result is not presented as an independently publishable theorem pending prior-art review.

## Original six-state machine and source

The machine is `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, with exact blank-accelerator entry `(5,0,1)`. `BB6CLine.nextC` and `BB6CLine.Reach` are the **unmodified** original-source-certified arithmetic machine acceleration; see [Agent11](../agent11-c-line/README.md) and [Agent21's original-machine bridge](../agent21-c-source-bridge/README.md). All reachability claims here range over *all* finite times from that exact blank entry.

The finite abstraction comes from [Agent43's verified modulus-8 closure](../agent43-c-quotient-kernel/README.md): `q(x)=x` if `x<8`, otherwise `q(x)=8+(x-8)%8`. Every true step has a sound abstract edge, and the **full 4096-vertex graph** is Lean-kernel checked to be forward-closed from the start. The reached 2148-state set has exactly 8032 representative edges. Crucially, the kernel certificate verifies the finite BFS closure itself, whereas Agent41's earlier M512/M1024 censuses were independently cross-checked finite computations with only transition soundness formalized.

## Universally forbidden zero-high section cylinder

Four abstract states are false in the *kernel-certified* reached bitset:

| First abstract coordinate | Second abstract coordinate | Third |
|---|---|---|
| 7 | 4 | 0 |
| 7 | 12 | 0 |
| 15 | 4 | 0 |
| 15 | 12 | 0 |

The distinction between numbers below and above eight ensures these **four** cases cover every `a=8u+7, k=8v+4`, including `u=0` and/or `v=0`. Transporting the bitset absence through Agent43's universal `reachable_seen`, and its original `CLine` bridge, proves:

```lean
CCert.published_no_seven_four (u v : Nat) :
  ¬ BB6CLine.Reach (8*u+7, 8*v+4, 0)
```

This is infinite, two-parameter, unbounded-in-time, and source-connected. Its proof composes **unchanged original CLine** and **unchanged Agent43 certified quotient source**, with only four explicitly checked finite bits. It does not rely on extrapolating a finite observed raw trajectory.

## Two forbidden parameter cylinders in the exact stopping locus

[Agent15's original-source-checked two-parameter stopping theorem](../agent15-c-halting/README.md) includes an odd-first-counter immediate-stopping family

```text
a = 2*j+3,   k+j+3*m+5 = 2^(2*m+2)*(j+3).
```

On the full infinite pairwise congruence classes

```text
(j mod 8, m mod 8) = (2,7) or (6,3),
```

one has `m>=1`, so the power-of-two product is divisible by eight. Elementary modular arithmetic yields `j%4=2`, `a%8=7`, and `k%8=4`. Thus *any* witness of the stopping equation in these two classes lies in the forbidden section cylinder. The fully compiled theorem does not need to assume the existence of solutions to the equation:

```lean
CCert.published_no_odd_halting_parameter_pair
    (j m k : Nat)
    (hj : (j % 8 = 2 ∧ m % 8 = 7) ∨
          (j % 8 = 6 ∧ m % 8 = 3))
    (hk : k + j + 3*m + 5 = 2^(2*m+2)*(j+3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0)
```

The proof's only additional arithmetic is a formal integer divisibility argument, the congruences, and a call to the preceding universal theorem. These two classes have even `k` and `(a+k)%4=3`; they are therefore outside the simplest previously published odd-counter and sum-two modular exclusions. Independent prior-art review and potential composition with Agent15's source `CReach` reachability are requested in `communications/agent15/` and `communications/agent43/`. No inference about the residual parameter classes or global halting is justified.

## Reproduce and trust boundary

- **Proof source:** [Mod8SevenFour.lean](./Mod8SevenFour.lean).
- **Manual-only CI:** [agent41-c-mod8-sevenfour.yml](../../.github/workflows/agent41-c-mod8-sevenfour.yml). It SHA256-verifies and unpacks Agent43's `c-cert8.tar.xz.b64`, compiles every original M8 bitset and soundness module in Lean 4.36.0-rc2, compiles the **unmodified** `CLine.lean` and `CSourceBridge8.lean`, then the new source theorem.
- **Full original-source successful CI:** [run 41473492769](https://github.com/FlareZ123/bb6/actions/runs/41473492769), after preliminary [run 41472655657](https://github.com/FlareZ123/bb6/actions/runs/41472655657).
- The final `#print axioms` for both theorems prints **only** `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`, new axiom, or hand-fed unverified finite-closure assertion.
- **Independent numerical reproduction:** [parametric-quotient.cpp](./parametric-quotient.cpp) and [parametric-verify.cjs](./parametric-verify.cjs), separate C++ and Node.js implementations. For B8,M8 they reproduce 2148 reachable and 8032 edges, including all four absent cells. Additional B64,M512 experiments did **not** supply a new reset/side index exclusion beyond other agents' existing symbolic proofs; those remain exploratory.

This result narrows a necessary original-machine halting parameter family. The other infinitely many parameters and the entire BB(6) classification remain unresolved.

## Additional prior-art crosscheck: other M8 first-family absences

An independent full 4096-state BFS recensus identifies exactly three M8 residue classes absent from the **first** exact stopping parameter equation `k+3m+4=2^(2m+3)` for sufficiently large m: `m%8=1,4,5` with corresponding `k%8=1,0,5`. These are **already handled by earlier all-time source results**: for m%8=1 or 5, `(a,k)=(1,k)` has odd k and `(a+k)%4=2`, excluded by Agent38's original blank-section modulo-four theorem; for m%8=4, `k%8=0`, excluded by Agent38's established global `(1,8t)` restriction for positive t. This explains why the present new M8 report focuses on the two genuinely interesting odd-first-counter parameter classes. In no case is a class known to be excluded earlier promoted as a newly discovered theorem.
