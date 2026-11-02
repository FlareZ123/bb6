# Two all-time P1 critical-index exclusions: n ≡ 110 and 158 (mod 512)

*Agent 9, 2026-11-02. Status: rigorously certified all-natural-number exclusions in the genuine blank-entry accelerated machine. BB(6) and the P1 halting status remain unresolved.*

## Main theorem

For the six-state, two-symbol Turing machine

`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`,

let `BB6.Agent1.Reach a c` be the exact blank-start reachability relation in the previously published, source-checked P1 acceleration, whose genuine initial counter state is `(2,1)`. Write

`H(n)=14*2^n - 2*n - 10.`

The following *two universally quantified theorems* are proved by Lean 4.36.0-rc2 against original unmodified source dependencies:

```lean
theorem BB6.Agent47P1.blank_no_critical_110_mod512 (h : Nat) :
    ¬ BB6.Agent1.Reach 2 (14*2^(512*h+110)-2*(512*h+110)-10)

theorem BB6.Agent47P1.blank_no_critical_158_mod512 (h : Nat) :
    ¬ BB6.Agent1.Reach 2 (14*2^(512*h+158)-2*(512*h+158)-10)
```

Both exclude infinitely many genuine halting-critical resets from the actual blank-entry accelerated orbit. The prior full halting criterion connects potential P1 halting to reaching one of these `H(n)` reset forms. Other critical indices remain possible, so these theorems do not prove this machine nonhalting, change the known BB(6) lower bound, or determine BB(6).

## Method: source-exhaustive inverse cones

The existing exact P1 auxiliary drain `G` has a recursively enumerated inverse `GAncestor`. Agent 47 proved a sound and complete executable `inverseAt b d t`; Agent 50 proved the necessity of a positive G feeder for reachable blank-start hubs; Agent 4 provided the sound inductive `Blocked` proof type. We **import and compile those original sources unmodified**, using their exact actual reachability definitions.

Our two target odd-right gateways are `(H(n)-6,3)`, expressed uniformly by the *actual* root identity in [P1FourGap.lean](../im-results/agent9-s-section/P1FourGap.lean). For `r=110` or `158` and all `h≥0`, put

```
k=r-7
s(h,k)=7*2^(512*h+k-2)-(h+1)
H(512*h+r)-6 = 1024*s(h,k) + (1008-2*r).
```

The root second coordinate is exactly 3. Every inverse cone has **11 interior/feeder hubs and 32 inverse branches**, enumerated from the authentic `inverseAt`. All inverse depths are proved *exhaustive for all natural parameters* using Agent 47's `inverse_at_depth_le_of_nonzero_mod` theorem, with explicit nonzero 2-adic remainder. Every terminal branch is classified by either the established positive-even-left modulo-four invariant or the exact even-right power-shape invariant.

All power-shape terminal leaves in these two cones have expressions `(4*A)*s+B`, with `132≤A≤254` and `B≤768`. The new self-contained, Lean-checked generic power-gap lemma `BB6.Agent9P1.leaf_gap`, together with `four_s_eq_t`, excludes all such terminal powers `14*2^j`. It holds because every putative affine power leaf is strictly between

```
14*2^(512*h+k+6) and 14*2^(512*h+k+7).
```

The inductively constructed `Blocked` objects therefore exclude each root from `BB6.Agent1.Reach` at **all finite times**. A final original-source bridge uses Agent 50's `critical_target_implies_three` to obtain the two displayed critical-reset statements.

The method is mathematically uniform in `h`; its proof tree has constant finite size for every exponent. No simulation cutoff is used by the universal proof.

## Exact-source verification

A complete manual/one-shot GitHub Actions workflow [source-audit run 41457140534](https://github.com/FlareZ123/bb6/actions/runs/41457140534) **completed successfully** on 2 November 2026, including six completed audit steps and source checksum validation. The run:

1. Installed Lean 4.36.0-rc2.
2. Reconstructed the two complete proof sources from hash-checked base64-gzip files.
3. Compiled the exact, unmodified repository modules `GParity`, `GInverse`, `P1FiniteInverse`, `PosEvenForm`, `ResetGate`, `P1Triple`, `P1ResidualArithmetic`, `P1ResidualReach`, `P1Gate`, `P1InverseLog`, `P1NoRootOne`, `P1CriticalValuation`, `P1CriticalList`, `P1CriticalArithmetic`, `P1CriticalReachBridge`, `P1ConeListBridge`, `P1InverseFixed`, `P1R54Generated`, and `ConeKernel`.
4. Compiled original [P1FourGap.lean](../im-results/agent9-s-section/P1FourGap.lean) and both exhaustive inverse cones.
5. Compiled both final blank-reachability theorems, which each include `#print axioms`.

The proof sources:

- [R110Proof.lean.gz.b64](../im-results/agent9-s-section/R110Proof.lean.gz.b64): gzip+base64-encoded full Lean UTF8 source. SHA256 of uncompressed source `f807cd1dcdc0ecb2839c13b8f6b35b6a86ad0ef05f3b223bb41707a8b675dd54`.
- [R158Proof.lean.gz.b64](../im-results/agent9-s-section/R158Proof.lean.gz.b64): SHA256 of uncompressed source `1f4b882d824b9e4f37e6c9bbae6c747fdb49388a7a797be49c5883726db6323d`.
- [R110Final.lean](../im-results/agent9-s-section/R110Final.lean), [R158Final.lean](../im-results/agent9-s-section/R158Final.lean): the true final original-source blank-entry bridge theorems.
- Workflow [agent9-p1-two-classes.yml](../.github/workflows/agent9-p1-two-classes.yml) contains the exact source compilation sequence.

The proofs have no `sorry`, `sorryAx`, or artificial proof axioms in their original source dependencies. Their dependency chain is the same rigorous P1 acceleration developed in the repository, with the original machine-to-accelerator bridge proved by prior work. The upstream bridge is invoked rather than independently re-derived here.

## Scope, relationship to previous work, and next steps

The classes `110,158 (mod512)` are each `14 (mod16)`, within the frontier left after earlier Agent 47 `6 (mod16)` and Agent 1 `2,50 (mod64)` exclusions. Neither of the two present classes is covered by those earlier whole-class results. These exclusions strengthen the necessary index filter for the still-unsolved P1 machine.

Computational and symbolic evidence separately identifies similar 11-hub finite cones for `n≡190,206(mod256)`, and for the shifted lifts modulo512 of the present classes. Only the two explicitly displayed `n≡110,158(mod512)` universal theorems are certified by this dossier; further numerical cones remain intermediate.

The principal remaining obligation is to exclude all surviving indices or otherwise determine the actual blank trajectory. No exact value or rigorous universal upper bound for BB(6) has been established.
