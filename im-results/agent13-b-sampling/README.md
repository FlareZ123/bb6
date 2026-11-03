# Machine B: a quantitative limitation of scalar reset-parity congruence rules

**Agent 13, normal invocation 2026-11-03. Intermediate method-limit theorem.**
The six-state BB(6) holdout remains undecided. These theorems concern the exact *scalar* map already authenticated against the original Machine B in the DeepMind Cryptids source. They do not exclude its true blank-origin reset sequence, prove nonhalting, or bound BB(6). No independent novelty review has occurred; do not promote this file to `results/`.

## Authenticated original-machine connection

The original rooted transition table is `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`, Cryptids holdout #710. Upstream proves the partial machine's entry at `A(3,0,0)` after 17 raw steps. Local source-connected Agent18 `im-results/agent18-b-cycle/ONE-DIMENSIONAL.md` documents the original-source **successful CI 41393439663** and exact reduction:

- `G(z)=3*floor(z/2)+4+5*(z%2)` for every natural `z`;
- `A(0)=3`, `Z(n)=G^[A(n)](0)`, and `A(n+1)=Z(n)+9-3*(Z(n)%2)`;
- original blank machine halts iff `∃n, Z(n)%2=0`.

The giant recursive **subsequence** `A(n)` is still unresolved. An unrestricted synthetic candidate `v` need not occur in that subsequence. Agent5 already proved and source-checked full-word finite 2-adic coding, aperiodicity, and parity-gap lemmas in `im-results/agent5-b-parity-runs/`; original full-source Lean CI [41493062011](https://github.com/FlareZ123/bb6/actions/runs/41493062011). The findings below apply this known mechanism to a specific **diagonal sample** and supply a quantitative refutation bound. No claim is made to invent the general Collatz parity-coding phenomenon.

## Kernel-verified theorem: explicit log-gap modular-rule falsifier

For `H(v) = (G^[v+6](0))%2` and positive modulus `m`, define the exact positive difference

```
D(N,m) = G^[N+6+m](0) - G^[N+6](0) > 0.
```

Theorem `diagonal_disagreement_bounded` proves **for every natural N and every m>0**:

```
∃ v, N ≤ v ≤ N + floor(log2 D(N,m))  ∧  H(v) ≠ H(v+m).
```

Thus even after any finite initial exception, no fixed congruence-class-only lookup can predict `H(v)` on *all* natural candidate payloads. The theorem supplies an explicit finite search horizon instead of an unbounded existential refutation. `mismatch_within_log2` is the more general base lemma: for `z<w`, the parity streams of `G^j(z)` and `G^j(w)` disagree at some `0≤j≤floor(log2(w-z))`. Its proof uses:

1. `2G(z)=3z+8+7(z%2)`, which gives `2*(G(w)-G(z))=3*(w-z)` when the two input parities agree.
2. Induction: matching the first `k` parity symbols implies `2^k | (w-z)`; the factor 3 is coprime to powers of 2.
3. `2^(floor(log2(w-z))+1) > w-z`, contradicting divisibility if all those parities agree.
4. Iteration composition and strict growth of `G` transport the witness to the candidate indices `v=N+j`.

A weaker source-independent theorem `diagonal_disagrees_arbitrarily_late` is also checked, as are `first_two_sample_values` and `synthetic_mod8_falsifier`. These are proven directly from a copied, literal `G` and `iterG`, with no extra source-level axiom.

## Exact finite falsification and boundaries

- `G^3(0)=19` and `G^25(0)=227091`: the first two genuine recursively sampled values are odd, so `A(1)=25` and `A(2)=227097`.
- `19 ≡ 91 (mod 8)`, yet `H(19)=1` and `H(91)=0`. Both 19 and 91 occur on the full scalar orbit `G^t(0)` at `t=3,6`; only 19 is presently a proved authentic nested reset payload. The example falsifies an unrestricted residue-only reset rule, **not** the true nested-blank condition.
- A stronger **finite empirical** scalar-orbit falsifier: `505 ≡ 100921 ≡ 57 (mod 64)`, but `H(505)=1` and `H(100921)=0`. These occur at full-scalar times `t=10,23`; neither is a proved genuine nested reset. This numerical pair is Python-regressed, not Lean-proved.
- The third genuine finite sample `G^227097(0)` is odd and congruent to **11 mod 16**, with bit length **132847**. This is a reproducible exact-integer computation; the earlier Agent5 work already kernel-certified its parity. No fourth sample or all-time conclusion is implied.
- The log-gap theorem is **unrestricted in v**. It leaves open any more subtle invariant that applies only to the genuine recursively generated set `{Z(n)}`, a thin subset of candidate payloads. It therefore does not change the holdout's classification.

## Reproduction, evidence, and provenance

Local Lean toolchain: **Lean 4.36.0-rc2**, reconstructed from the invocation's supplied archive; both complete source modules compiled directly in the kernel, with no `sorry` or `native_decide`. `#print axioms`: `diagonal_disagreement_bounded`, `parity_prefix_divisible`, and `mismatch_within_log2` depend only on `[propext, Quot.sound]`; the weaker `diagonal_disagrees_arbitrarily_late` uses standard `[propext, Classical.choice, Quot.sound]`. The two finite `decide` statements have no axioms.

Reconstruct files using the local `unpack.py` (exclusive lock plus atomic replacement, hash check), then compile in dependency order:

```text
python unpack.py
LEAN_PATH=. lean -o BSamplingLimits.olean BSamplingLimits.lean
LEAN_PATH=. lean BSamplingBound.lean
python check_samples.py
```

SHA-256 of exact uncompressed verified Lean sources:

- `BSamplingLimits.lean`: `190f39e449d2fa48427e1ba7063cd258bd44b923f639f10b9b325c04792c4423`
- `BSamplingBound.lean`: `1633d7e3454b4146c87af2d887ad2a49dc9a65b23466138439bab8fc84c84cea`

The local independent Python regression `check_samples.py` passes all expected checks. Source-to-original-machine equivalence relies on Agent18's earlier imported, source-CI-verified original-machine reduction; this new Lean pair independently copies the proven arithmetic function. **No new original-source CI validation was dispatched** during the reported GitHub Actions widespread startup failure ([Critic report](../../communications/broadcast/2026-11-03T1002Z_Critic-cross-workflow-ci-failure.md)). This source connection is therefore via the existing authenticated equality and inspection, not a new unmodified-source import proof.

## Next discriminating question

Can one establish a *true blank-sequence-sensitive* restriction on the inputs `Z(n)` that survives deliberately adversarial synthetic orbit values? In particular, prove or falsify a useful invariant of the two-scale diagonal map `z ↦ G^[z+6](0)` on the recursively generated `Z(n)` subset, beyond congruence classes of arbitrary synthetic `z`. Check preexisting Agent5/Agent18 parity results before attempting a duplicate all-word coding proof. A novel root decision still requires proving every `Z(n)` odd, or finding an even `Z(n)` with an authenticated raw halting runtime.
