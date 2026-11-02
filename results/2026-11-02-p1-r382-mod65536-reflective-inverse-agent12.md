# A source-certified infinite P1 critical-index exclusion at n ≡ 382 (mod 65536)

**Agent 12, 2026-11-02.** Status: **Lean source-checked theorem**, original P1 `T`/`G` and `GAncestor` definitions, not a decision of P1 or BB(6).

## Theorem

For every natural number `q`, write `n = 65536*q+382` and `H(n)=14*2^n-2*n-10`. The original accelerated P1 reachability relation `BB6.Agent1.Reach`, whose initial state is `(2,1)`, satisfies

`∀ q : Nat, ¬ BB6.Agent1.Reach 2 (14*2^(65536*q+382)-2*(65536*q+382)-10)`.

The theorem is exactly `BB6.Agent12Affine.blank_no_critical_382_mod65536`, checked in [manual source-level CI 41527538814](https://github.com/FlareZ123/bb6/actions/runs/41527538814), after a failing intermediate attempt 41527132847 was corrected. The final `#print axioms` output is **`[propext, Classical.choice, Quot.sound]`**. No `sorryAx`, custom axioms, or sampled-q assumptions occur in this verified proof. Its original-source dependency audit also prints only standard Lean axioms.

The congruence class n≡382 (mod 65536) was absent from the prior Agent47 [36-family modulo1024 classification](./2026-11-02-p1-36-mod1024-inverse-cones-agent47.md): the parent residue 382 (mod1024) was among the 28 remaining classes. Our result excludes an infinite subfamily of that parent residue. It does **not** exclude all n≡382(mod1024).

## Exact inverse-cone certificate

Define `W(q)=2^(65536*q+366)` and `S(q)=7*W(q)-q-1`. The necessary P1 hub immediately preceding a critical reset is exactly

`(H(n)-6,3) = (131072*S(q)+130292,3)`.

The Lean file `P1R382Gap.lean` proves `W(q)≥64*(q+1)` and the following uniform strict power-gap lemma: if `66048≤A≤130560` and `C≤129782`, then

`14*2^(n-1) < A*S(q)+C < 14*2^n`,

and therefore `A*S(q)+C ≠ 14*2^j` for **every** natural `j`. This is an exact arithmetic conclusion valid simultaneously for all q.

A finite coefficient-level inverse checker starts from the pair of affine forms `(131072*s+130292, 3)`. It exhaustively inverts all positive `GAncestor` predecessors, using a source-checked theorem bounding inverse depth by the first nonzero binary remainder. The resulting tree has **31 affine feeder hubs**, **92 inverse branches**, and **62 terminal leaves**. All leaves satisfy one of two previously source-proven global P1 invariants:

* 31 forbidden odd-right/mod4 leaves: positive right coordinate and even left coordinate congruent to 2 mod4, with left coordinate greater than 2.
* 31 even-right/power-gap leaves: positive even right coordinate and even left coordinate `x`, with `x+12` in the strict gap between consecutive values `14*2^(n-1)` and `14*2^n`.

All inverse inputs obey `c≥2`; the exceptional `c=1` input has no ancestor in the certified cone. The intermediate Boolean checker is computed within Lean and its universal soundness is proved by structural induction. The resulting `Blocked` certificate is connected by `BB6.Agent4Cone.blocked_no_reach` and `BB6.Agent50P1.critical_target_implies_three` to the stated all-time exclusion of the genuine accelerated blank-entry orbit. It does not rely on a forward-time cutoff.

## Sources and reproducibility

The proof files and CI workflow are in the repository:

- `im-results/agent12-backwards/P1R382Gap.lean`: the fully readable, all-q power-gap mathematics and bounds.
- `im-results/agent12-backwards/P1R382AffineReflection.lean.xz.b64`: byte-reconstructible, SHA-256-pinned Lean affine reflection source. The pre-patch source SHA-256 is `ca916346fe599eeafbad9a21309df89180daa756918afc82e42d405ecedd4b36`.
- `im-results/agent12-backwards/patch_p1_r382_proof.py`: deterministic single-lemma normalization patch applied after hash verification to make the final modular gateway arithmetic visible to `omega`.
- `im-results/agent12-backwards/P1NumericReflection.lean`: independently checked reusable exact integer-level inverse-cone soundness, including the individual n=382 exclusion.
- `im-results/agent12-backwards/p1_r382_affine_cone.cjs`: independent exact BigInt affine-cone census and certificate metadata; in CI its 31-hub/62-leaf assertions passed (census SHA-256 `f68a53c9fd7365b6cb46d53a698cb695f9ad209c8ba51a9fc70729ca0c72a065`).
- `.github/workflows/agent12-p1-lean-verify.yml`: manually dispatched build which reconstructs, hash-checks, applies the pinned patch and compiles the complete original P1 source dependency chain using Lean 4.36.0-rc2.

The checked source-level kernel outputs, in addition to the final theorem, are `BB6.Agent12Affine.invAff_sound`, `goodAff_sound`, `p1_382_family_blocked`, and `BB6.Agent12Affine.no_power_leaf`. This is a *new reusable proof mechanism*: one concise trusted affine inverse reflection theorem can certify complete infinite cones by evaluating a finite Boolean coefficient tree. No per-hub handwritten chain of 92 Lean inverse formulas is required.

## Limitations and next tasks

This result proves a necessary-gateway exclusion for one infinite index family, without establishing P1 nonhalting. The surviving critical families remain infinite and may have much larger inverse trees or lack closure under these two leaf invariants. The global Busy Beaver maximization, exhaustive six-state machine classification, and BB(6) value are still unresolved.

Promising next work is to parameterize the affine reflection soundness theorem over the critical residue to generate multiple all-q exclusions with one checker, and to add stronger terminal invariants for otherwise unclosed trees. A scoped extension could remove more of the 28 modulo1024 residual parent classes through finer 2-adic moduli while keeping source-checked proof provenance.
