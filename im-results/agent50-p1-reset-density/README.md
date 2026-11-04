> **STRICT ALL-RESET-COUNT STRENGTHENING, ORIGINAL SOURCE-CERTIFIED:** [manual Lean CI run 41775736722](https://github.com/FlareZ123/bb6/actions/runs/41775736722), job 126395536779, success, SHA256-checked original unmodified modules and new [ResetStrict](ResetStrict.lean.xz.b64), [ResetStrictBridge](ResetStrictBridge.lean.xz.b64). Source `BB6.Agent50Density.source_critical_wall_reset_density_strict` establishes `n+2≤2*(2*z+1)*Nat.log2(3*n+4)` for every genuine critical P1 affine-wall inverse cone, n≥14. The stronger `source_critical_wall_needs_three_resets` proves **for all n≥70**, every such source wall history has ≥3 positive-depth inverses, resolving the exactly-two-reset mathematical conjecture in [Agent28's draft](../agent28-p1-word-automaton/TWO-RESET-CANDIDATE.md) by a different proof. The proof preserves the root defect n+2, yielding a strict one-unit improvement in the logarithmic cost budget; the growth inequality `10*log2(3n+4)<n+2` is kernel-proved for all n≥70. Both final source theorem axioms are exactly `[propext, Classical.choice, Quot.sound]`, no mocks or sorry. Precise decoded source SHA256: `7540ccecc0e0f7e428afd5f6bc9b8a0b6ca8898d7226870c27942ea0555d3ea4` (ResetStrict), `ddd3c17788560e97afc9b5d51757c6db35972585fe25b40a497ade55a6cf3dc1` (ResetStrictBridge). **Original BB(6)/P1 open questions, exceptional c=1 exits, and high-cost exits remain open.** The older text below reflects the initial development, superseded by these original-source certificates. External novelty and independent referee review pending.

> **ORIGINAL-SOURCE LEAN CHECKED 2026-11-04:** The entire source bridge sketched below has now been proved and compiled on unchanged original P1 dependencies, in [manual CI run 41774968544](https://github.com/FlareZ123/bb6/actions/runs/41774968544), job 126393095617, head 2fdf820a414d51dd9d4efe2cf48805b043029c0b, success. Final theorem `BB6.Agent50Density.source_critical_wall_reset_density` axiom audit is exactly `[propext, Classical.choice, Quot.sound]`, no sorry or mock sources. Original Lean source (hash-checked after xz/base64 decoding) is [ResetBudget](ResetBudget.lean.xz.b64), [ResetSourceAlgebra](ResetSourceAlgebra.lean.xz.b64), [ResetSourceBridge](ResetSourceBridge.lean.xz.b64); exact respective source SHA256: `cfc5104ae546ee196995dbff7bb7e46082244f65dde07a1ffb86eb151d1bd0da`, `f145e33a241d46568e175266f6c238e20a6d286764eb015a4219911dbee7fe1b`, `7c5afd006bacb644465390fe3d1b02805995ea0631f1ef848b5e17e95de814d2`. The `CountCone` in the source theorem is *proved faithful* to each `OddCone` source edge and counts depth-t>0 inverse moves. Every `OddCone (14*2^n-2*n-16) 3 b d m` with n≥14 and b=4(m+n) has such a `CountCone` whose positive-depth count z satisfies `n≤2*(2*z+1)*Nat.log2(3*n+4)`. The older pending-bridge language below is retained as historical development notes and is superseded by this certificate. This remains a necessary wall restriction, without resolving any P1 halting root or BB(6). External novelty review is pending. The manual workflow is [agent50-p1-reset-density.yml](../../.github/workflows/agent50-p1-reset-density.yml).

# P1 reset-density bound (Agent 50, 2026-11-04)

**Status: intermediate result.** Exact abstract combinatorial theorem kernel-checked with Lean 4.36.0-rc2; its proposed connection to *unmodified original* `OddCone/inverseAt` has **not yet been constructed or checked**. Do not cite it as an original-source theorem or as a BB(6) decision. Work here is separate from Agent28's n≥70 two-reset candidate: this is an all-reset-count logarithmic lower-bound programme.

## Formal abstract theorem

The source-independent `ResetBudget.lean` defines `DefectPrefix n m z u N B`, a history stopped at the first cost crossing `2*m ≥ n`. It has the following exact local semantics:

* root `(m,z,u,N,B)=(0,0,0,n+2,n+2)`;
* upper inverse `t=0`: if `2*m<n` and `N=2*N'`, advance `m↦m+1,u↦u+1,N↦N'`, retaining `z,B`;
* positive-depth inverse `t≥1`, `l=t+1≥2`: if `2*m<n`, `M+N=2(n+m+2)`, `M=2^l*h`, and `N'+h=n+m+l+1`, advance `m↦m+l,z↦z+1,u↦0,N↦N',B↦N'`.

The Lean theorem `defect_prefix_budget` proves by induction **for every such history**, with `L` satisfying `3n+4<2^(L+1)`:

```
0<N, N≤n+m+2, B≤n+m+2, 2^u*N=B,
u≤L, m≤2*z*L+u.
```

Therefore `resets_needed_to_cross_half` proves, for every abstract half-cost-crossing history,

```
n ≤ 2*(2*z+1)*Nat.log2(3*n+4).
```

Here `Nat.log2` is the floor binary logarithm. This inequality is exact for all natural parameters under the displayed inductive hypotheses. The separate kernel theorem `power_gap_below_half` proves that for all `n≥14, 2m<n`,

```
3n+4 < 2^(n-m).
```

All three final theorem axiom audits from a local original Lean 4.36.0-rc2 executable are `[propext, Quot.sound]`; there are no sorrys, custom axioms, or imports beyond Std.

**Reproduction:** `ResetBudget.lean.xz.b64` decodes to xz-compressed UTF-8 Lean source. Decompress and compile with `lean ResetBudget.lean`. Decoded source SHA-256 `cfc5104ae546ee196995dbff7bb7e46082244f65dde07a1ffb86eb151d1bd0da`. Compressed-base64 file SHA-256 `e86b3dd81692d453e50154f193c7032660868b1aa8c88dd70359ef891439d36a`.

## Source-connected conjectural corollary (paper derivation, pending Lean bridge)

The existing original-source `OddWordSourceBridge.lean` and `OddWordCost.lean` certify that, for `n≥14`, any odd inverse P1 critical history reaching its affine wall `b=4(m+n)` has cumulative cost `2m≥n`. Thus the abstract bound would imply the **all-n necessary reset-density bound**

```
2*(2*z+1)*floor(log2(3*n+4)) ≥ n
```

for the number `z` of positive-depth `inverseAt` steps in a source history reaching the wall, provided the abstract transport below is formalized. Consequences would include at least 6 resets for `n=200`, at least 23 for `n=1024`, and at least 79 for `n=4096`. Asymptotically this forces `z=Ω(n/log n)`, unlike any fixed-reset exclusion. It has no control over high-cost even exits or the `c=1` exception.

The proposed transport uses the already published source equations. Write `P=2^n`, `K=7P-n-3`, and at an odd-cone hub use `d=2D+1`, `F=(b+12)/2`, cumulative inverse cost `m`. Original `odd_cone_mass` yields `F+D+m=K+2`; `inverseAt_iff_power_mass` yields `2^(t+1) D'+m=K+D`.

Maintain a positive odd integer coefficient `C≤2^m` and positive defect `N≤n+m+2` with `F+N=7*2^(n-m)*C` while `2m<n`. At the root `C=1,N=n+2`. For `t=0`, exact source equations yield `F=2F'`; since `2m<n` gives an even power on the right, `N=2N'` and `C'=C`. For `t≥1`, let `l=t+1`, `M=2(n+m+2)-N`, `V=2^(m+1)-C`. Agent28's source-independent `defect_reset_input_identity` yields `2^l D'+M=7*2^(n-m)*V`. Since `0<M≤3n+4<2^(n-m)`, Agent28's `power_remainder_division` proves `2^l|M` and `2^l≤M`, so `m+l<n`. Put `h=M/2^l`, `N'=n+m+l+1-h` and `C'=2^(m+l)-V`; the `defect_reset_output_identity` gives `F'+N'=7*2^(n-m-l)*C'`. The natural positivity/bounds and oddness of `C'` follow from `l≥2`, `C≤2^m`, and `M≤2(n+m+2)`. These are the exact hypotheses of `DefectPrefix`.

**Source-bridge obligation:** implement the invariant as an induction over the original `OddCone` path up to its *first* half-cost crossing, preserving the original guards, accurate edge count, and `C,N,F` state. The argument above is not yet a Lean-checked connection and should be independently falsified before a source claim. The abstract theorem itself makes no assertion about original Turing-machine executions or blank reachability.

## Validation and limitations

An independent exact-integer normalized-grammar probe checked this budget invariant along finite source-compatible odd-inverse prefixes for `n=14,30,46,62,70,78,94,110,126,142,158,174,190,206,222,238,254,270,286`, stopping at the first half-cost crossing; no violation appeared. These sample tests are exploratory. The mathematical claim above rests only on the kernel-checked *abstract* theorem. The source extension, full-tree completeness and novelty over outside literature remain unverified.

**Highest-value next action:** prove or refute the original-source transport and run manual pinned Lean source CI. Compare with Agent28's n≥70 exactly-two-reset result. Do not treat this bound as a machine decision.