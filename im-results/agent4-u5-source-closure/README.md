# U5 q=0 source-only closure

**Status: Lean draft; exact-source preflight pending.** No theorem in this directory is yet claimed as compiled or source-certified.

## Contribution

`U5Q0SourceOnly.lean` contains formal proof drafts for two all-time exclusions in the exact original Machine C section orbit:

- `X_t=(44t-1,42t-1)) is blank-unreachable for every `t=32n+19`.
- `X_t=(44t-1,42t-1)) is blank-unreachable for every `t=128n+99`.

It also supplies drop-in replacements for the q=0-parent lemmas on the existing U5 residual cylinders `w=21 (mod 32)` and `w=37 (mod 128)`.

The intended proof route does **not** use the finite M16 quotient certificate. It uses the exact source-parent fan `q0_oddodd_parent_fan_iff`, the complete even/even source-parent fan, the unique even/odd valuation-two parent theorem, and the existing blank-root odd-right sum-one and odd/odd sum-two image exclusions.

## Proof structure

For `t=32n+19`, the fan equation `43t-1=4^q U`, with `U` even, and `(43t-1) mod 32=16` force `q≤1`.

- At `q=0`, the parent is `(1376n+814,1360n+804)`, an even/even state with sum `2 mod 4`. The complete source-parent fan leaves only its direct parent `(2736n+1616,680n+401)`, which has odd right coordinate and sum `1 mod 4`.
- At `q=1`, the parent is `(344n+202,1876n+1107)`, which itself has odd right coordinate and sum `1 mod 4`.

For `t=128n+99`, `(43t-1) mod 64=32` forces `q≤2`.

- At `q=0`, the even/even sum-two parent again reduces to a forbidden odd-right sum-one state: `(10944n+8456,2720n+2101)`.
- At `q=1`, the parent `(1376n+1062,7504n+5797)` has a unique original-source parent `(4440n+3427,5972n+4611)`, which is odd/odd with sum `2 mod 4`.
- At `q=2`, the parent `(344n+264,8020n+6193)` is odd-right with sum `1 mod 4`.

The two residual wrappers reuse the exact congruences already derived from the U5 equations: `t=19 (mod 32)` on `w=21 (mod 32)`, and `t=99 (mod 128)` on `w=37 (mod 128)`. The exact two-step pullback from `(64t+5,32t+3)` to `X_t` is retained.

## End-to-end root connection

`U5SourceOnlyHighStop.lean` composes the `w=21 (mod 32)` source-only q=0 closure with the existing exact U5 six-even-right chain and the original `mzero_first_two_reach` / `m0_odd_ray_parent` source-parent lemmas. Its main draft theorem is:

```lean
blank_no_high_m0_u5_w21
```

It excludes the actual blank-section reachability of the high m=0 stopping root
`(2*(39+64*s)+3, 3*(39+64*s)+7)` under the exact U5 residual equations and `w=21 (mod 32)`. The dependency chain contains no finite quotient certificate. The proof route is:

1. high stopping root `-> A_s` by `mzero_first_two_reach`;
2. `A_s` has only the exact `L_s` and `B_s` source parents;
3. `L_s` is excluded by the existing mod-8 image invariant;
4. `B_s` pulls back along the exact six-even-right chain to the terminal y=3 state;
5. the terminal y=3 parent fan has q=0 (the new source-only theorem), q=1 (odd-right sum-two exclusion), or q≥2 (contradicts `m+1=1 (mod 8)`).

The module also drafts `u5_residual_nonempty`: for every natural w it constructs natural s,m satisfying the two residual equations. The proof uses `2^210 ≡ 1 (mod 211)`, `2^201 ≡ 68 (mod 211)`, and `2^r ≥ r+1` to obtain `s ≥ 27w+1` and `m ≥ 24w`. The theorem `u5_residual_s_strict_mono` proves that s is strictly increasing with w for any two residual solutions. Consequently, `every_w21_residual_has_unreachable_root` packages w=32n+21 as an explicit infinite sequence of pairwise distinct nonempty residual instances whose high m=0 roots are excluded.

A further arithmetic consequence is that every such residual has `s=293 (mod 512)`, hence the stopping-root index `j=39+64s` satisfies `j=18791 (mod 32768)`, equivalently `t_root=(j-7)/32=587 (mod 1024)`. This containing residue class is disjoint from the four previously source-certified m=0 classes `j=1895 (mod 2048)`, `j=359 (mod 8192)`, `j=5479 (mod 16384)`, and `j=10599 (mod 32768)`.

**Important density qualification:** the U5 residual equations generate only the specific exponentially growing sequence indexed by `w_n=32n+21`; they do not generate every root index in `j=18791 (mod 32768)`. The construction has `r_n=201+3360w_n=70761+107520n`, `s_n=(5*2^{r_n}-129)/211`, and `j_n=39+64s_n`. Thus this is an additional infinite, pairwise-distinct sparse subset inside a new residue class, not a fifth full arithmetic-progression exclusion. No density increment is claimed: the previously certified coverage remains `23/512` of the odd root-parameter ray. Since `j_n` grows exponentially, the constructed sequence itself has natural density zero.

This is the intended source-to-root connection, including nonvacuity and an additional infinite sparse family lying inside a new disjoint residue class, but the new high-stop module is still uncompiled and is not yet a certified theorem.

## Why this matters

The current M16 route excludes the same q=0 source-parent fan by projecting its possible parents into absent cells of the kernel-checked finite quotient. This draft replaces that finite-quotient dependency on these two cylinders with direct original-source predecessor arguments. It therefore offers a smaller and more transparent route for the same two infinite U5 subfamilies.

This does **not** close the remaining U5 odd residue classes, the full Machine C stopping criterion, or BB(6).

## Verification and next step

Lean 4.36.0-rc2 has now been reconstructed and launched locally. The uploaded ZIP contains a `.tar.zst` payload, so it required an additional Zstandard tar extraction after concatenating the two uploaded parts.

An isolated local preflight of the exact arithmetic declarations copied from `U5SourceOnlyHighStop.lean` succeeded:

- `u5_residual_nonempty`
- `u5_residual_s_strict_mono`
- `u5_high_root_parameter_residue`

Their isolated `#print axioms` profiles were respectively `[propext, Quot.sound]`, `[propext, Classical.choice, Quot.sound]`, and `[propext, Quot.sound]`. This checks the arithmetic proof fragments, including the modular exponent calculations and residue inversion, but **does not compile either repository module or certify the source-parent/root chain**.

The full source files have not yet been staged in the local runtime. Preflight must compile the **complete exact import closure**, not only the two new files: in particular `U5Q0OddOddFan.lean` (previously marked an uncompiled source-fan draft), `U5Y3M8.lean`, `U5Y3ParentFan.lean`, `U5M8Q0Partial.lean`, `U5Q0M16Residual.lean`, and the original-source predecessor/image modules they import. The `U5Q0M16Residual` module is used only for elementary residual congruences; it does not import `CCert` or a finite quotient.

Per the current research-direction instruction, do not dispatch CI until this exact changed-source dependency closure has passed a focused local Lean preflight. After that, run a single focused manual source workflow with axiom prints for all exported declarations; if successful, integrate the w=21 source-only theorem into the maintained U5 high-stop dossier in place.
