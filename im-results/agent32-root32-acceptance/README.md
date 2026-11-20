# U5B2Root32 local acceptance and proof repairs

## Status

The patched `U5B2Root32` import closure compiles successfully under Lean 4.36.0-rc2. The complete closure contains **49 project Lean modules**.

The source snapshot used for the full local closure run was repository commit `bbc1d6080634b2186ad9ca1ebd2035449706a035`. The subsequent main-branch commit `a91219071daa3e78a6f1f531badf0f9df877c060` changed only a JavaScript generator, not Lean sources. The root proof repair was committed as `39789de9c739984d6a499bc158f9a9d81c7f0a54`.

## Reproduction

With Lean 4.36.0-rc2 installed:

```sh
python3 tools/lean_compile_closure.py \
  im-results/agent3-c-bounce-inverse/U5B2Root32.lean \
  --workdir /tmp/lean-closure-b2-root32-current \
  --jobs 4 \
  --lean /path/to/lean-4.36.0-rc2-linux/bin/lean
```

Observed result:

```
[lean-closure] SUCCESS: compiled 49 project modules from 1 root(s)
```

This is a full source-closure compile, not a CI-only check. The exact local toolchain was `Lean 4.36.0-rc2`.

## Repairs

The original root module failed elaboration despite its 48 imported project modules compiling. The root proof repairs:

- Use explicit ex-falso elimination in the impossible divisibility branch.
- Remove tactics that ran after their goals had already closed.
- Replace a `by_contra` use unavailable in this Lean-core environment with explicit case analysis.
- Make the exponent type explicit in `Nat.pow_dvd_pow`, preventing an unconstrained exponent from being inferred.
- Replace a failed associativity-only normalization with arithmetic normalization.
- Replace the looping modulo simplification in `p4_root32_u_parameter` with a controlled modulo reduction and an explicit residue/quotient argument.
- Replace the expensive `p4_sum_mod64_of_root32` arithmetic search with explicit modulo-64 reduction, followed by small cancellation lemmas.

The final two modular lemmas isolate the finite facts
`(x+32) % 64 = 0 → x = 32` for `x < 64`, and
`(19*a) % 64 = 32 → a = 32` for `a < 64`.

## Axiom audit

The root module's emitted `#print axioms` profiles for the key results contain no `sorryAx`. In particular:

- `blank_no_b2_root32_from_root_index`: `[propext, Classical.choice, Quot.sound]`
- `blank_no_b2_root32_from_exact_root_index`: `[propext, Classical.choice, Quot.sound]`
- `p4_root32_u_parameter`: `[propext, Quot.sound]`
- `p4_sum_mod64_of_root32`: `[propext, Quot.sound]`

The root source also contains no explicit `sorry` or `admit` tokens. The use of `Classical.choice` in some upstream results is visible in the profiles; it is not a hidden proof placeholder.

## Scope and limitations

This accepts the patched formal proof chain for the stated root32 exclusion and its residual modular transfer. It does **not** determine BB(6), prove a global upper bound for all halting six-state machines, or establish that every other candidate family has been resolved.

The existing manual Agent 3 family workflow now has a `root32_only` input that runs this exact closure script after installing Lean. The corresponding remote CI run was dispatched after the local preflight; its result should be checked separately.
