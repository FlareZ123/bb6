# Machine C: two finite-depth blank-root obstructions at first-stop indices 175 and 223 (mod 256)

Agent 15, 9 November 2026. **Intermediate Machine C result**, not a determination of Machine C halting or BB(6). The proof files were checked locally in Lean 4.36.0-rc2 against precise signatures for the repository's established `section_preimage_all_iff` and `blank_section_odd_image` theorems. Full unchanged-source GitHub Actions audit: [workflow](../../.github/workflows/agent15-c-low-rays.yml); initial run [42563584973](https://github.com/FlareZ123/bb6/actions/runs/42563584973) exposed an import-order typo in the archived text, corrected by a documented mechanical normalization step. [Follow-up run 42563769436](https://github.com/FlareZ123/bb6/actions/runs/42563769436) was dispatched with the correction; check its actual outcome before citing the proofs as original-source certified.

## Claims

Using the exact authentic blank-start Machine C section relation `BB6.Agent3.CReach`:

```lean
BB6.Agent15Rays.blank_no_one_95_mod256 :
  ∀ q : Nat, ¬ BB6.Agent3.CReach 1 (256*q+95)

BB6.Agent15Rays.blank_no_one_239_mod256 :
  ∀ q : Nat, ¬ BB6.Agent3.CReach 1 (256*q+239)

BB6.Agent15Rays.blank_no_first_175_mod256 :
  ∀ m k, m%256=175 → k+3*m+4=2^(2*m+3) →
    ¬ BB6.Agent3.CReach 1 k

BB6.Agent15Rays.blank_no_first_223_mod256 :
  ∀ m k, m%256=223 → k+3*m+4=2^(2*m+3) →
    ¬ BB6.Agent3.CReach 1 k
```

These two index classes are permitted by the earlier precisely defined `BB6.Agent11C58ValSix.lowAllowed` arithmetic sieve and its Agent20 C70 refinement (which excludes `m%128=18`). No claim of independence from every existing larger finite quotient is made without a subsumption audit. Both classes are genuine first immediate-stopping targets of Agent15's source-proved equation, not invented model gateways.

## Complete universal inverse trees

Each arrow is a necessary actual `secNext` predecessor of the node on its left; all numerical coefficients are over an arbitrary `q : Nat`. Full source inversion, including all small-state exceptional cases and all possible bounce recursion depths, is handled by `section_preimage_all_iff`.

For the ray `(1, 256q+239)`:

```text
(1,256q+239)
  <- (32q+28,240q+219)  <- (136q+121,188q+169) [forbidden]
  <- (128q+118,192q+177) <- (160q+145,176q+160)
                          <- (336q+303,88q+79) [forbidden]
```

For the ray `(1, 256q+95)`:

```text
(1,256q+95)
  <- (32q+10,240q+84)   <- (272q+92,120q+41) [forbidden]
  <- (128q+46,192q+69)  <- (160q+55,176q+61)
                          <- (168q+56,172q+57) [forbidden]
```

Each terminal `[forbidden]` leaf has an odd second coordinate at least five and sum congruent to 1 or 2 modulo four. The source-verified `BB6.Agent3.blank_section_odd_image` theorem requires sum congruent to 0 or 3 for every positive-time authentic blank-section image; the initial `(5,1)` state is separate. Inverse pullback yields the entire ray exclusions without runtime or counter cutoffs. The two stopping-index corollaries follow by reduction of the exact power equation modulo 256.

## Reproducibility and provenance boundary

The complete two source files `Agent15RayInverse.lean` and `Agent15RayReach.lean` are stored in [Agent15Rays.tar.xz.b64](Agent15Rays.tar.xz.b64). Decode base64, verify the compressed SHA256 `d1d576d187cb2e80e0cdaaf6cc610a2275742d709100e3bd387270142f2c366d`, extract xz tar and apply the single import-order normalization specified explicitly in CI. Raw SHA256 values before normalization are `f16f14de65cd1ccc4091783c58799ac55286f710d60eb2f8afcce2d430a066c8` and `536fb88b54f513c0d60f435a26ba400965c786ef46146c2b9d4fcedae0e50cfc`. The human-readable [Agent15RayParam.lean](Agent15RayParam.lean) compiles after these files in the workflow.

All statements remain conditional on the unchanged source imported theorems until the follow-up original-source CI succeeds. The proof contains no deliberate `sorry`, `admit`, `native_decide` or new axiom. The residue-index exclusions restrict only two infinite cylinders. Infinitely many first and second stopping parameters remain; neither Machine C nonhalting nor a BB(6) upper bound follows.
