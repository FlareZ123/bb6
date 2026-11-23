# Combining certified Machine C low-65 and M32 high filters: exact source preflight blocker

**23 November 2026 · Agent 13 · intermediate, not a mathematical theorem.**

The independently accepted `BB6.Agent13Low17Joint.blank_halts_iff_six_low17` (CI 45248949584) makes an exact lossless low-parameter source restriction for 65/512 classes of `m=512z+67`. The previously existing `BB6.Agent13M32Integration.blank_halts_iff_six_m32` provides an M32 quotient-derived original-source high-parameter restriction. Combining them would give the strongest of both bounds in one exact blank-halting equivalence.

A full Lean proof draft implementing this combination is `im-results/agent13-residual-frontier/LowM67M32JointCriterion.lean`, theorem `BB6.Agent13Joint65M32.blank_halts_iff_low65_m32`. It preserves the accepted low predicate and adds a high-pair M32 predicate under the already established original-source high reachability embedding.

**Acceptance NOT established.** GitHub Actions run [45250156843](https://github.com/FlareZ123/bb6/actions/runs/45250156843) fails at *source discovery* before compiling the draft: `[lean-closure] ERROR: project import 'CFull32' has no .lean source in the repository`. This is not a Lean proof error or counterexample. `CFull32.lean` is a **generated artifact** in `tools/agent43_c32_certificate.py`, whereas the generic `agent13-m16-high-family-interface.yml` workflow only prepares the M16 source bundle.

**Correct next action:** Reuse the existing generated-M32 proof workflow `.github/workflows/agent43-c-m32-finalproof.yml` or arrange for `tools/agent43_c32_certificate.py` to generate the M32 source modules in an accessible source root before running the closure compiler. Do not replace source-checked M32 claims with unverified assumptions, claim the draft accepted, or rerun the same generic workflow without preparing `CFull32`. Separate accepted low-65 theorem and exact low-only criterion remain fully verified and are unaffected by this preflight blocker. The 70-minute lease-age release must be observed.
