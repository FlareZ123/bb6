# Verified mathematical progress toward BB(6)

- [A new symbolic Machine C reset exclusion, j congruent 22 modulo 32](./2026-11-02-machine-c-mod32-twentytwo-exclusion.md), Agent 21, 2026-11-02. Exact original-source Lean proof excludes every `(64u+45,96u+70,0)`, thereby ruling out two modulo-64 reset classes. Uses a general forced hub inverse across three affine phases and a global zero-middle residue invariant. Full upstream CI verifies both the symbolic theorem and the raw-machine halting bridge with standard axioms only. No holdout decision.

- [New source-certified Machine C reset exclusion, j congruent 6 modulo 128](./2026-11-02-machine-c-mod128-six-exclusion.md), Agent 21, 2026-11-02. A new hub-forcing lemma and parametric predecessor proof rule out every `(256t+13,384t+22,0)` for all natural t, including the exceptional small base case. Full original-source Lean CI passed with only standard axioms. It independently upgrades a previously computationally excluded residue to a formal all-time theorem; remaining Machine C gateways and BB(6) remain open.

This index lists substantive statements that improve the mathematical frontier. It is not a solved-BB(6) claim.

- [New infinite Machine C reset exclusion, j congruent 16 modulo 32](./2026-11-02-machine-c-mod32-exclusion.md), Agent 21, 2026-11-02. Proves that the published exact blank-entry acceleration cannot reach `(64t+33,96t+52,0)` for any natural `t`. Formal Lean proof excludes a previously surviving infinite residue class by two forced predecessor chains and a global modular invariant. The original-machine/acceleration equivalence is independently certified. Other Machine C gates and the exact value of BB(6) remain open.

- [Three source-certified infinite Machine C inverse-gateway exclusions](./2026-11-02-machine-c-symbolic-inverse-exclusions.md), Agent 23, 2026-11-02. Three direct Lean-verified symbolic proofs exclude all j≡3(mod16), j≡7(mod64), and j≡59(mod64) reset indices from the original accelerated blank orbit. These were previously computer-identified in Agent20's finite abstraction; here the reusable symbolic predecessor calculus and exact source bridge are kernel certified. No holdout is decided.\n
- [Machine C side-gateway modulo-16 exclusion](./2026-11-02-machine-c-side-mod16-exclusion.md), Agent 23, 2026-11-02. A direct source-bridged Lean proof excludes every `(0,4n,24n+23)` side gateway with `n%16=0` for all n, including zero; full verification [run 41400280303](https://github.com/FlareZ123/bb6/actions/runs/41400280303). The family had appeared in Agent20's computational sieve; the new all-time symbolic certificate is independent of finite graph enumeration. Machine C and BB(6) remain undecided.

Underlying verified Lean modules, compressed source hashes, CI workflow and full proof dossier are in [Agent 21's detailed intermediate source directory](../im-results/agent21-c-source-bridge/).

