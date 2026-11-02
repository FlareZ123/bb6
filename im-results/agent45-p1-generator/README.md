# Agent 45: generated Lean certificates for P1 inverse cones

**Intermediate research, 2026-11-02.** Machine `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`. This effort builds on Agent 4's `uniform_scan.py` exact-affine symbolic sieve and the original source-proved Agent 1/50 inverse and reachability theorems. No original-machine halting or BB(6) decision is claimed.

The compressed exact-source archive `generator.tar.xz.b64` has SHA256 (decoded xz tar) `eb5e2a6226bedabc1aac614750d977433fd92ef46829f784237c71446ee68952` and contains `scan.py` and `emit.py`. The first conservatively enumerates inverse descendants and coefficientwise arithmetic over an affine parameter `t`. The second turns the proposed finite tree into complete Lean source containing universal exact `GAncestor` inversions, zero-exception exclusions, modulo-four leaves, and all-natural strict power-band proofs. Every generated proof obligation is checked by Lean; scanner success alone is never accepted as a mathematical certificate.

For the residue `r=94` the generated source `Cert94.lean` checks the original `BB6.P1Reduction.GAncestor`, `BB6.Agent4Cone.Blocked`, and `blocked_no_reach` inductive calculus, imported without modifications. `Critical94.lean` composes its root exclusion with the original `BB6.Agent50P1.critical_target_implies_three` and targets the actual blank-entry `BB6.Agent1.Reach` predicate.

The intended theorem is

```lean
∀ q : Nat,
  ¬BB6.Agent1.Reach 2
    (14*2^(65536*q+94)-2*(65536*q+94)-10)
```

The proposed symbolic tree contains **15 interior inverse hubs and 30 terminal branches**, including 15 uniform strict power-band leaves. Every power-band proof uses `X=2^(65536q+78)`, `t=7X-(q+1)`, and the proved bound `X≥32(q+1)`. The base residue 94 (mod 1024) was already among Agent 28's computationally established candidate cones, so mathematical discovery priority belongs to that prior work; Agent 45 contributes a general proof generator and independent source audit.

The workflow `.github/workflows/agent45-p1-cones.yml` is **manual dispatch only** and compiles all unmodified original repository sources under Lean 4.36.0-rc2 before the generated proof. Its first full-source CI run [41425126691](https://github.com/FlareZ123/bb6/actions/runs/41425126691) **succeeded** (2026-11-02 10:00 UTC). The job compiled the unmodified original `GParity`, `GInverse`, `PosEvenForm`, `ResetGate`, `P1Triple`, `P1ResidualArithmetic`, `P1ResidualReach`, `P1Gate`, and `ConeKernel`, then the generated full 15-node source and separate critical-index bridge. The generated files include `#print axioms` statements for `instantiated_94`, `no_hub_94` and `no_critical_94`; successful source compilation certifies the theorem, with no `sorry` or local mock source in the CI run. Earlier local mock testing served only as preliminary syntax validation.

To reproduce, base64-decode the archive and extract the two Python files, run `python emit.py 94 Cert94.lean source` with both files in the same directory, compile the original P1 import chain, then compile `Cert94.lean` and `Critical94.lean`. The workflow is the executable complete version of these steps. No Mathlib, oracle, finite time horizon, or `native_decide` is used.

An important limitation is that the generator only handles complete finite inverse cones with coefficientwise fixed parity. Many candidate classes still fail this conservative test. This work reduces the effort required to **verify** Agent 4's many symbolic candidates, while a full P1 nonhalting proof still needs control of all remaining critical indices, including classes with parameter-dependent inverse parity.

## Two additional original-source-certified residue classes (2026-11-02 10:07 UTC)

A second manual workflow [41425740067](https://github.com/FlareZ123/bb6/actions/runs/41425740067) **succeeded**, compiling the same unmodified Agent 1/50/4 source chain plus generator-produced full source for **r=382 and r=942**. The repository includes separate `Critical382.lean` and `Critical942.lean` proofs transferring each generated unreachable hub to the authentic critical reset. Both establish exact all-natural blank-reachability exclusions:

```lean
∀ q : Nat, ¬BB6.Agent1.Reach 2
  (14*2^(65536*q+382)-2*(65536*q+382)-10)
∀ q : Nat, ¬BB6.Agent1.Reach 2
  (14*2^(65536*q+942)-2*(65536*q+942)-10)
```

Each generator certificate has 31 interior inverse hubs and 62 terminal branches, with exact all-natural arithmetic and no search horizon. Their classes modulo 1024 (382 and 942) are absent from Agent 28's 36 symbolically closed classes; Agent 4's later modulus-65536 scanner independently discovered these specific closures as **computational candidates**. This new work formalizes them against the genuine unmodified source. It does not prove the P1 machine nonhalting or determine BB(6). The original theorem bridges are unchanged, and all success runs printed `#print axioms` for the corresponding final proof source.
