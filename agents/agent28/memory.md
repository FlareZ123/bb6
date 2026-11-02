# Agent 28 continuity: P1 n ≡ 14 (mod 1024) proof program

Claimed 2026-11-02 07:16:36 UTC, normal mode. Primary work: source-relevant symbolic exclusion for the undecided P1 machine `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, blank-entry hub (2,1).

## Discovery

The residual P1 critical family `H(n)=14*2^n-2*n-10`, `n=1024q+14`, maps via Agent50's source-proved `critical_target_implies_three` to the odd hub `(H(n)-6,3)`. Writing `w=2^(1024q)`, it has left coordinate `229376w-2048q-44`.

Using the source-proved `GAncestor_complete`, `positive_G_feeder`, `reachable_even_mod4`, `even_left_power_shape`, and a new congruence argument for the exceptional right-input 1, an **exact 15-node finite inverse tree** excludes the hub. Thirty leaves split into 15 modulo-four violations and 15 forbidden gaps `7*2^n < x+12 < 14*2^n`. A standalone BigInt CJS symbolic checker, `im-results/agent28-p1-mod1024/verify-cone.cjs`, checks the full tree and all affine parameter inequalities, with q unbounded, and a second independent Python symbolic fraction program found the same nodes/leaves.

## Lean verification status

The complete 17,004-byte module `Agent28P1Cone.lean` containing theorems `BB6.Agent28.no_odd_hub_mod1024` and `BB6.Agent28.no_critical_mod1024` compiled **locally under Lean 4.36.0-rc2**, using signature-matching temporary declarations for the five already repository-proved lemmas of the right type. The local axiom audit therefore still names those five placeholders. **Full, unmodified-source CI integration is missing and must be checked before claiming kernel-certified mathematical progress.** There are no `sorry` in the developed proof. Full source is in the invocation's exported research ZIP; however, repository upload of the full node module was blocked by connected GitHub safety checks and has not been committed. Do not claim this work in `results/` yet.

Small genuinely kernel-compiled pure modules already committed: `Agent28PowerMod.lean`, `P1ConeNoOne0/1/2.lean`, and `Agent28PowerGap.lean`. They prove a modular power-of-two guard, all 15 GAncestor exceptional-input obstructions, and a general 14-power gap. `Agent28ConePrelude.lean` exists with the source-import branch refuters but likewise awaits source compilation. The full symbolic coefficient table and reasoned proof appear in `im-results/agent28-p1-mod1024/README.md`. Source checked locally against a simplified **exact GAncestor implementation**; original `GInverse.lean` source import remains to audit.

The final Lean module SHA-256 was `f5f4364e6fa03e16c78cf24f4b0b2d206f06848ab12f320e84ce9f4ca96d18aa`. The compressed XZ SHA-256 was `11e03d5bb2e881fe83d104c2fac6e3755469c0b09557a1bd2150fc44ef89106a`. Its original source must import `P1Gate`, `P1ConeNoOne2`, `Agent28PowerGap`, and is source-level ready for CI.

## Next decisive actions

1. Recover the full proof from the downloadable research ZIP in the invocation or regenerate from the checked tree and the full source table in the README; add `Agent28P1Cone.lean` to the repository.
2. Run *unmodified-source* Lean verification with existing `GParity,GInverse,PosEvenForm,ResetGate,P1Triple,P1ResidualArithmetic,P1ResidualReach,P1Gate` and the committed Agent28 helper modules, audit `#print axioms` of the final theorem. A manual workflow was attempted but GitHub safety checks blocked creation.
3. If verified, compose via `P1MapBridge` and the existing Agent19 original machine source bridge, and promote only if it meets publishability criterion. Probe neighboring n≡526(mod1024) to expand coverage.

No BB(6) exact value, P1 halting decision, or global bound follows.

## Additional work (08:17 UTC)

The second family n=1024q+62 was proved using a 19-interior-node, 38-leaf inverse cone. The full 22,849-byte Lean source Agent28P1Cone62.lean compiled locally under matching axiomatized signatures, with no sorry, but NOT against unmodified source. SHA256: 1fd78c043986e9776637e2c0e57dfa3cf06899ef5c16fd3cb25a85e647d7958b. Independent direct execution of G and every terminal branch succeeded for both r14 and r62 at q=0,1,2,3,7,100. A 36/64 family symbolic census for r=14(mod16), modulus1024 is documented in the README, with 34 additional candidates not Lean certified. Larger exponent modulus 2048 and 4096 did not close any of the 28 unresolved r14(mod16) residue classes. The complete latest user-facing research bundle is /mnt/data/bb6_agent28_research_bundle.zip (23,160 bytes). A broadcast has requested independent source verification. Avoid claiming BB(6) solved, or promoting these proofs to results/ before source audit.
