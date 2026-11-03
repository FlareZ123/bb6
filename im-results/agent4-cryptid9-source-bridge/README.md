# Cryptid9 S-section source transport and conditional 729-gate

**Status:** intermediate mathematical/source-alignment proof. The original BB(6) blank-rooted machine has **not** been decided. No new upper or lower bound for BB(6) follows.

**Agent 4, 2026-11-03.** Research programme [R-20261103T0753Z-agent9-s-valuation-return](../../research/issues/R-20261103T0753Z-agent9-s-valuation-return.md).

## Source and exact scope

Original machine: `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`. The upstream Google DeepMind Cryptids module is `BusyBeaver/BB6/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean` at commit `c86f15861709b76042998c5211c7b2f83991621b`. It defines `HighLevelState`, `highLevelNext`, `is_valid_highLevel_acceleration`, and `isHalt_iff_highLevel_acceleration`. Its actual S-to-T transition at `b%3=2,c=0` is **`some (.T m)`**, whereas Agent9's S-only `Sstep` represents the end of the S section as **`none`**.

[SourceSRun.lean](SourceSRun.lean) imports the existing [Agent9 original-source one-step projection](../agent9-valuation-return/SourceSProjection.lean). It proves by induction that *every* `n`-step surviving S-only path from `(b+16,c)` corresponds to the unmodified high-level S path from `S b c`; it also proves that an S-only `none` after a surviving prefix means the original high-level state is **T**, not a halt.

[SourceGate.lean](SourceGate.lean) gives a mathematically exact new conditional source-gate composition:

```
source_immediate_halt_after_transfer:
  scalarRun n (some (b+16,c)) = some (q,d)
  → scalarRun (n+1) (some (b+16,c)) = none
  → q%729 = 0
  → sourceRun (n+2) (some (.S b c)) = none

blank_source_halt_if_729_gate:
  scalarRun n (some (141,3)) = some (q,d)
  → scalarRun (n+1) (some (141,3)) = none
  → q%729=0
  → sourceRun (n+5) (some (.T 1)) = none
```

The latter uses the exact three-high-level-step prefix `T(1)→T(28)→T(92)→S(125,3)`; `q=125+16=141`. It is **conditional** on reaching the 729-divisible transfer gate from the true start. Neither that reachability nor any S-to-T transfer from `(141,3)` is established. The 729-divisible S-counter yields a T-counter `m≡226 (mod 243)`, which falls into the original source T-branch immediate halt. The fixed residue 226 is one of the seven T gates previously classified by Agent9; the all-prefix original-source transport is the additional semantic integration here.

## Verification status and dependency honesty

On 2026-11-03, locally built Lean 4.36.0-rc2 `SourceSProjection`, `SourceSRun`, `SourceGate` against a **temporary, exact transcription of the upstream high-level S and T branches** and shadow declarations for the other three source constructors. Every named theorem compiled, no `sorry`, and `#print axioms` listed only `[propext, Quot.sound]` or `[]`. The temporary shadow upstream module was deliberately **not** committed. Thus these are **locally kernel-checked arithmetic/alignment proofs; full original-upstream-source compilation is still pending**.

The repository has a documented GitHub Actions runner failure affecting manual jobs before execution (Critic 2026-11-03 08:04 UTC). A future source check must compile the unaltered pinned Cryptids imports with a compatible upstream Lean toolchain, then `SourceSProjection`, `SourceSRun`, and `SourceGate` using the same trusted declarations. A successful local shadow compile alone does not certify the original source import.

Local SHA256: `SourceSRun.lean` c8396c224604c3b101c2ac696ad86741943de1309a8782d52598fa7fdfb98bed; `SourceGate.lean` 7d00cc02364de8c218dabc3c15b8434e67755fca10d4b67fcd0006136aa6a008. The files in GitHub may differ in final whitespace; re-hash there and compare before an authoritative CI report.

## Next genuine obstruction

For the actual start `q=141,c=3` (and the distinct authenticated `q=17,c=3`), derive a seed-sensitive **all-time** invariant preventing S-to-T transfer, or prove a transfer and analyze its genuine T continuation. Agent9's standalone maximal-valuation and fatal-congruence certificates are available in `im-results/agent9-valuation-return/`. A 100,000-step finite survival observation is only a regression test. Additional congruence classes or longer finite traces alone would not settle the problem.

## Kernel-checked infinite synthetic first-halt family

[SourceSynthetic.lean](SourceSynthetic.lean) is a further all-natural local Lean 4.36.0-rc2 proof with no `sorry`, and only standard `[propext, Quot.sound]` axioms, under the same shadow-source limitation above. Set `a(0)=0`, `a(n+1)=9a(n)+2`, `Q(c)=3a(c+5)+4`, and `B(c)=Q(c)-16`. The key quantified theorem is:

```lean
synthetic_first_halt (c : Nat) :
  sourceRun (c+7) (some (.S (syntheticInput c-16) c)) = none ∧
  ∀ j, j<c+7 →
    ∃ st, sourceRun j (some (.S (syntheticInput c-16) c)) = some st
```

The first source S-only scalar step maps `(Q(c),c)` to `(9^(c+5),c+4)`. Exactly `c+4` zero-residue steps then map this to `(4^(c+4)*3^(c+6),0)`, a 729-divisible S counter. The next high-level step transfers to T, and the subsequent T step halts. The proof separately checks every shorter prefix stays live, so `c+7` is the **exact number of high-level transitions from this synthetic S starting configuration**. It is not an original primitive-step count.

This yields synthetic halting configurations at arbitrarily large S-section height, refuting any proposed global assertion that all high-height S states survive. These are deliberately constructed alternative starting configurations. **There is no proof that any belongs to the original blank-derived orbit**. This does not imply a new BB(6) score or a resolved original holdout.

The complete source proof imports the preceding two modules. Source files may be locally checked in this order: `SourceSProjection` (Agent9), `SourceSRun`, `SourceGate`, `SourceSynthetic`. They were checked with Lean 4.36.0-rc2 against the exact high-level S and T branch transcription; full original pinned Cryptids compilation remains pending. The local file SHA256 before repository upload was `1164f25024a70e5a9184b9618d43d4a432dda5651b7c0dd061baaed118bc82b5`, with potential whitespace differences in the uploaded copy.
