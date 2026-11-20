# Cryptid D: source-certified return grammar and 3-adic synchronization

**Research state (6 November 2026): exact return and shift theorems for specified source configurations; no global true-blank halt/nonhalt decision.** [Complete working proof record](FULL_RESEARCH_LOG.md).

## Original machine and proven scope

The D-start table is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. The original `I_n(r)` F/0 section has blank left tape, leading unary `1^n` and suffix `r`. Physical blank-padding and first-return conditions matter when composing source steps.

- [BlankEighthRejoin.lean](BlankEighthRejoin.lean) source-certifies another actual-blank exceptional return after 6,046 regular source steps, with successful [original-source CI 41870046802](https://github.com/FlareZ123/bb6/actions/runs/41870046802). This is finite authentic continuation without a perpetual-survival conclusion.
- [DRegularShift.lean](DRegularShift.lean) proves for the canonical eleven-row regular return model, without the earlier conditional shift hypothesis, an all-depth `3^k` input/`8^k` output shift identity, including matching success and failure at regular exits. [CI 41872704046](https://github.com/FlareZ123/bb6/actions/runs/41872704046). [DRegularSourceShift.lean](DRegularSourceShift.lean) transports paired regular runs to the physical original six-state machine: [CI 41872968993](https://github.com/FlareZ123/bb6/actions/runs/41872968993).
- [DRegularDurationShift.lean](DRegularDurationShift.lean) and [DRegularTimedShift.lean](DRegularTimedShift.lean) give exact quadratic runtime dependence for `k` regular returns, with `55 Q_k + 12·9^k = 12·64^k`: [CI 41875379548](https://github.com/FlareZ123/bb6/actions/runs/41875379548). The physical-source timed composition and exceptional-packet extensions have their own dependencies, explained in the [full synthesis](2026-11-04-eighth-and-3adic-synchrony.md).
- Further source-certified lemmas describe a guarded E-boundary halting cylinder, B-run valuation, a universal **synthetic** unary halting extension, and precise E111 first-return conditions. All exact theorem references remain in the [full research log](FULL_RESEARCH_LOG.md).

## Unresolved root problem

Regular all-depth synchronization does not establish that the actual blank orbit remains regular at **every** return. Exceptional exits, physical suffix equivalence and possible original halts need complete treatment.

**Next proof:** establish a blank-root forward-closed word/suffix invariant across every exceptional packet, or produce an original-machine halting witness. A large finite trace or synthetic halting extension cannot settle the blank trajectory.


## Exact 3-adic block evaluation for long regular runs (7 November 2026)

**DRegularFast.lean** turns the all-depth shift theorem in **DRegularShift.run_shift** into an exact block evaluator. For a canonical section s and block length k, write

    s.a = 2 + ((s.a-2) mod 3^k) + 3^k * ((s.a-2) / 3^k).

The small representative is evaluated for k regular sections. The exact shift theorem lifts its endpoint by 8^k times the quotient. The file proves **run_block**, the multi-block evaluator **fastRunBlocks**, and the arbitrary-length identity

    DRegular.run n s = DRegularFast.fastRun n s.

The current block size is 512. This is an exact evaluator for the eleven-row DRegular model, not a new theorem about the original machine.

**Local validation (Lean 4.36.0-rc2):** a standalone kernel computation evaluated the 12,588-step twenty-first regular segment from the actual symbolic-root seed, represented as a 116,926-bit integer (SHA-256 6058f62d1da9808c0da7609037f59cfe61fba7ceadf9dc0886dfbc25d66b9781). It produced the 134,738-bit endpoint (SHA-256 3e2c1a9d3ca8c6b80cd32917a32601966814ec5f0718f48ff6dc2ff60fbbf767), with shape L(9*t21+4,8,1) and t21 mod 27 = 6. The explicit fastRun computation plus endpoint check compiled in 9.36 seconds with 1.5 GB maximum RSS; the endpoint computation itself is by decide and has no axioms. The generic equality theorem inherits the axiom profile of DRegularShift.run_shift ([propext, Classical.choice, Quot.sound]).

**BlankTwentyFirstRejoin.lean** now uses DRegularFast.fastRun for this long segment, and the manual root-chain workflow compiles DRegularFast.lean before it. The earlier root-chain run [42377931873](https://github.com/FlareZ123/bb6/actions/runs/42377931873) was cancelled at the verification step and predates this optimization; it is not a Lean failure report. A fresh manual source-only run is still required to certify the updated composition.

## Conditional root lookahead and source-return status (20 November 2026)

### Root-specific episode #41 is source-closed, conditionally

The corrected DRegular lookahead reaches the episode-41 candidate
\(L(9t_{41}+7,7,1)\), with \(t_{41}\equiv76\pmod{81}\). Its source-specific
EEE escape produces the p=2 packet
\(M(512u_{41}+257,4,2;0\,1^6)\). Writing
\(k_{41}=81s+76=27(3s+2)+22\) and \(q=7=3\cdot2+1\), the packet lies exactly
in the family handled by
[P2K4SourceReentry.lean](../agent2-packet-shift/P2K4SourceReentry.lean).

The theorem **close_one_regular_reentry** returns this packet to a physical
regular section for every parameter in its family; **source_chain_close_one**
composes that return with any already-proved source prefix. GitHub Actions
run [43391093227](https://github.com/FlareZ123/bb6/actions/runs/43391093227)
succeeded, with axiom profile [propext, Quot.sound] for both wrapper
theorems. Thus the specific #41 packet candidate is no longer an
unresolved source-return case.


Evidence status: the #41 first-stop identification is still a model-only
computational candidate, not a kernel-certified first-stop theorem.
The actual seed39 used by Seed39Probe.lean is
\(L(64t_{38}+49,6,0)\), supplied by
BlankThirtySeventhToThirtyEighthRejoin.lean. Seed39Probe evaluates
firstExceptionFromSeed39 using firstStopBlocks with a 2,000-block cap
(1,024,000 regular transitions). Its soundness theorem is conditional on
the bound firstExceptionFromSeed39.1 < 1024000; that bound is not proved
in the file, and the reported #eval output is not stored as a certificate.
The manual workflow agent37-root-exceptions34-38.yml has no runs and does
not compile Seed39Probe. Therefore the reported residue
\(L(9t_{41}+7,7,1)\), \(t_{41}\equiv76\pmod{81}\), must be treated as a
computational hypothesis. The source closure below is a verified
conditional implication for that packet if the candidate is confirmed.

Do not confuse this actual root seed39 with
DRegularFirstExit.seed39_exception, which starts from the separate toy
state \(L(39,0,0)\).


This does **not** prove that the authentic blank-tape trajectory reaches
#41. The upstream root chain through episodes 19–38 remains unverified, so
the #41 lookahead and its source closure are still conditional on that
prefix.

Unfolding the q=7, u=2 endpoint and the existing regular-endpoint normalizer
gives the next regular seed explicitly. With \(t=3s+2\),
\(a_K=512t+426\), and \(\operatorname{wordInc}(\operatorname{code}(2))=21\),
the normalizer returns
\[
L(8a_K+53,4,0)=L(4096t+3461,4,0)
              =L(12288s+11653,4,0).
\]
This seed is still conditional on the upstream blank-root prefix and the
unverified Seed39 first-stop bound.

### Seed42 two-step original-source composition (wrapper pending)

The earlier four-base-case / DRegularShift.next_shift route is not
needed for this seed. Put \(p=4096s+3883\). Then
\[
L(12288s+11653,4,0)=L(3p+4,4,0).
\]
The already source-certified theorem
DRegularELow.e_zero_suffix (all \(k,q\), physical ObsEq) gives
\[
L(3p+4,4,0)
\xrightarrow{\;12p^2+49p+66\;}
L(8p+5,1,13)
=L(32768s+31069,1,13).
\]
This is an original-machine source result, not a DRegular.next-only
prediction.

Now split \(s=3r+i\). The second source row is one of three already
source-certified universal contracts:

| \(i\) | Middle state | Source theorem | Resulting regular state |
|---:|---|---|---|
| 0 | \(L(3k_0+4,1,13)\), \(k_0=32768r+10355\) | DRegularESource.e_contract_many | \(L(262144r+82849,3,10)\) |
| 1 | \(L(3k_1+3,1,13)\), \(k_1=32768r+21278\) | ARegularFull.original_A_positive_row | \(L(262144r+170263,1,5)\) |
| 2 | \(L(3k_2+2,1,13)\), \(k_2=32768r+32201\) | BRegularSource.original_B_row | \(L(262144r+257631,0,0)\) |

The target indices follow directly from the corresponding DRegular.next
rows: respectively \(8k_0+9\), \(8k_1+39\), and \(8k_2+23\). All three
targets are canonical. The first E step and each second-row step are
original-source results; BoundaryPadding.source_chain composes their
physical ObsEq certificates and exact primitive times.

The arithmetic and source dependencies are recorded in
[seed42-two-step-source-composition.md](seed42-two-step-source-composition.md).
**Status:** the composition is a proof-ready derivation from existing
source-certified modules, but a single Lean wrapper for all three branches
has not yet been compiled or axiom-audited. Do not cite the composed theorem
as kernel-checked until that wrapper passes local preflight and its
transitive axiom audit.

This advances the conditional seed by two original-source returns for every
\(s\), without proving that the seed is reached from the blank tape. The
actual root connection remains blocked by the Seed39 first-stop bound and
the required extra ternary digit \(s\bmod3\) (equivalently the
corresponding \(t_{41}\bmod243\) information).

### Remaining p=2 source families

The K=4 wrapper is deliberately narrower than the full k≡4 (mod 9)
residual: it handles \(k=27t+22\) and \(q=3u+1\). Other k≡4 (mod 9)
subfamilies, including k≡4 or 13 (mod 27) and the other q residues at
k≡22 (mod 27), remain open.

The raw source module [P2K7Source.lean](../agent35-cryptid-code/P2K7Source.lean)
handles \(k=27t+25\) for all q, with separate q mod 3 endpoints. It was
compiled in successful workflow run
[42519761689](https://github.com/FlareZ123/bb6/actions/runs/42519761689).
No regular-section wrapper is present yet. Its three exact endpoints match
the existing regular-endpoint normalizer; a wrapper using
**EChainBEExit.regularEndpoint_reentry** is a concrete integration task.
This covers the k≡25 (mod 27) subfamily of k≡7 (mod 9), not the entire
k≡7 class. Other subfamilies and deeper 3-adic cylinders remain; see the
[packet-shift dossier](../agent2-packet-shift/README.md).

### Episode-19 proof and source-audit status

The current main-branch
[NineteenthTail5684.lean](../agent37-d-timing-cocycle/NineteenthTail5684.lean)
uses a 32-step block evaluator and native_decide. The preceding Agent 2
incarnation locally compiled that exact module in 1.766 seconds against the
pinned predecessor artifacts, but this is **not an accepted kernel-only
proof**: Lean's native-decision tactic introduces a dedicated axiom, and
the stage-4b workflow explicitly rejects that dependency. There has been no
CI run on this current fast32 source revision.

[NineteenthTerminalCertificate.lean](../agent37-d-timing-cocycle/NineteenthTerminalCertificate.lean)
still composes the 4,096-step prefix and 5,684-step tail with
run_add 4096 5684; the earlier direct run_add attempts ended in runner
shutdown without a Lean diagnostic. The current NineteenthTail5684.lean already defines
fastRunBlocksWith and run_blockedWith parametrically in block size B, so
the 64-block route requires no separate evaluator from the old branch.
For the tail, use 5684=64*88+52 and
run_blockedWith 64 88 52; for the complete endpoint, use
9780=64*152+52 and run_blockedWith 64 152 52. Then prove the concrete
endpoint with decide +kernel. The 32-block alternatives are
5684=32*177+20 and 9780=32*305+20. This avoids the large
run_add 4096 5684 induction. These remain proof candidates until a
local Lean preflight is completed.

The current invocation's local shell and Python tools fail before even
trivial commands execute. Agent 6 has been asked to preflight kernel-only
alternatives; no response has arrived yet. Do not dispatch CI as a
substitute for local preflight, and do not count the current native-decide
tail as a kernel-checked result.

The old E/A packet proof issue is no longer current: commit e7009d5
fixed the q−1 successor case in EFirstAPacket.lean, and run
[43394857303](https://github.com/FlareZ123/bb6/actions/runs/43394857303)
printed [propext, Quot.sound] for exceptional_EA_packet before the
larger root audit was externally shut down at the sixteenth root. The
earlier 43391359969 failure belongs to the pre-fix source. A later
stage-3b attempt, [44289702591](https://github.com/FlareZ123/bb6/actions/runs/44289702591),
also ended in runner shutdown without a Lean diagnostic.

The source-certified D root currently reaches episode 18. Episodes 19–38
remain a conditional continuation, despite the prepared arithmetic and
source-return modules. Keep these distinctions explicit; no all-time
nonhalting result follows from the finite chain.

