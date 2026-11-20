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
The first DRegular exceptional return from this seed has not yet been
computed; this is the next root-specific arithmetic probe.


A further one-step reduction is available from the existing 3-adic shift
theorems. Write \(p=4096s+3883\); then the seed above has
\(a_{42}=12288s+11653=4+3p\). The arithmetic L-step table predicts the
base case
\(\operatorname{next}(4,4,0)=\operatorname{some}(5,1,13)\). If this tiny
base case is checked against the actual DRegular.next definition, the
existing DRegularShift.next_shift theorem gives the next regular state
\[
L(5+8p,1,13)=L(32768s+31069,1,13).
\]
The duration base case is 49, so DRegularDurationShift predicts the
corresponding original-machine segment length
\(49+24p=98304s+93241\). This is a conditional one-step model reduction,
not yet a source-certified root extension.

For a further finite-state reduction, the arithmetic L-step table predicts
the four small base cases
\(\operatorname{next}(4,4,0)=(5,1,13)\),
\(\operatorname{next}(4,1,13)=(9,3,10)\),
\(\operatorname{next}(3,1,13)=(39,1,5)\), and
\(\operatorname{next}(2,1,13)=(23,0,0)\). If these are checked against the
actual DRegular.next definition, DRegularShift.next_shift propagates them
to the three second-step branches for \(s=3r+i\):
\[
\begin{array}{c|c}
i & \text{candidate second state}\\
0 & L(262144r+82849,3,10)\\
1 & L(262144r+170263,1,5)\\
2 & L(262144r+257631,0,0)
\end{array}
\]
This suggests a finite-state 3-adic transducer: the next ternary digit
selects one of finitely many control updates, and the shift theorem
propagates each base case to arbitrary higher digits. The arithmetic
first-exit table has its exceptional boundary at \(a\bmod3=1,\ q>0,\ b=1\).
This remains a research lead until the base cases are checked against
DRegular.next and the root seed39 first-stop bound is certified.
 The next branch depends on
\(s\bmod3\), equivalently on \(t_{41}\bmod243\); the currently reported
\(t_{41}\bmod81=76\) is insufficient. A checked Seed39Probe first-stop
bound should preserve this extra ternary digit.


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
shutdown without a Lean diagnostic. A better candidate is a kernel-only
decide +kernel proof using the reusable 64-step evaluator preserved in
branch agent2-d-root-fast64-fixed (namespace BB6.Agent2Fast64), or the
current 32-step block helper. Prefer proving the complete 9,780-step
endpoint directly from seed19 with 64 blocks (152 blocks plus 52 steps)
or 32 blocks (305 blocks plus 20 steps), avoiding the large
run_add 4096 5684 induction. These alternatives still require a local
Lean preflight.

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

