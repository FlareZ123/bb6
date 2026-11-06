# Historical full research log

**Unabridged snapshot of the former research README, 6 November 2026.** Mathematical derivations, failed approaches, source references, finite data and chronology are preserved. Dated “pending”, “current” and “next” statements below refer to their original writing time and may be superseded. Use the maintained [summary](README.md) for the synthesized status.

---

# D-start Cryptid: a conditional 3-adic synchronisation theorem

**Classification: intermediate reduction, not a resolved blank-tape holdout and not an unconditional theorem about the source machine.** Agent 2, 2026-11-02. The mathematical implication below is verified by the Lean kernel, while its two hypotheses remain open for the actual Turing-machine return system.

## Precise objective and statement

The D-start machine is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. In the standard `I_n(r)` notation, its head is in F reading 0, its left side is entirely blank, and its right side begins `1^n r`, where `r` is empty or begins 0. From a valid such input, denote the next completed F/0 return by `M(n,r) = (n',r')` if one exists.

A key **unproved source-specific conjecture**, already suggested by Agent 31's earlier finite tests, is *single-return shift equivariance*:

```text
For all n >= 5 and all valid suffixes r:
  if M(n,r) = (m,t), then M(n+3,r) = (m+8,t).
  Both outcomes should likewise agree when there is no F/0 return.
```

The second hypothesis is a *return-domain guard*: whenever `n >= 5` and a return exists, the returned unary length `m >= 5`. This is also unproved for all source configurations. The threshold 5 was used as a deliberately conservative proof parameter before the false n=4 return marker was diagnosed; it should not be interpreted as a demonstrated sharp boundary.

The newly Lean-checked **conditional reduction** proves that these two hypotheses imply, for **all** k,j,n,q and suffix r with n≥5 and 0≤j≤k:

```text
M^j(n + 3^k q, r)
  = shift_(8^j * 3^(k-j) * q) ( M^j(n,r) )
```

Here `shift_d(Some(m,t)) = Some(m+d,t)` and `shift_d(None) = None`. In particular, whenever the smaller starting configuration completes j<k returns, the larger also completes j, with *exactly the same suffix* and *the same current unary-length residue modulo 3*. Thus the first k A/E/B branch decisions coincide in any trajectory for which the relevant returns exist. For j=k, the returned unary lengths differ by precisely `8^k q`.

This reduces the full proposed 3-adic branch-continuity statement to **one** universal return-shift law plus a domain guard. It does not assert either of those source-specific hypotheses. The abstract `None` means absence of a completed next F/0 return and does not distinguish actual halting from divergence. Consequently no halting equivalence is inferred from `None`.

## Formal verification

Source: [CryptidContinuity.lean](./CryptidContinuity.lean). The file is standalone and imports only `Lean`.

- `shift_multiple`: single-step shift by 3 implies shift by any 3q.
- `iterate_shift`: exact synchronisation after k returns for inputs separated by `3^k q`.
- `prefix_shift`: the corresponding relation at every prefix of length j≤k.
- `prefix_branch_mod_three`: equal returned suffix and unary length modulo 3 for j<k.

Compiled locally with uploaded **Lean 4.36.0-rc2**. Axiom audits: `shift_multiple`, `iterate_shift`, and `prefix_shift` depend only on `[propext, Quot.sound]`; the branch corollary additionally uses `Classical.choice`. There is no `sorry`, `admit`, or `native_decide`. The formal return oracle is an arbitrary function, so this kernel result is intentionally independent of the source-machine semantics. It must not be presented as a direct certificate for the D-start machine.

## Computational exploration and falsification

Reproducible standalone C++17 [test_shift3.cpp](./test_shift3.cpp) implements the 12 raw transition entries, both infinite blank sides via ample zero padding, and canonicalises the first left-blank F/0 return. Fixed `std::mt19937` seed 94929; `n=5..14`; 120 random suffix samples for each length `1..90`; the first suffix bit is 0. It checks `M(n+3,r)` against the +8 version of `M(n,r)` with a two-million-transition cap per comparison. Any halt mismatch is counted as a failure; timeouts, off-window or nonblank-left cases are separately flagged.

**Observed output, 2026-11-02:** Original first run checked 108,000 pairs with n=5..14 and no mismatch. **Revised physically correct test** checks 140,400 random pairs n=2..14 with the same seed, suffix lengths 1..90, and no mismatches or incomplete cases; 851 pairs halt on both sides. The revised program maintains an exact count of 1s strictly to the head's left and only accepts F/0 when the count is zero. It continues through interior F/0 passes that have nonblank left tape. This is reproducible finite evidence only, not an exhaustive certificate or formal proof of the two hypotheses. The same pattern had already survived Agent 31's independent 229,376 finite comparisons with suffixes up to 16 bits, so the primary value of this run is testing longer suffixes.

**Correction of an earlier false counterexample:** the old Agent 2 script treated a state-F/0 pass with nonblank left tape as a legitimate first return. Its purported 91-step `I_4(011)` successor actually has left list `1011`; the genuine first return is at **96** steps, to `I_3(01111010101)`. The matching `I_7(011)` return takes **157** steps and yields `I_11(01111010101)`. The previously alleged 3-step mismatch for n=4 versus n=31 vanishes; both branch strings are `E,A,A`. The complete finite no-earlier-return certificates for n=4 and n=7 are in [ReturnGuard.lean](./ReturnGuard.lean), compiled against the checksum-restored original machine in [CI 41442257562](https://github.com/FlareZ123/bb6/actions/runs/41442257562). All returned theorem axiom reports are empty. The existing abstract theorem retains its **arbitrary n≥5 guard as a formal hypothesis**; it does not prove n=4 is exceptional. Source-specific n↦n+3 equivariance may hold already for n≥2, but this remains conjectural.

## Research priorities

1. Prove the source-specific single-return shift theorem by a parametric F-boundary stuttering relation: the three first-delimiter cases in [Agent 31's proof](../agent31-cryptid-boundary/README.md) change the alternating left stack by exactly four pairs when n increases by three. The remaining obligation is to transport that four-pair difference through **all** possible suffix-processing returns, including A/E exceptional suffixes, while respecting real halts.
2. Prove the return-domain lower bound m≥5, or replace it with an inductively maintained condition that holds for the genuine blank start n=9 and its continuation.
3. Seek a **closed forward blank-reachable suffix language** after establishing equivariance. Continuity alone does not rule out eventual halting, since a 3-adic residue may eventually encode a halting branch.
4. Use the authentic source model and blank-padding bisimulation in Agent 31/32/35/37 before claiming any actual-machine theorem. The wiki [D-start analysis](https://wiki.bbchallenge.org/wiki/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---) explicitly describes the proposed but unproved 3-adic continuity.

**Scope:** this is proof of an abstract implication and a targeted computational test. No exact BB(6) value, new Busy Beaver bound, or original-machine decision is obtained. Retain in `im-results/` until an authenticated source theorem materially advances the decision problem.


## Additional authentic-source E branch proofs (2026-11-02)

[**EOneZeroHalt.lean**](./EOneZeroHalt.lean) proves a new universally quantified guarded halting cylinder of the D-start original six-state machine: for every k≥0 and arbitrary finite binary suffix ys, starting at F/0 on `1^(3k+4) 0 101101100 0 ys` enters frozen halt state 6 for the **first** time at `12k²+41k+147` primitive transitions. The additional zero after 101101100 is essential: with suffix `111` and no zero, the machine returns instead of halting. The proof expands 114 exact E-boundary steps into fixed symbolic chunks and composes with Agent31's original-source `prefix_E`. [Successful SHA-verified original-source Lean CI 41441110080](https://github.com/FlareZ123/bb6/actions/runs/41441110080), audit only `[propext, Quot.sound]`, no unproved placeholders.

[**ReturnGuard.lean**](./ReturnGuard.lean) imports that same original raw model and corrects the earlier false 91-step marker with completely axiom-free finite kernel evaluations, proving no physically blank-left F/0 return at any time 1..95 for the n4 case or 1..156 for n7. Both exact return configurations are source-proved. [Successful CI 41442257562](https://github.com/FlareZ123/bb6/actions/runs/41442257562).

[**EOneTripleReturn.lean**](./EOneTripleReturn.lean) extends the complementary E boundary `0 101101100111 ys` and gives a **source-kernel-verified universal exact return**:
`I_(3k+4)(0 101101100111 ys) -> I_(8k+3)(01111010101010101010 ys)` after `12k²+49k+170` raw transitions. The 134-step E-to-B bridge is proved for every alternating-stack length m and every arbitrary tail by 14 symbolic subsegments, followed by Agent32's source-proved universal `sweepB_run`. [Full authenticated original-source Lean CI 41443332942](https://github.com/FlareZ123/bb6/actions/runs/41443332942) passed with no unproved placeholders and the standard `[propext, Quot.sound]` axiom audit for all final theorems. This is an exact F/0 endpoint identity; the proof does not separately establish its first-return minimality. This is a conditional tape family and does not imply blank-orbit behavior.

These branch certificates remain **intermediate** and should not be promoted to `results/` without a demonstrated advance toward original blank-machine closure.

## 2026-11-02 17:06 UTC: exact B-run valuation and paired-stack portal

**Source-authenticated original-machine Lean CI:** [run 41487788756](https://github.com/FlareZ123/bb6/actions/runs/41487788756), successful at commit `1890820e6d2f01b81dad6672fc93c2efcc43cb2b`. The manual-only workflow `.github/workflows/agent2-brun-lean.yml` restores and checks Agent 31's SHA-pinned original six-state machine, and then kernel-compiles `BRunValuation.lean`, `BRunSource.lean`, and `APortal.lean`. Every final theorem reports standard axioms only, with no `sorryAx`.

**Consecutive B-branch arithmetic, exact iff.** Define `BStep n m` by `3m=8n+11`, precisely the unary update of the original-source `full_B` theorem. Define `BRun j n z` as a composable chain of exactly `j` steps. Then:

- `run_scale`: `3^j(5z+11)=8^j(5n+11)` for every BRun.
- `run_iff_three_power`: for **every** natural `j,n`, there exists some endpoint `z` with `BRun j n z` **iff** `3^j ∣ (5n+11)`. The sufficient direction constructs a valid sequence by mathematical induction and exact arithmetic, not simulation.
- `no_long_B_run`: no fixed natural-number start `n` can sustain `5n+11` consecutive B steps; equivalently, no starting `n` admits arbitrarily long B-only chains.
- `source_B_chain_from_dvd`: given `3^j ∣ (5n+11)`, the **actual original raw six-state machine**, starting in F-on-zero with `n` right-hand ones followed by **at least j explicit consecutive zero delimiter cells**, executes a finite raw-step trajectory to F-on-zero with the arithmetic B-run's endpoint length and the unchanged remaining suffix. Exact per-branch times follow Agent 31's already source-certified `full_B`; the theorem existentially sums those times. This prepares synthetic tapes and makes **no claim** that the original blank-start suffix contains this many zero delimiters.

**Original-machine 01-to-10 left-stack transport, all counts.** `APortal.lean` proves `portal_one` by direct four-step expansion of the original six-state machine, and `portal_run` by induction: for all `q`, left-tail `L`, and right-tail `ys`, from state A reading 1 with left nearest-first `(01)^q ++ L` and right `1::ys`, exactly `4q` raw transitions reach state A reading 1 with left `L` and right `1::((10)^q ++ ys)`. This lemma transfers an arbitrary run of alternating pairs **across** the head and has no hypotheses about the unknown surrounding tails. The final axiom audit is exactly `[propext, Quot.sound]`. It is a possible useful local component of a 3-adic `n→n+3` return-bisimulation proof, not the conjectured global return relation.

**Current open proof obligation.** Show that both the C-on-one reverse-sweep portal (Agent 32's `cWalk_run`) and the newly proved A-on-one alternating-pair portal preserve the exact physical first-return outcome when they process four extra left-side `01` pairs at the corresponding first left-stack marker. In bounded random prefix tests the first encounter with the marked bottom of the alternating stack was C-on-one, A-on-one, or the machine halted earlier. That empirical trichotomy and the resulting global shift law are **unproved** and must be treated as candidate structure. Any formal first-return proof must distinguish internal F-on-zero visits from F-on-zero with the **entire left tape blank** and must track explicit/implicit trailing zeros correctly.

**Scientific status:** intermediate local symbolic dynamics only. Does not resolve D-start from blank or BB(6), establish a new BB(6) bound, or claim publishable novelty over preexisting transducer literature.

## 2026-11-02 17:20 UTC: every unary F-on-zero tape has a finite halting continuation (Lean kernel checked)

**New fully quantified mathematical theorem:** `BB6.CryptidUniversalExtension.every_unary_has_halting_extension_all` in [UniversalExtension.lean](./UniversalExtension.lean), authenticated by [original-machine CI 41489869859](https://github.com/FlareZ123/bb6/actions/runs/41489869859), successfully compiled against the original Agent31 checksum-pinned `Boundary` module with Lean 4.36.0-rc2. Axiom audit reports **exactly `[propext, Classical.choice, Quot.sound]`**, with no `sorryAx`; the two exceptional witnesses for unary lengths zero and one use `by decide` and report **no axioms**.

For every natural `n`, there exists a finite right binary suffix `w` and a finite time `t` such that the **actual six-state original machine**, started in state F scanning zero with blank left tape and exactly `n` initial right-hand 1s followed by `w`, is in frozen halt state6 at time `t`. This includes **all** `n=0,1,2,...`. In formula form, if `I(n,w)=⟨[],false,1^n ++ w, F⟩`, then `∀n ∃w,t, (run t (I(n,w))).st=6`.

**Formal derivation, without large numerical simulation:**

1. The exact source-proved B return transforms `n=3k+2` to `8k+9`, consuming one leading zero in the arbitrary right suffix and preserving its remainder. `BRunValuation.lean` proves a B-chain has length `j` iff `3^j | (5n+11)`. `BExit.lean` proves every natural seed exits residue `n≡2 (mod 3)` after finitely many B branches, by contradiction with `no_long_B_run`; `run_nondecreasing` preserves `n≥2`.
2. If the terminal length is `n=3k+3`, the **new right-hand A halting cylinder** uses `0 1101101100`. In original machine state A scanning 0, a right prefix `1101101100` forces F-on-one at raw step 68 and frozen halt at raw step 69 for **all left tapes and arbitrary following suffixes**. Composed with the original prefix_A theorem, `full_A_halt` establishes frozen halt at `12k²+41k+101` additional raw steps from `I_{3k+3}(0 1101101100 ys)`, all k and ys. Authenticated independently in [CI 41488735119](https://github.com/FlareZ123/bb6/actions/runs/41488735119).
3. If the terminal length is `n=3k+4`, the right-hand E halting cylinder is `0 1101100`. From state E scanning 0 with immediate three left cells `001` and right prefix `1101100`, it reaches F-on-one after 65 steps and frozen halt after 66 steps for arbitrary left and right tails. `full_E_halt` combines this with Agent31's original `prefix_E` in `12k²+41k+99` steps. Authenticated with `BExit.lean` in [CI 41489207384](https://github.com/FlareZ123/bb6/actions/runs/41489207384). The E halting cylinder overlaps earlier Agent32 original-machine `EZeroHalt.lean`; the stronger arbitrary-left-tail statement is separately checked.
4. `BRunSource.lean` composes all required B returns on an input suffix containing enough explicit zeros, then `UniversalExtension.lean` composes the appropriate terminal A/E halting certificate. The exceptional `n=0` direct witness suffix is `0001101100`, halt step 151; for `n=1`, suffix `01101100`, halt step 74. Both are directly kernel evaluated with `by decide`. Therefore the theorem covers all natural `n`.

A runnable [halting_witness.py](./halting_witness.py) constructs one specific suffix and its **exact first-halt primitive-step count** by iterating the B arithmetic rule and choosing the corresponding terminal cylinder. Its independent sparse-tape raw simulator reproduced the predicted halting step exactly for every `n=0,…,24`, including `n=14`, which halts at step **1,041,317** for the constructed suffix. The formal Lean theorem independently establishes eventual halt for all n, and the generator uses the exact component step formulas; the computer samples are a cross-check rather than the proof.

**Key limitation and relevance to BB(6):** The theorem quantifies existentially over an input **extension chosen to force halting**. It does **not** show that the all-blank orbit ever encounters any chosen extension, nor that the original blank tape halts or runs forever. In fact it is a counter-obstruction to any attempted global nonhalting proof based solely on unary F-section length without restricting the accompanying right suffix. The longstanding `n→n+3` first-return conjugacy and exact BB(6) remain open. No `results/` promotion without external novelty and direct frontier relevance review.


## 2026-11-02 20:35 UTC: exact *first* return of the original E111 boundary

**Original-source Lean CI:** [successful workflow 41520580312](https://github.com/FlareZ123/bb6/actions/runs/41520580312), commit `511e22a5899dd2e359095e02d69759d1f70dca5e`, Lean 4.36.0-rc2. The workflow checksum-reconstructs unmodified Agent31 `Boundary.lean`, compiles Agent32 `CryptidSix.lean`, and checks the two new original-machine modules `NoEarlierF.lean` and `E111FirstReturn.lean`, plus preexisting `EOneTripleReturn.lean` and `EOneTriplePairs.lean`. Final axiom audits show `[propext, Quot.sound]` without `sorryAx`.

**New strict first-return result.** `BB6.CryptidE111FirstReturn.e111_boundary_first_return` proves, for every `m : Nat` and arbitrary finite binary suffix `ys`, that starting from Agent2's authentic `e0 m ys` E boundary:

- at exactly `2*m+137` original raw Turing-machine steps, the state is F on zero with the *entire physical left tape blank*;
- for every earlier time `t < 2*m+137`, this physical F/0 return does not occur.

Proof: all intermediate times of the initial 134-step source-certified E-to-B bridge are split into fourteen 10-or-4-step symbolic configurations `e0,...,e134`. The `NoReturn` property, checked by Lean at every step for all `m,ys`, allows internal F-on-zero visits only if the left tape remains nonempty. The separate all-natural theorem `BB6.CryptidFirstReturn.sweepB_firstF` proves that the subsequent  `2*m+3` B-sweep does not encounter **state F at all** before its exact endpoint. Exact step composition yields the strict first-return theorem.

**Fix to older proof chain:** this run also repaired two existing associativity obligations in `EOneTriplePairs.lean` (`scan_pairs`, `oppairs_add`). Those obligations caused `sorryAx` in previously failed CI runs; the successful source-level rebuild compiles all legacy dependencies with standard axioms only.

**Remaining missing implication:** the full F-section `I_(3k+4)(0 101101100111 ys)` first reaches the boundary `e0 (4k) ys` by the source-certified `prefix_E` after `12k²+41k+33` steps. It is not yet formally proved that no earlier physically blank-left F/0 return happens during that initial prefix. The  E-boundary first-return certificate alone is therefore **not yet** a first-return theorem for the original entire F-to-F section. The single-return shift law for arbitrary suffixes and the genuine blank orbit remain unresolved.

**Computational test (independent finite evidence):** a literal sparse-tape C++ simulator compared all F-section inputs `I_n(0 w)` for unary lengths `n=2..15`, suffix lengths through 15 bits, with their `n+3` counterparts. It completed 458,752 paired first-return-or-halt comparisons, with no mismatch or timeout at the prescribed finite cutoff. This is consistent with the conjectured shift law but cannot establish it and is not used by the Lean proof.


## 2026-11-02 20:49 UTC: **complete original-source E111 first positive return**

The stronger [original-source Lean workflow 41522567162](https://github.com/FlareZ123/bb6/actions/runs/41522567162) passed at commit `671836c22176bf4e4c327bcc60b03d726f5ff669`, checking [`PrefixNoF.lean`](./PrefixNoF.lean) and [`FullE111First.lean`](./FullE111First.lean) in addition to the strict E-boundary proof above. The final original-source statement is `BB6.CryptidFullE111First.full_E_one_triple_first_return`.

For *every* natural `k` and arbitrary finite binary suffix `ys`, the actual original D-start six-state machine started at the physical F/0 section

```
I_(3k+4)(0 101101100111 ys)
```

has its **first positive-time physically blank-left F-on-zero return** exactly at

```
T(k) = 12*k*k + 49*k + 170
```

and reaches

```
I_(8k+3)(01111010101010101010 ys).
```

The source-certified prefix `prefix_E` takes `12*k*k+41*k+33` raw steps and is followed by the E111 boundary run of `8*k+137` steps. The new `prefixE_positive_noF` proves **state F does not occur at all at any strictly positive intermediate prefix time** for *any* `k,ys`; it decomposes all intermediate times among a 24-step initial setup, arbitrarily many complete triple-symbol pumps, and the final delimiter scan. The parametric pump no-F proof is itself decomposed into forward `2m+3` and reverse `4m+24` sweeps; each local transition segment is checked against the authentic source. The E111 boundary result rules out physically blank-left F/0 at all remaining intermediate times, while permitting internal visits to state F with nonblank left tape.

The resulting exact first-return theorem reports **only standard Lean axioms `[propext, Quot.sound]`**, no `sorryAx`, no `native_decide`, and no unverified assumption. The original source is automatically SHA-restored and compiled in the manual-only workflow. This resolves the previously documented *first-return minimality* gap in the E111 family. It is a mathematically fully certified infinite-family theorem, but remains classified **intermediate** because it has no demonstrated implication for the actual all-blank orbit or universal BB(6) upper bound.

Reusable targets now include proving analogous *all-time* prefix exclusions for residue 2 and residue 0 (`prefix_B` and `prefix_A`), then exploiting their exact completed first returns for global macro shift invariants. The four-left-pair A/E portal and unconditional first-return shift across *arbitrary suffixes* remain open.


## 2026-11-04: Eighth original-blank exception, unconditional all-depth 3-adic regular synchronization and universal quadratic raw cost

The new [**synthesis with full proof provenance**](./2026-11-04-eighth-and-3adic-synchrony.md) documents a marked advance over the earlier **conditional** `CryptidContinuity.lean` theorem. Three independent primary advances are now original-source-model verified:

1. [`BlankEighthRejoin.lean`](./BlankEighthRejoin.lean) certifies from the actual all-blank six-state source 6,046 regular return steps after Agent35's seventh reentry, followed by the universally quantified exceptional E/A reentry into pure unary `L(64*t8+81,0,0)`. [Pinned full original-source Lean **SUCCESS 41870046802**](https://github.com/FlareZ123/bb6/actions/runs/41870046802), all axioms standard, no `sorryAx`. The source terminal E input has a unary counter with 53,597 binary digits.
2. [`DRegularShift.lean`](./DRegularShift.lean) establishes **unconditionally for every canonical s and all natural k,p** the complete Option-valued prefix synchrony `run k (shift s (3^k*p)) = (run k s).map (shift · (8^k*p))` for the unchanged eleven-row source-derived return function, including identical ability/inability to continue in the regular language. [Standalone model source CI **SUCCESS 41872704046**](https://github.com/FlareZ123/bb6/actions/runs/41872704046). [`DRegularSourceShift.paired_original_run`](./DRegularSourceShift.lean) lifts both trajectories to **authentic original six-state primitive runs** modulo physically correct blank-padding equivalence, at exact (distinct) primitive-step times. [Full original source CI **SUCCESS 41872968993**](https://github.com/FlareZ123/bb6/actions/runs/41872968993).
3. [`DRegularDurationShift.lean`](./DRegularDurationShift.lean) and [`DRegularTimedShift.lean`](./DRegularTimedShift.lean) show the exact source-primitive return runtime for **every** k-return and every 3^k unary input lift is a quadratic polynomial in the lift multiplier p. Its coefficient `Q_k` is independent of the entire B/A/E branch history and satisfies `55 Q_k + 12·9^k =12·64^k`. [Source-original eleven-row model Lean CI **SUCCESS 41875379548**](https://github.com/FlareZ123/bb6/actions/runs/41875379548). Primitive six-state source-level `lifted_original_timed` is undergoing full original-source audit [41875708707](https://github.com/FlareZ123/bb6/actions/runs/41875708707) (pending at this checkpoint).

A further source proof [`EExceptionalShift.lean`](./EExceptionalShift.lean) and [`EExceptionalAppend.lean`](./EExceptionalAppend.lean) investigates **lifting this synchrony through the first genuinely irregular E packet**. It uses the source-proved original six-state E-double macro to show the complete output tail is fixed, while the leading unary block shifts by 8 per added 3 input unary bits and the exceptional primitive-step cost retains the same quadratic curvature. Full pinned source audit in [queued CI 41877521068](https://github.com/FlareZ123/bb6/actions/runs/41877521068). Treat these exact source-composed assertions as pending until compiler success.

These are mathematical results for one specific six-state accelerator with rigorously checked finite source semantics. **Neither D machine global halting/nonhalting nor exact BB(6) is settled.** An actual root-specific forward-closed suffix language or source-certified halting witness is still required, and related external 3-adic results should be compared before any publishability claim. Correct placement remains `im-results/`, with no promotion to `results/` yet.
