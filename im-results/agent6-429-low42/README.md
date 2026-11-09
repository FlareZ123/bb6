# Machine #429: uniform deficit 4k+2 prepared-tape return

**Intermediate mathematical research (9 November 2026, Agent 6).** Machine #429 is the six-state, two-symbol table `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`. The machine's genuine blank-origin status remains open. This dossier covers **every k >= 0**, with no cutoff on either parameter.

## Exact mathematical claim

Let `J(u,w)` denote the established complete bi-infinite prepared-tape configuration `BB429JPhysical.jTape u w`, with state A and head at coordinate zero. The new [Low42Physical.lean](Low42Physical.lean) states, uniformly for every `j,k : Nat`:

```text
Original J(j+2k+1, 2j)
    -- (4j² + 22j + 18k + 79) exact primitive steps -->
Complete J(0, 4j+4k+12),
    with final absolute physical head at -(2j+4k+5).
```

This is the entire `r=2u-w=4k+2` residue family for `k>=0`; it proves the exact full-tape successor and head displacement on **prepared J inputs**. The theorem uses the original `BB6Coverage.run target429`, `BB429PhysicalBridge.Represents`, and physical head equation, so it concerns actual primitive instructions rather than accelerated step counts. The boundary `r=2` (k=0) is included through a new signed even-C/0 recurrence, extending [Agent 6's earlier low2 dossier](../agent6-429-low2/README.md). The authentic blank tape's reachability of an arbitrary prepared J input remains a separate obligation.

## Why this family closes symbolically

[Low42Delta.lean](Low42Delta.lean) uses the established exact original-table source zipper, its signed `runWithDelta` transition, and previously proved all-suffix E/1 return. The checkpoint after `j` original physical bubbles has nearest-first complete zipper

```text
stage42(j,k) = A / 1, left = 1^(4j) (10)^(2k+1) 1^6,
                         right = [1,0,1]
```

The exact source continuation has two fresh C/0 sections. The first is at step `8j+10` with relative head +6 and left word `1^(4j+8)(10)^(2k)1^6`. After `4j+11` additional steps, it reaches A/1 with left word `(01)^(2k)1^5`. For positive `k=m+1`, the nontrivial crossing is a five-step handoff into the existing `e1After(2m+1)` macro, an exact `14m+15` E/1 return, and a `4j+18` repaint into a second C/0 with left word `10 1^(4j+4m+20)`. The existing `c0_to_junc0_delta` then terminates the trace.

The additional `k=0` branch proves `c0_even_to_c0_delta n`: an all-parameter contiguous even C/0 frontier returns to a new C/0 in `4n+11` moves with signed displacement `+3`. Combining both branches, [`BB429Low42.low42_source_all`](Low42Delta.lean) states:

```lean
runWithDelta (20*j+18*k+79) (stage42 j k) =
  some (junc 0 0 (4*j+4*k+12),
    -((4*j+4*k+5:Nat):Int))
```

The physical proof's exact all-cell geometry is

```text
negFill (jTape (j+2k+1) (2j)) j x = true
iff
  [-2j-4k-8 <= x <= 2j+1 and
   x is not an unfilled negative-even hole in [-2j-4k-2,-2j-2]]
  or x = 2j+3.
```

The local theorem `stage_tape_rep` establishes this complete spatial correspondence, so the prior generic `multi_bubble_prefix` and `source_runWithDelta_rep` jointly produce the physical return and head `-(2j+4k+5)`.

## Proof status and next use

Both new source and full physical files **compiled locally in Lean 4.36.0-rc2** with exact copied source zipper / tape definitions and temporary interface axioms replacing only existing repository proofs (the bubble-prefix macro, signed-source return, and physical bridge). The local final theorem's axiom audit lists those interface placeholders, so **the combined module has not yet been checked against the complete unchanged original repository source**. Neither file introduces a `sorry` or mock axiom. The targeted `.github/workflows/agent6-429-low42.yml` was added with a path-filtered push trigger and a manual dispatch option; it compiles `Low42Delta.lean` and `Low42Physical.lean` against the complete original dependency graph and rejects `sorryAx`. **Report original-source kernel certification only after that run is observed successful.**

The main scientific remaining obligation for machine #429 is an **all-time authentic blank-root section invariant or genuine halt witness**, especially avoidance of the fatal `B/001` / `C/01` event. This result supplies an exact new infinite family of transition clauses for that closure. [Agent 18's low-J dossier](../agent18-429-low-j/README.md) previously had this `r=4k+2` family as a finite-test formula; the new symbolic proof removes that finite-range limitation on the prepared branch, subject to the original-source audit above.

## Sharp universal head-excursion theorem

A second, parameter-independent **exact** result is in [Low42Max.lean.xz.b64](Low42Max.lean.xz.b64), an XZ/base64-compressed 24,527-byte Lean file (SHA-256 of extracted `Low42Max.lean`: `9858955ef0ad8ce9b3f2769adebd1943c6081e99bd7d77a436a6c215bea13ed5`). Its `BB429Low42Max.low42_source_max_all` theorem establishes for **every** `j,k : Nat`:

```lean
runWithMax (20*j+18*k+79) (stage42 j k) =
  some (junc 0 0 (4*j+4*k+12), -((4*j+4*k+5:Nat):Int), 10)
```

Here `runWithMax` is Agent 1's exact original-source primitive monitor, whose third component is the **maximum** head displacement over *every successfully executed instruction prefix*, including the start. Thus the global rightward record is **exactly 10 relative cells** after the bubble section, independent of both unbounded parameters. The new proof establishes the crucial even-C/0 sharp `c0_even_to_c0_max` result (its maximum and endpoint are both +3) along with sharp all-parameter A/F, A/B, E/1 and C/0 macros. There are no source-level additional axioms or sorry. This module **compiled locally in Lean 4.36.0-rc2** against exactly copied original source definitions and interface-equivalent assumptions for already proved dependencies; original-repo Lean CI verification is included in the workflow, with status to be checked.

[`Low42PrefixPhysical.lean`](Low42PrefixPhysical.lean) lifts this sharp maximum through the original physical `target429` table: for every `t ≤ 20j+18k+79`, starting from the **exact original physical tape after the j-bubble prefix**, the machine executes t successful primitive instructions and ends at a head coordinate at most `2j+10`. This is a universal finite-segment barrier on the *entire original infinite tape*, not merely an endpoint calculation. The original prepared J's rightmost initially marked cell is `2j+3`; this certified segment reaches its maximal head seven cells farther to the right. Both the sharp monitor and physical-prefix theorem are included in the fail-closed original-source CI audit.
