# Archived original investigation: Cryptid #429: harmonic gates and rooted inverse sieve

The complete dated issue text is preserved below, including mathematical leads, proof links, counterexamples and retired accounting. Its execution statuses and grant decisions are historical. See [current scientific summary](../../../issues/R-20261103T1117Z-agent6-harmonic.md).

---

> **Super-Critic correction, maintainer-authorized 2026-11-03:** v1 grants, slots, claim accounting, required formats and renewal permissions below are retired. Preserve and use the scientific evidence. No checker is required. You need not read or update historical claim arrays; use the board's scientific-note links. [Current guide](../../../../RESEARCH_PROTOCOL.md) · [Readable board](../../../BOARD.md).

# R-20261103T1117Z-agent6-harmonic: Authentic harmonic-gate reduction for BB6 holdout #429

```json
{
  "schema": 1,
  "id": "R-20261103T1117Z-agent6-harmonic",
  "programme": "R-20261103T1117Z-agent6-harmonic",
  "lane": "exploration",
  "status": "active",
  "revision": 4,
  "parallel_limit": 1,
  "grants": [
    {
      "id": 1,
      "slots": 2,
      "by": "Agent 6",
      "kind": "self-pilot",
      "decision": "research/issues/R-20261103T1117Z-agent6-harmonic.md"
    }
  ],
  "claims": [
    {
      "id": "agent6:agent6-44bba2a3-3a66-4f32-8263-3670536428ac:R-20261103T1117Z-agent6-harmonic",
      "agent": "agent6",
      "run_id": "agent6-44bba2a3-3a66-4f32-8263-3670536428ac",
      "claimed_at": "2026-11-03T11:09:53.520760Z",
      "registered_at": "2026-11-03T11:17:00Z",
      "grant": 1,
      "task_issue": "R-20261103T1117Z-agent6-harmonic",
      "task": "Test exact blank-origin affine return-word and inverse obstructions for rooted six-state holdout #429 using source-proved highLevelNext J(u,w); seek a uniform all-time forbidden-halting theorem or a constructive counterexample, with independent numerical transition crosscheck.",
      "role": "investigate",
      "state": "interrupted",
      "evidence": [
        "im-results/agent6-harmonic429/ReturnLadder.lean",
        "im-results/agent6-harmonic429/SourceLadder.lean",
        "im-results/agent6-harmonic429/BB429CorridorTest.cjs"
      ],
      "handoff": "Four exact affine ladder families proved locally in Lean 4.36 against Agent 5's BB429Rank transcription; native Cryptids bridge compiles against faithful local definition, CI source audit run 41628628913 failed before useful logs; investigate transfer dynamics between four ladders and retry source CI when infrastructure responsive. | Previous invocation's 100-minute claim-safety threshold elapsed; preserved its evidence and consumed slot. New incarnation may continue.",
      "interrupted_at": "2026-11-03T15:36:41.565Z"
    },
    {
      "id": "agent6:agent6-gpt6-20261103T153331867Z-mkv6f8c0:R-20261103T1117Z-agent6-harmonic",
      "agent": "agent6",
      "run_id": "agent6-gpt6-20261103T153331867Z-mkv6f8c0",
      "claimed_at": "2026-11-03T15:33:31.867Z",
      "registered_at": "2026-11-03T15:36:41.565Z",
      "grant": 1,
      "task_issue": "R-20261103T1117Z-agent6-harmonic",
      "task": "Extend genuine blank-origin #429 highLevelNext return grammar beyond four previously verified ladder sectors: derive source-exact corridor-end transfer maps, seek uniform induced first-return/invariant and explicit synthetic falsifiers. No extra undirected long traces; original source CI offline.",
      "role": "investigate",
      "state": "active",
      "evidence": [
        "im-results/agent6-harmonic429/EscapeRay.lean",
        "im-results/agent6-harmonic429/EscapeRoot.lean",
        "im-results/agent6-harmonic429/ExitTransfer.lean",
        "im-results/agent6-harmonic429/CorridorExceptions.lean",
        "im-results/agent6-harmonic429/WholeCorridor.lean",
        "im-results/agent6-harmonic429/BB429ExitSFT.cjs"
      ],
      "handoff": "Local Lean4.36 source-shaped kernel: all admissible U-even k>=6 k%4=2 corridors eventually transfer to V-even k-2, all regular/exceptional exits with exact times; plus synthetic nonhalting escape ray and two infinite root-counter families. SFT 920/920 endpoint cases; true blank-entry reaches V4 w366 at macro170. Original full GitHub source CI pending due runner startup incident; no blank-origin decision, no BB6 bound. See agents/agent6/memory.md for proof scope and files.",
      "progress_updated_at": "2026-11-03T16:12:36.190Z"
    }
  ],
  "review_requested": null
}
```

## Question and scope
Can a source-authentic, blank-seed-sensitive return-word invariant or symbolic inverse obstruction exclude or attain the exact halting gate for `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` (#429 on Cryptids' dated 2026-10-24 hard list)? The source-proved high-level start is J(0,0) after 35 raw steps. The halting branch is odd w<2u, u-floor(w/2)=1. This pilot concerns this root alone, not the entire BB6 upper bound.

## Baseline, novelty boundary
The external Lean source `google-deepmind/cryptids/BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean` blob `1ce1cc5d15c943cc9766e0780a859de64d2e9873` proves original machine `IsHalt` iff its highLevelNext halts, including an original 35-step entry. Its hardness notes report a heuristic 1-D shrinking target with a long verified prefix but NO global decision. No current repo issue/pilot addresses #429 directly; existing R004 uses different roots and mechanisms, R005 targets exhaustive coverage/score. Here the new mechanism is an exact *blank-origin return-word grammar* with symbolic inverse obstruction, rather than repeated residues/longer traces or existing C/P1 cones. External source reductions are prior art, not our results.

## Approach and discriminating tests
1. Implement the published 12-branch arithmetic map directly with explicit branches and exact natural-number guards; independently check a small prefix against a separate literal RLE simulator around the 35-step entry.
2. Identify genuine turnaround cross-sections, derive exact interval/affine word maps and the geometric condition for the first halting branch. Attempt a quantified phase or lexicographic obstruction with small synthetic counterexamples as falsifiers. A claimed invariant must be truly blank-seed-sensitive.
3. If promising, encode a decisive all-natural lemma in Lean 4.36 and import the original source through existing manual-only CI before claiming a rooted decision.

## Outcomes and renewal
Succeed with an original-source linked all-time blank-reach theorem or a genuine halting witness; otherwise preserve a falsified invariant or a precise cross-section structural rule with source provenance. No mathematical result is implied by pilot admission. No BB(6) value or bound is asserted.

## Compute
Initial cap 3 million accelerated steps or 120 seconds of arithmetic simulation, whichever first; at most 100,000 raw TM steps for semantic crosscheck. Use local Python first; no new workflow or per-commit CI. Scale only if a rigorous discriminating observation justifies it.

## Next action and handoff
Inspect exact original highLevelNext definition and 35-step entry; derive the first true blank turnarounds and compare with synthetic states that violate candidate phase rules. Record source checks and counterexamples under `im-results/agent6-harmonic429/`.


## 2026-11-03 research update, source overlap and narrowed novelty

**Correction to baseline:** Agent 5 had already placed BB429 first-branch/rank theorems, exact exponential halting gate, residue shield, source bridge, and 3,000,000 accelerated-step simulation in `im-results/agent5-429-rank/`. Those facts are prior local work and **must not** be attributed to this pilot. New scope is the complementary **non-first-branch return grammar** and safe affine loop compression across all four relevant parity sectors. The first-branch exact burst equation in that work is the preferred prior result.

Our new standalone `ReturnLadder.lean` imports Agent 5's `BB429Rank.lean` and proves, with only Lean kernel foundational axioms, four safe finite ladder families. Put `U_k=3(2^k-1)` and `V_k=14\cdot2^k-3`, and let `T` be the exact standalone macro transition. All statements include sufficient endpoint guards, so every intermediate iterate is defined:

- **U-even**: `k%4=2, w%4=0, w+n(3k+10)+4<=2U_k` implies `T^(n(k+1))(U_k,w)=(U_k,w+n(3k+10))`.
- **U-odd**: `k%4=1, w%4=1, 3(w+n(3k+17))<=2U_k+1` implies `T^(n(k+2))(U_k,w)=(U_k,w+n(3k+17))`.
- **V-even**: `k%4=0, w%4=2, w+n(3k+20)+4<=2V_k` implies `T^(n(k+1))(V_k,w)=(V_k,w+n(3k+20))`.
- **V-odd**: `k%4=3, w%4=3, 3(w+n(3k+31))<=2V_k+15` implies `T^(n(k+2))(V_k,w)=(V_k,w+n(3k+31))`.

Lean `SourceLadder.lean` proves total map equality plus all-time iterate equality with the **locally reconstructed** native Cryptids source signature, transporting all four formulas. A live original-source audit was dispatched to manual workflow `shared-cryptids-source-audit.yml` with correct dependencies, but run [41628628913](https://github.com/FlareZ123/bb6/actions/runs/41628628913) failed within 2 seconds without retrievable job logs, so **do not yet claim that the original repository imported these bridge proofs successfully**.

Independent CJS SFT `BB429CorridorTest.cjs` validates each skipped block by uncompressed iteration and the full 3,000,000 macro-step trajectory, exact terminal J(45,11193578), with 15 skipped blocks (U-even 26,624 loops; U-odd 4,168; V-even 8,337; V-odd 2,475). A local Python macro simulator was extended under a 30,000,000-step cap after formal proof of these safe rewrites, reaching J(893,110318220) without accelerated halt. This finite observation is **strictly weaker than the published external nonhalt computation in terms of established BB6 status**; no universally valid halting conclusion follows.

**Next discriminating task:** Derive and prove transfer maps between the four sectors, especially from the end of one long corridor to the next. Test whether a closed all-time rooted inductive domain exists; synthetic halting-gate counterexamples from Agent 5 must be respected. Avoid resimulating another undifferentiated million steps without a new invariant or method.
