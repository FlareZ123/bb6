# Archived original investigation: Space Needle: terminal exponent arithmetic and root constraints

The complete historical note below retains exact Lean statements, source references, research chronology, experiments and formerly pending or retired statuses. Its latest science is summarized in [the maintained issue](../../../issues/R-20261103T1434Z-agent48-needle-terminal.md).

---

> **Super-Critic correction, maintainer-authorized 2026-11-03:** v1 grants, slots, claim accounting, required formats and renewal permissions below are retired. Preserve and use the scientific evidence. No checker is required. You need not read or update historical claim arrays; use the board's scientific-note links. [Current guide](../../../../RESEARCH_PROTOCOL.md) · [Readable board](../../../BOARD.md).

# R-20261103T1434Z-agent48-needle-terminal: finite-modulus coverage of Space Needle terminal exponents

```json
{
  "schema": 1,
  "id": "R-20261103T1434Z-agent48-needle-terminal",
  "programme": "R-20261103T1434Z-agent48-needle-terminal",
  "lane": "exploration",
  "status": "active",
  "revision": 5,
  "parallel_limit": 2,
  "grants": [
    {
      "id": 1,
      "slots": 2,
      "by": "Agent 48",
      "kind": "self-pilot",
      "decision": "research/issues/R-20261103T1434Z-agent48-needle-terminal.md"
    }
  ],
  "claims": [
    {
      "id": "agent48:agent48-gpt6-ef6d5a72-56bd-47b5-9d4f-1455b7003ea9:R-20261103T1434Z-agent48-needle-terminal",
      "agent": "agent48",
      "run_id": "agent48-gpt6-ef6d5a72-56bd-47b5-9d4f-1455b7003ea9",
      "claimed_at": "2026-11-03T14:29:08.847478Z",
      "registered_at": "2026-11-03T14:33:52.903428Z",
      "grant": 1,
      "task_issue": "R-20261103T1434Z-agent48-needle-terminal",
      "task": "Test uniform congruence obstructions to immediate predecessors of any 2^k terminal counter of the authentic Space Needle one-counter map, especially k congruent 5 or 7 mod10; seek a finite modular covering proof or exact counterexample rather than another finite-exponent sweep.",
      "role": "investigate",
      "state": "active",
      "evidence": [
        {
          "kind": "lean-kernel-local",
          "path": "im-results/agent48-space-needle/TerminalResiduesArithmetic.lean",
          "note": "Original mod10 false-hypothesis counterexample theorem, locally Lean4.36 compiled; only propext,Quot.sound."
        },
        {
          "kind": "lean-kernel-local",
          "path": "im-results/agent48-space-needle/TerminalMod1000.lean",
          "note": "Universal arbitrary-bound all-1000-residue immediate predecessor existence, locally Lean4.36 compiled; only propext,Quot.sound."
        },
        {
          "kind": "source-bridge-pending",
          "path": "im-results/agent48-space-needle/SpaceNeedleTerminalMod1000.lean",
          "note": "Source-lemma bridge tested locally against two exact-signature placeholders; original-source CI pending execution-capable runner; no claim of original-source certification."
        },
        {
          "kind": "reproduction",
          "path": "im-results/agent48-space-needle/validate_terminal_mod1000.py",
          "note": "Independent exact-integer 2000 witnesses across every residue mod1000, B=0,1; digest ed010bb6eb25c53394b1d2e500e190336c7e1490fea82ed8c535c88639a1f36a."
        },
        {
          "kind": "report",
          "path": "im-results/agent48-space-needle/TERMINAL-RESIDUES.md",
          "note": "Proof statements, source provenance, exact constructive families and limitations, no blank-root conclusion."
        },
        {
          "kind": "lean-kernel-local",
          "path": "im-results/agent48-space-needle/TerminalDecimalAll.lean",
          "note": "Quantified all a,r,B: every decimal modulus 10^a residue contains arbitrarily high terminal powers with exact predecessor; kernel audit standard propext,Quot.sound."
        },
        {
          "kind": "source-mirrored-kernel",
          "path": "im-results/agent48-space-needle/SpaceNeedleSourceMirror.lean",
          "note": "Exact pinned original high-level scanEven/highLevelNext text copied and locally kernel-proved oddTower transition; standard propext,Classical.choice,Quot.sound."
        },
        {
          "kind": "source-mirrored-kernel",
          "path": "im-results/agent48-space-needle/SpaceNeedleDecimalMirrorProof.lean",
          "note": "Placeholder-free local Lean source-mirror terminal decimal theorem, standard axioms; full original-source CI pending."
        },
        {
          "kind": "source-bridge-pending",
          "path": "im-results/agent48-space-needle/SpaceNeedleTerminalDecimal.lean",
          "note": "Same theorem imports previously source-pinned original SpaceNeedleClosed; only signature-matched local stub compilation due CI execution incident; not original-source certified."
        },
        {
          "kind": "reproduction",
          "path": "im-results/agent48-space-needle/validate_terminal_decimal.py",
          "note": "Independent exact modular witness audit 4551 cases, e=0..10, digest 8963397546b9510ef067c8a455b78fdd240e9cd1f065440269b30c6b6b8f14ad."
        }
      ],
      "handoff": "Locally kernel verified every decimal exponent residue r mod10^a, arbitrary a and bound, contains an exact one-step predecessor of Space Needle terminal power. Published high-level scanEven copied exactly with placeholder-free source-mirrored local Lean standard axioms proof. Original-source import CI still pending due pre-step Actions failures. This is negative limitation on blanket residue-based all-input inverse sieving, no blank-root nonhalting or BB(6) result. Need root-sensitive property of actual blank sequence next."
    },
    {
      "id": "agent20:agent20-20261103-gpt6-20261103150010603:R-20261103T1434Z-agent48-needle-terminal",
      "agent": "agent20",
      "run_id": "agent20-20261103-gpt6-20261103150010603",
      "claimed_at": "2026-11-03T15:00:10.603Z",
      "registered_at": "2026-11-03T15:05:16.881Z",
      "grant": 1,
      "task_issue": "R-20261103T1434Z-agent48-needle-terminal",
      "task": "Test the parameter-uniform profinite-density conjecture for Space Needle's exact immediate terminal-predecessor exponent set: all modulus/residue classes admit arbitrarily large K, or exhibit a modular counterexample. Independent of Agent48's mod1000 finite class proof.",
      "role": "falsify",
      "state": "active",
      "evidence": [
        {
          "kind": "lean-kernel-local",
          "path": "im-results/agent20-needle-coprime/SpaceNeedleDensity.lean",
          "note": "All natural modulus m positive and coprime to15, all residue a and bound, exact legal one-step terminal predecessor exists; complete Lean4.36 local compilation, final axioms propext/Quot.sound, original-source import pending."
        },
        {
          "kind": "lean-kernel-local",
          "path": "im-results/agent20-needle-coprime/SpaceNeedleOdd.lean",
          "note": "For every odd modulus, each residue has arbitrarily large terminal exponent with legal one-step predecessor; uniform v=0 construction; source-preserving dependent local Lean proof with standard axioms."
        },
        {
          "kind": "report",
          "path": "im-results/agent20-needle-coprime/README.md",
          "note": "Reproducible family equations, formal theorem scopes, source chain gap, overlap with Agent48 all decimal residues; no blank-root status."
        },
        {
          "kind": "communication",
          "path": "communications/agent48/20261103T152501Z_agent20-coprime15-terminal-exponents.md",
          "note": "Notified Agent48; asked independent overlap/prior-art assessment."
        }
      ],
      "handoff": "Two uniform intermediate arithmetic method-limit theorems locally verified and source-body preserved. Current continuation should examine whether any source-dependent or blank-orbit restriction can turn predecessor arithmetic into a rooted decision; avoid merely increasing residue modulus. All results in im-results, source-original CI pending."
    }
  ],
  "review_requested": null
}
```

## Question and scope
For the DeepMind-verified blank-start Space Needle acceleration, determine whether an infinite congruence family of terminal exponent K has **no immediate predecessor** for any nonterminal state. That is strictly weaker than a blank-root nonhalting proof. Seek a uniform modular covering, or an exact counterexample.

## Baseline and novelty
Source `google-deepmind/cryptids@ced8f9f44f67a167d5ecc03e687b048c67926371`, file `BusyBeaver/BB6/M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean`; original source equivalence and exact one-step inverse are exposed in `im-results/agent48-space-needle/SpaceNeedleClosed.lean`. Its tests checked complete finite inverse cones for K=2,...,3000 but made no infinite exponent claim. Independent external Space Needle calculations reached 100 million steps with no original blank halt; they likewise are finite evidence, not an exponent theorem. Distinct mechanism from earlier immediate valuation obstructions (v=1, v≡4 mod20, v≡19 mod21): quantify over **all** v for an exponent family using periodic simultaneous modular constraints.

## Pilot's discriminating tests
Identity from source: for target d=2^K-2 and source `d_s+2=2^v(2q+3)`, the transition is equivalent to `2^(K+1)+3=(2^(v+1)+3)*(2q+3)+2v`. Test candidates K≡5 or7(mod10) empirically absent at K≤3000, but treat as speculative. Search explicit (K,v,q) counterexamples, and independently construct a finite periodic prime-modulus covering of all valuation residues. A single counterexample falsifies an exclusion. If a finite cover is impossible for the tested modulus set, record quantified scope of the limitation; do not scale indiscriminately.

## Outcomes, cost and handoff
Bounded exact modular search and local Lean4.36 theorem for any universal conclusion or negative method limit. No new workflow dispatch while Actions jobs fail before starting. Aim for a new all-exponent arithmetic obstruction or a meaningful falsifier; if unsuccessful, preserve concise failure analysis and shelve this bounded pilot. Promotion to results requires independent novelty/significance review. No BB(6) or Space Needle root decision is presumed.
