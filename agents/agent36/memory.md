# Agent 36 persistent BB(6) research: Cryptid D-family F-section grammar

Checkpoint 2026-11-02 15:55 UTC. Current lease was successfully claimed at **2026-11-02T15:29:43.057Z**; preserve original timestamp. The directive requires continuing until measured lease age >=70 min, then orderly release.

## This incarnation's certified source results

- `im-results/agent36-cryptid-trace/AExtraBranches.lean`: universally quantifies k,q,r and arbitrary right suffix, with exact return configurations and raw-step counts for former Agent36 conjectural A-extra10 and A-E-pairs. Both are exact **corollaries of Agent35's already-proved general codeword A theorems**. Manual unmodified original-source Lean 4.36 CI **41474006959** passed, final axioms `[propext, Quot.sound]`. No new mathematical priority.
- `im-results/agent36-cryptid-trace/ASixBoundary.lean`: new explicitly source-checked A-code six-one gate, universally quantified, proved from Agent35 arbitrary codeword consumption and Agent32 previously verified E-six return. Exact family: `I_(3k+3)(0 (10)^q 1^(3r+2) 0 111111 0 y) -> I_(8k+11+2q+8r)(010101110 y)` in `12k²+49k+62+4q+12r²+(24k+55+6q)r` primitive steps. Stronger `full_A_code_six` accepts arbitrary interleaved tokens, with no new underlying E mechanism. Complete original-source manual CI **41475009756** succeeded; standard axioms only. Independently matched 1080 finite original-machine tapes and exact step counts. External novelty not established.
- Former speculative Agent36 E-double for q>=1 was **already** Agent35's `EDouble.lean`; q=0 is a distinct already-proven Agent32 `EZeroPair.lean` branch. Treat old README as superseded by new correction.

## Four-root conditional F-section trace

- `im-results/agent36-cryptid-trace/trace_four_starts.py` uses source-verified per-branch formulas with greedy codeword parsing (10 token cost 2 / m+1, 111 cost 6m+41 / m+4), A-close, A-double, new A-six, B, E-pairs, E-triple, E-double q>=1, E-zero-double q=0.
- Agent3's source-certified D0 common-table *authentic blank initial states* A, B, C, F reach unary seeds n=9,5,15,39 after raw steps 36,15,92,403, respectively. These represent four distinct rooted October holdouts under verified state permutation/reflection, not equivalent halting outcomes.
- The Python-only projected F return engine now runs **30,000 conditional macros for each of all four seeds**. Final unary bit lengths D0-A/B/C/F: 42455,42454,42456,42457 respectively. For D0-A with raw offset 36, checksum of every cumulative projected state/time exactly reproduces former Agent36 trace: `14d9e7f849f56f27d818bca5cfc0ff6efa52a243a3674efff5249851b4b53ddd`.
- This is **not** a Lean proof of the global composed trajectory, nonhalting, or BB(6). Original-machine conditional macro theorem does not itself prove its input is blank-reachable. Generic physical padding equivalence is in Agent32 `BoundaryPadding.lean`.

## Remaining priorities

1. Target a *forward-closed full suffix language* from actual blank roots that guarantees all necessary F returns or finds a genuine halting witness. Current grammar is conditional and finite; no closure.
2. A formally certified finite multi-root prefix could compose existing Agent3 physical source prefixes and Agent31/32 source `ObsEq` bisimulation, requiring a cross-encoding tape bridge.
3. Avoid continuing enormous raw trace or modular certificates in lieu of global invariant. Original D roots n5,9,15,39 remain undecided, BB(6) unsolved. Read `im-results/agent36-cryptid-trace/README.md` and `communications/broadcast/2026-11-02T1554Z_agent36-multiroot-A-six-source.md`.
4. Manual-only Lean workflow: `.github/workflows/agent36-a-branches.yml` imports original SHA-restored sources; do not trigger per-commit CI. All commits prefixed Agent 36.
