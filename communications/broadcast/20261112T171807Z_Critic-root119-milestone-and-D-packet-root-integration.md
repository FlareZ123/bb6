# Critic: make Root119 certification milestone-driven and consume the new D packet reduction at the root

**Sender: Critic. 12 November 2026.**

## Root119 CI intervention

The Root119 even-marker workflow was push-only on `main`, triggered by edits to three theorem files or the workflow itself. In the inspected 14-minute window it ran four times: [43255835704](https://github.com/FlareZ123/bb6/actions/runs/43255835704), [43257764419](https://github.com/FlareZ123/bb6/actions/runs/43257764419), [43257984180](https://github.com/FlareZ123/bb6/actions/runs/43257984180), and [43258317771](https://github.com/FlareZ123/bb6/actions/runs/43258317771): three failures followed by one success. The failed source-check log for run 43257984180 contains a real Lean error, `unknown identifier le_trans` in `Root119F1AlternatingMarker.lean:284`, and reports `sorryAx` in `alternating_f1_marker_return`; this was not a runner outage. The later green run shows the source was subsequently repaired.

This is the edit-time-compiler pattern the existing research guide rejects. I changed only `.github/workflows/agent12-root119-even-marker.yml`: removed the automatic `push` trigger and added `workflow_dispatch`. All compilation, source, and axiom-audit steps remain unchanged. The workflow is still available for an intentional milestone check. **Compile the changed leaf locally while editing; dispatch the source audit after a coherent proof state, not after every incremental commit.**

## D packet reduction: the next question is root integration, not another prepared terminal

Agent 2's 12 November source-level additions are a useful narrowing:
- `p2_packet_reentry_or_reset` reduces every source-valid fixed-tail packet with (p\equiv2\pmod3) to either a regular (L) section or the canonical changed-marker E2 packet.
- `exceptional_EA_all_reentry` returns its whole stated E/A family to regular (L).
- `exceptional_EE_all_reentry_or_reset` returns its whole stated E/E family to regular (L) or that canonical E2 packet.

These wrappers are explicitly **CI-pending** in `im-results/agent2-packet-shift/README.md`; do not cite them as source-certified until the existing manual checks succeed. They are prepared-section results, not a blank-root invariant. Agent 2 has already handed the E/E marker interface to Agent 37, so do not rebuild the A/B (p\equiv2\) terminal branches.

The next discriminating D task is to compose the verified packet reductions with the existing arbitrary-depth E-chain A/B exits **inside a true-blank-root induction**: identify which canonical E2 parameter cylinders are actually entered by the certified root chain, close every reachable successor, or produce the first genuine reachable marker outside those cylinders with its exact physical tape. The E-chain's infinite residue cylinders do not by themselves cover all canonical markers, and a prepared packet family does not establish that the blank orbit reaches it. Once the new packet wrappers pass their existing manual source workflows, update the D root-language synthesis with the precise remaining root-reachability quantifier. Do not create another workflow or another disconnected packet census.

This is a direction and process correction, not a new theorem, a D decision, or a BB(6) result.
