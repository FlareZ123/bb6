# #429: all-time E right-marker and genuine A/0001 predecessor exclusion

**Original-source Lean verified:** CI [42587182635](https://github.com/FlareZ123/bb6/actions/runs/42587182635), job 129059694373, commit `f1444c82ebf0855bc985c366377ad8bbed1bb778` (source); the manually dispatched workflow rebuilt all imported original-source theorems. Proofs require exactly `[propext, Quot.sound]`, no `sorryAx`.

The original machine is `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`, on a blank bi-infinite tape. [BB429EGuard.lean](BB429EGuard.lean) proves:

1. **All-time genuine E/0 and E/1 entries have a marked immediate right neighbor**, for every raw successful blank-run time `n`. Incoming transitions to E are precisely D/0 and E/1, both writing `1` at the previous head and moving left. Thus for `R(n)=c` and `c.state=E`, `c.tape(c.head+1)=true`. This is the E/1 counterpart of Agent32's earlier F/0 blank-right invariant and holds even when the E head is scanning zero.
2. A genuine E/0 transition to A **cannot** enter the fatal A/0001 corridor (the `k=0` instance of the earlier single-state halting criterion). The newly formed A right+2 cell is the E entry's marked right neighbor, while A/0001 demands a zero there.
3. **Every genuine A/0001 is immediately preceded by B/1.** Incoming A transitions can only come from B/1 (write-one right), E/0 (write-zero left), or F/1 (write-one left). E/0 is excluded by point 2. F/1 is excluded because it necessarily marks the new A head's right+1 cell, while A/0001 needs that cell blank. The original blank start cannot itself scan A/0001. Lean proves `root_aGate_zero_only_B1` for every genuine blank-run time and a concrete immediate predecessor `j=n-1`.

This is a genuine all-time original-physical-root restriction on the `k=0` terminal pattern, not a proof that such a pattern cannot occur. For `k≥1`, an A/0 alternating corridor may still be entered from E/0 or B/1; F/1 is independently excluded by its immediate mark. Thus the all-time root problem remains.

The wider exact halt criterion, for every `k≥0`, is [Agent3's A-corridor theorem](../agent3-429-a-corridor/README.md), with score `N+1=n+2*k+4` when the terminal query counts as a step. These source results are intermediate and do not establish BB(6) or a decision for #429.

**Root-sensitive next move:** Organize the already established complete Junc/ScanE physical returns to characterize genuine A/0001 visits after B/1, and genuine E/0 outputs with `k≥1`. In particular the entire right neighbor of a genuine E configuration is known, so prepared E states with a blank immediate-right tape are unreachable from the original blank. Do not infer that a prepared E state matching a local word is physically reachable.
