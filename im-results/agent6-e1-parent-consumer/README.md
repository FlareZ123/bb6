# Canonical68 E1 parent consumer

**Status: source-audited conditional Lean consumer.** The combined Canonical74 + Canonical68 source-audit job passed in run 45725315357; the Canonical68 artifact is 15074083310. This is a conditional reduction, not an exact BB(6) result.

## Purpose

The accepted canonical76 core has a 76-entry quotient roster. Agent31's existing Canonical74Raw109Raw123Graft.lean removes the source-accepted Raw109 and Raw123 parent cylinders, leaving 74 representatives. This module consumes the other six source-accepted E1 sibling parents, yielding a conditional 68-entry residual roster.

The eight E1 parent bounds and common target floor are:

| Parent | E1 move | Accepted parent bound |
|---|---|---:|
| Raw60 | 1RA | 1,175 |
| Raw109 | 1RB | 1,703 |
| Raw110 | 0LC | 6,766,859 |
| Raw111 | 0RC | 7,014 |
| Raw117 | 1RD | 1,291 |
| Raw121 | 1RE | 4,063 |
| Raw123 | 0RF | 10,000 |
| Raw125 | 1RF | 1,290 |

Raw110 sets the binding floor 6,766,859. Raw109 and Raw123 are already consumed by the Canonical74 module. This module defines and consumes Raw60, Raw110, Raw111, Raw117, Raw121, and Raw125.

## Lean interface

- Canonical68E1ParentGraft.lean imports the Canonical74 source consumer.
- The six new parent tables are reconstructed from the common four-step E1 prefix and their E1 move.
- Each parent has a sameTable membership-count theorem in the current roster, followed by sequential empty-replacement grafts:
  roster74 → roster73 → roster72 → roster71 → roster70 → roster69 → roster68.
- The theorem count68 records the exact retained roster length.
- The theorem sound68 consumes the eight parent Covers and leaves every other quotient-compatible parent explicit.
- The theorem exact_at_target is conditional on the 68 retained Covers and a champion witness.

The module deliberately takes the six new Covers as premises rather than importing their large source proof closures. The individually accepted parent proofs must be wired into an instantiation module after this conditional consumer compiles.

## Verification and remaining work

The existing .github/workflows/agent31-canonical71-raw109.yml now compiles this file immediately after Canonical74. Run 45725315357 passed the source compile and explicit axiom gate for all six new membership counts, roster lengths 73 through 68, sound68, and exact_at_target. The allowed axiom profile is propext, Classical.choice, and Quot.sound; no sorryAx or native_decide was accepted. The uploaded artifact includes the Canonical68 .olean, source, summary, and axiom profiles.

The eight source-accepted parent proofs can be supplied through their existing interfaces: Raw60 cover_at_target, Raw109 all_closed, Raw110 raw110_cover, Raw111 all_completions, Raw117 all117, Raw121 all121, Raw123 raw123_cover, and Raw125 raw125_cover. This module deliberately leaves those as explicit Cover premises rather than importing their heterogeneous proof closures. A separate instantiation module remains useful but is not required for the conditional theorem.

The 68 retained quotient Covers remain open. The 11 unresolved E1 sibling parents and the champion-containing Raw113 entry remain among the outstanding work. Raw110 sets the binding floor at 6,766,859; this does not establish a tight bound at the current champion score.

No exact value of BB(6), no global upper bound, and no closure of the 68 residuals is claimed.
