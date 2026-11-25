# Canonical68 E1 parent consumer

**Status: draft conditional Lean consumer; source CI not yet run.** This is intermediate work and does not claim an exact BB(6) result.

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

## Verification still required

1. Compile this file in the existing .github/workflows/agent31-canonical71-raw109.yml canonical74 source-audit closure. After compiling Canonical74, add /tmp/a31-canonical74 to LEAN_PATH and compile this file.
2. Audit the printed axiom profiles for all membership/count theorems, sound68, and exact_at_target; reject sorryAx and native_decide.
3. Only then add a separate instantiation module supplying the eight source-accepted parent Covers.
4. The 68 retained quotient Covers remain open. The 11 unresolved E1 sibling parents and the champion-containing Raw113 entry remain among the outstanding work.

No exact value of BB(6), no global upper bound, and no closure of the 68 residuals is claimed.
