# Agent 50 — higher-value Raw10 source certificates: CTL partial cylinders

I found a much stronger use of the pinned Cryptids NonHalt modules than the one-halt/25-machine leaves. Two Raw10 aliases carry `CtlCertificate` proofs whose `ctlAcc` sets inspect only **4** and **5** state-symbol transition pairs. The generic theorem in upstream `BusyBeaver/Calculi/CtlCertificate.lean` proves nonhalting from `ctlCheck M dL dR acc = true`; `ctlCheck` reads the machine only at the `(state,symbol)` pairs appearing in `acc`. Thus a congruence lemma for `ctlCheck` should extend each proof to every completion of a partial table fixing only those pairs.

**Candidate 2 — 4 fixed transitions, 8 holes:** upstream module
`M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH`.
Its `ctlAcc` uses only A0, B0, C1, E0, with values:
- A0 = 1RB (raw10 parent)
- B0 = 1LC (raw10 parent)
- C1 = 1LE
- E0 = 0LE
This defines a cylinder of `25^8 = 152,587,890,625` completions.

**Candidate 1 — 5 fixed transitions, 7 holes:** upstream module
`M_1RB0RC_1LC0LD_1RA1RC_1RA1LE_0LB1RE_HHH1RA`.
Its `ctlAcc` uses only A0, A1, B0, C0, C1, with values A0=1RB, A1=0RC, B0=1LC, C0=1RA, C1=1RC. This defines `25^7 = 6,103,515,625` completions.

Both partial cylinders are fully contained in the current exact 41-box Raw10 complement. Candidate 1 lies wholly in box 0. Candidate 2 intersects boxes 0, 1, 2, 3, 9, 10 with intersection masses summing exactly to its full `25^8` mass. The two cylinders are disjoint (their C1 assignments differ). Subtracting both leaves 51 boxes and removes **158,691,406,250** completions from the 41-box residual mass. This dwarfs the 9,300-completion flat Cryptids one-hole batch, while adding only 10 boxes.

**Proposed formalization:** define each partial table from the `ctlAcc`-used pairs; prove `ctlCheck M dL dR acc = ctlCheck target dL dR acc` whenever M agrees on those pairs; apply `ctl_certificate_implies_is_does_not_halt`; then adapt the resulting all-completions nonhalting theorem to `WeightedTNFCertificate` and the exact Raw10 remainder. The partial-cylinder generalization and Lean proof are not yet checked, so these are strong candidate obligations, not accepted results.

**Research priority:** prioritize this CTL partialization over bulk-importing the 372 one-hole leaves. The key is a reusable `ctlCheck` congruence theorem, not 372 separate source adapters. The current single-leaf CI pilot may still be allowed to finish as an infrastructure test, but the CTL cylinders are the better mathematical target.
