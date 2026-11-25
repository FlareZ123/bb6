# Domain BlockFAR and raw10 box 7

## Status (2026-11-25)

Local Lean 4.36.0-rc2 kernel accepts the complete universal **box7_upper** theorem, 37 concrete domain certificates, the generic nondeterministic BlockFAR soundness and source adapter, and domain-preserving one-halt normalization. All axiom audits report only propext, Classical.choice, Quot.sound. The exact full original-repository rebuild and weighted consumer are pending; do not yet count this as an ingested canonical cover or global BB(6) closure.

The base34 residual rectangle indexed 7 (zero based, from Raw10Encoded.lean) fixes the first nine rows:
`[8,14,11,7,17,4,9,2,23]`. E1 ranges over 0..24 except 15; F0 and F1 range over 0..24. Thus 15,000 tables. Code 0 is halt, 1+4*q+2*w+r represents an ordinary move. Each slot admits an ordinary replacement. Among 1,680 single-halt representatives, 1,047 halt with score <=36, 633 have checked nonhalting certificates. The six cases open after the short side-cycle scan are (3,16,0), (14,1,0), (17,1,0), (19,1,0), (19,12,0), (24,1,0). All six are covered. The 37 certificates jointly cover the entire nonhalting single-halt slice. This is a universal rectangle theorem, not a sample.

## Reusable method

The domain checker allows any permitted action on every visit to a slot, so even an adversarial nondeterministic choice cannot halt on a checked graph. Each graph comprises a finite subset of the 144 microstates of a three-cell block (6 states x 3 positions x 8 words). It contains the entry, all internal successors, and verifies every possible exit against the same left-DFA/right-NFA invariant as Agent13's BlockFAR. Safe cycles inside the block are allowed. No step bound, deterministic-exit hypothesis, or trust in Python saturation is needed. Domain-preserving normalization is necessary because the original one-halt normal form's fallback move need not be in the given box. The new proof keeps the actual halt and every visited ordinary transition, filling other halt rows with allowed ordinary moves.

## Reproduction

The source archive is stored compactly because the local environment cannot push by git. The connector blob hash matched the local Git object exactly. SHA256 `13192eb6b8c2354f684fbe18801ed2b8077b01c633236b7e37d5cb3a2351efa7`. It contains readable Lean files, untrusted generator, the fixed 37-group manifest, and a reproducible build script. No olean files or generated bulk proof data included. From repository root, run `bash im-results/agent49-domain-blockfar/check.sh` with Lean 4.36.0-rc2 on PATH. The generator replays the fixed manifest, not the exploratory greedy search. All concrete checks use `decide +kernel`.

Local build used the existing BlockMacro, BlockFAR, RangeCheck, Frontier, OneHalt, BlockFARBridge proof bodies (copied into the sandbox; comments or equivalent minor proof syntax may differ). The script uses the actual repository modules. The final theorem is `BB6.Agent49Box7.box7_upper` and bound is the ordinary BB score, i.e. number of successful transitions plus the final halt. Adding at most five blank-delay steps yields weighted bound 41. The separate weighted adapter should be compiled in the upstream source closure; see Box7Weighted.lean. No coverage mass should be counted globally until exact parent/box identity and weighted source consumer are accepted.
