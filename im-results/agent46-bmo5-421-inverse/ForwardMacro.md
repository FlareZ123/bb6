# Exact forward band acceleration and the positive-exit conjecture

## Complete macro

Use the accepted shared graph of #252, #421 and #754. Write P_k=5*2^k, L_k=P_k-k-3, T_k=2P_k-k-6 and q=2(x-L_k)+k+6. In band k, q has parity k and lies in [k+6,2P_k+k+2].

Set n=max{r:3^r q <= 2P_k+k+2}, z=3^n q, u=3z. The next macro event is exactly:

| Condition | Event |
|---|---|
| z=2P_k+k | Halt at T_k |
| z=2P_k+k+2 | Special arc to (k+1,3k+15) |
| otherwise u<=6P_k+k | Regular arc to (k+1,u+3-2P_k) |
| otherwise | Regular skip to (k+2,u+6-6P_k) |

The proof uses the exact same-band Q multiplier 3, its converse, the endpoint parity, and the original regular/special arc formulas. The maximal run contains no hidden terminal: all preceding states have actual outgoing arcs. Strict counter growth and determinism imply that the band-limited Boolean test is equivalent, in both directions, to reaching some terminal with band index at most the limit. No inverse search or speculative branch is involved.

The exact starting coordinates for roots 2, 3, 1 are respectively (0,6), (0,8), (0,12), the last after the arc 1->5. In the accepted original graph bridge these correspond to #421, #754 and #252.

## Proof artifacts and status

- CapPositiveMacroCore.lean: total power-of-three threshold function, maximality and uniqueness.
- CapForwardMacro.lean: coordinate realization and the four-way sound macro.
- CapForwardMacroReach.lean: bandHaltBy, exact bounded and unbounded reachability equivalences and three seed instantiations.
- CapForwardMacroSource.lean: composition with the existing original-machine root criteria; source-closure CI through agent46-bmo5-ancestry.yml target macro.

**Accepted:** [CI 45423604706](https://github.com/FlareZ123/bb6/actions/runs/45423604706) succeeded at revision 24f28fb580ceb428ea161fe87ca750b556852a73, using Lean 4.36.0-rc2, the original pinned Cryptids source, the full graph dependency chain and the three original-machine iff declarations. The workflow audits against sorryAx and native_decide. The graph-level proofs also compiled locally with standard axioms only. No nonhalting theorem for an original machine is claimed.

## Concrete all-time target

Define a total positive-exit recurrence at band k:

    r = tripleCount(2P_k-2,q)
    U = 3^(r+1) q
    q_next = U+3-2P_k.

For 1<=q<=2P_k-2, U lies in [2P_k-1,6P_k-6], and therefore q_next lies in [2,4P_k-3]. Parity alternates. This gives an unconditional total recurrence within a relaxed positive-coordinate domain. It gives an actual regular one-band transition precisely when q_next>=k+7 (assuming current q is a valid positive band coordinate). Otherwise the next step of the actual band graph first enters the negative W region of the current band, and requires the full four-way macro.

Thus a sufficient nonhalting theorem is that q_k>=k+6 forever for each of the three authentic relaxed orbits, starting #421 at (0,6), #754 at (0,8), and #252 at (1,15) after its initial special exit. A violation is a concrete first-obstruction witness, not necessarily a halt. The recurrence reduces the original question to avoiding a shrinking linear-sized strip near the lower edge of an exponentially wide normalized band.

An exact integer exploratory run through band 100000 on each root found no halt: #421 and #754 exclusively one-band regular events; #252 one initial special event then exclusively one-band regular events. There was no negative W entry or maximal same-band endpoint except #252 at band zero. The maximum same-band run lengths for roots 1,2,3 were 12,10,9. This is finite evidence only. The all-time lower inequality is still open; do not substitute a probabilistic argument or finite scan for its proof.

The full macro remains exact even if this conjecture fails. CapPositiveGate.lean formally proves the pass case, the first authentic negative state in the fail case, and the sufficient nonhalting obligations for all three seeds. It compiled locally against the exact copied graph dependencies; full source closure for this newer module is pending. Reproduce the exploratory experiment with python forward_macro_scan.py 100000.
