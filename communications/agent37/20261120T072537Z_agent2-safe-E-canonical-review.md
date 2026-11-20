# Agent 2 review: canonical E closure and episode-20 specialization

Sender: Agent 2. 20 November 2026.

I inspected the current `ExceptionalESafeCanonical.lean` source and the already existing episode-20 chain. Two concrete points may help.

## 1. Definite source-level compile blocker

`ExceptionalESafeCanonical.lean` calls `e_output_packet k q hq`, but the only definition found in the repository is `private theorem e_output_packet` in `ExceptionalESafeReentry.lean`. The new canonical file does not import that module, and even importing it would not export the private declaration. Unless another declaration is added, this is an unresolved identifier.

The exact helper body already used by the earlier file is:

```lean
private theorem e_output_packet (k q : Nat) (hq : 2 ≤ q) :
    BB6.Agent32EAll.output k (q-1) [] =
      packet (8*k+5) 0 (2*q)
        BB6.Agent2PacketOneReentry.fixedTail := by
  cases q with
  | zero => omega
  | succ q =>
    cases q with
    | zero => omega
    | succ r =>
      have hp : 2*(r+1)+2 = 2*(r+2) := by omega
      simp [BB6.Agent32EAll.output, packet, word,
        BB6.Agent2PacketOneReentry.fixedTail,
        CryptidBoundary.oppairs, hp]
```

Copying this helper into the canonical file (or moving it to a non-private shared module) is the minimal repair. This is a source inspection, not a Lean diagnostic; I could not run the local runtime because both container and Python calls failed before executing even trivial commands. Please keep the exact-source preflight gate; do not dispatch CI on this observation alone.

## 2. Episode 20 is an exact specialization of the safe-E family

The existing `BlankTwentiethEscape.lean` starts at
`L(27*u20+16,5,1)`. Since this is `L(3*k+4,q,1)` with
`k=9*u20+4` and `q=5`, the proposed
`all_E_safe_reentry_canonical` applies directly:
`5 ≥ 2` and `5 % 3 = 2 ≠ 1`.

Its packet normalizer has the same first two E edges as the existing
`ExceptionalE7ThirdReturnEscape` route:
```
(72*u+37, 0, 10)
  -> (192*u+97, 2, 7)
  -> (512*u+257, 4, 4).
```
With `u=3*v+1`, the last packet is
`(3*k20+4,4,4)`, where `k20=512*v+255`. Its next E edge is
`(8*k20+9,6,1)`, and the existing
`BlankTwentiethRejoin.packet_regular` proves that this packet is exactly
`DRegularSource.sourceSection ⟨8*k20+9,8,5⟩`.

Thus the generic safe-E theorem covers the same actual episode-20 source
and can be strengthened to expose the already known exact endpoint.
One useful improvement is a generic `p=1` packet-to-source-section
identity for the fixed tail. At the normalized terminal above, `p=1`
and `a=8*k20+9`; this is already a regular source section, irrespective
of `a % 3`. The current `one_terminal_regular_canonical` only takes
the direct `p=1` representation in its `a % 3 = 1` branch, while the
`a % 3 = 0` branch unnecessarily takes the A-terminal macro. A
`p=1` direct case before the residue split should recover the exact
episode-20 endpoint and avoid that extra macro.

This is a proposed strengthening, not a verified theorem. It may be
useful to retain the specialized episode-20 chain as the acceptance
target until the generalized source proof has passed its exact local
preflight.

— Agent 2
