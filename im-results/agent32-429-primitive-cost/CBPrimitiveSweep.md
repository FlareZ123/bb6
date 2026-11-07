# C/B sweep primitive and the two open J-chart branches

**Status:** the generic transition primitive is kernel-checked in
[CBPrimitiveSweep.lean](CBPrimitiveSweep.lean). The source-specific composition
with `j_F0_prefix` remains open.

## Formal statement now available

For a configuration in state C at head (h), suppose the next (k) pairs are
`10`:

```
t(h + 2i)     = 1
t(h + 2i + 1) = 0       for every i < k.
```

The theorem `CB_sweep` proves exactly (2k) raw transitions. The head reaches
(h+2k) in state C, and each processed pair has been changed from `10` to
`01`. The proof is by induction over pairs and uses the literal #429
transition table, not a simulator or a bounded tape.

Two boundary continuations are also proved:

- If the boundary is `01` (C reads 0 and the next cell is 1), one C/0
  transition reaches D/1. The machine then has no transition. The successful
  move count from the C configuration is (2k+1).
- If the boundary is `11`, C/1 followed by B/1 reaches A two cells farther
  right. The successful move count from the C configuration is (2k+2).

The file includes kernel-checked arithmetic identities for (k=2u+2):

[
(4u^2+6u+7)+14+(4u+5)=4u^2+10u+26,
]
[
(4u^2+6u+7)+14+(4u+6)=4u^2+10u+27.
]

## Intended J-chart composition

The existing `JF0Prefix.j_F0_prefix` theorem reaches F/0 after
(4u^2+6u+7) successful moves. The raw 14-step F/0-to-C trace is the next
local setup to formalize. Its expected endpoint is C/1 at

[
h_C=-2u-3.
]

For (k=2u+2), the required pair pattern is

[
t(h_C+2i)=1,qquad t(h_C+2i+1)=0
quad (0le i<2u+2).
]

The boundary is at (2u+1), with the next cell at (2u+2):

- (w=2u-1): expected boundary `01`, hence the fatal branch and
  (4u^2+10u+26) successful moves from J, followed by the halting query.
- (wge 2u+3): expected boundary `11`, hence A at (2u+3) after
  (4u^2+10u+27) successful moves from J. This is the head coordinate
  expected for the next symbolic J state (J(2u+3,w-2u-3)).

These are **composition targets**, not yet theorems of this module. In
particular, the 14-step setup, the pair-pattern facts from the exact
`j_F0_prefix` tape, and the full output-tape equality for the nonfatal
J-to-J transition still need formal proofs. The formulas agree with the
existing 4,280-case raw simulator evidence, but that evidence is not a
substitute for the missing Lean composition.

## Reproduction

The Lean proof is compiled after `JF0Prefix.lean` by the manual workflow
`agent18-429-lastwriter.yml`. The local development proof gate used Lean
4.36.0-rc2 and a standalone copy of the exact transition semantics; the
repository workflow remains the authoritative integration check.
