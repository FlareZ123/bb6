# C/B sweep primitive and J-chart composition status

**Status:** the generic C/B transition primitive is kernel-checked in
[CBPrimitiveSweep.lean](CBPrimitiveSweep.lean). Its source-specific
composition is now closed for the two outer J-chart branches by
[Agent1's J-first-branch proof](../agent1-429-j-first-branch/README.md).

## Formal statement now available

For a configuration in state C at head (h), suppose the next (k) pairs
are `10`:

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

## J-chart composition now proved

The source-specific setup is no longer an open obligation:

- `JF0Prefix.j_F0_prefix` reaches F/0 after (4u^2+6u+7) successful moves.
- The exact 14-step F/0-to-C/1 setup is proved.
- The `10`-pair pattern for (k=2u+2) is derived from the full
  `j_F0_prefix` tape.
- The C/B sweep and final boundary transitions are composed with complete
  output-tape equality.

For (w+1=2u), the boundary is `01`, so the raw J configuration makes
(4u^2+10u+26) successful moves and then halts on the D/1 query.

For (w\ge 2u+3), the boundary is `11`, so the raw J configuration makes
(4u^2+10u+27) successful moves and returns to the translated J chart
(J(2u+3,w-2u-3)).

The continuation branch is further composed through arbitrary consecutive
high-3 segments in
[Agent32's High3Ladder.lean](../agent32-429-high3-ladder/High3Ladder.lean).

## Remaining cases and scope

The three neighboring parameter cases (w=2u), (w=2u+1), and
(w=2u+2), plus the (w<2u) families, remain open as raw J-chart return
theorems. The exact raw branch results still do not prove that the authentic
blank-start orbit reaches any arbitrary synthetic J parameter. The separate
raw-to-Cryptids encoding bridge is also not yet CI-accepted; see
[Agent1's JSourceBridge.lean](../agent1-429-j-first-branch/JSourceBridge.lean).

## Reproduction

The generic C/B lemma is compiled by the manual workflow
`agent18-429-lastwriter.yml`. The source-specific outer-branch composition
and the arbitrary high-3 ladder are compiled by
`agent32-429-raw-parent.yml`; the latter passed in
[CI run 42399391414](https://github.com/FlareZ123/bb6/actions/runs/42399391414).
