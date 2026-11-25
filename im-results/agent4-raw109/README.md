# Raw109: complete candidate parent bound, sharded source audit

Raw109 is the six-hole parent
`1RB---_1RC---_0RD---_1LD1RE_---1RB_------`
with 25^6 = 244,140,625 compatible completions. The first unassigned
query is B1 at primitive step 7. Eleven moving choices have immediate
side-cycle certificates, the halt choice is bounded at the query, and
all thirteen other moving choices have complete candidate trees with
no unresolved exception hypotheses.

**Current status:** the unconditional theorem
`BB6.Agent4Raw109Closed.all_closed` in [Raw109Closed.lean](Raw109Closed.lean)
would bound every compatible machine at weighted score 1703. The
four-child audit 45551831758 and final two inductive leaf audit
[45581032451](https://github.com/FlareZ123/bb6/actions/runs/45581032451)
passed, but the full parent audits have not completed. The latest
[45595224651](https://github.com/FlareZ123/bb6/actions/runs/45595224651)
was cancelled during Raw109B1LFKid05 compilation, not at a mathematical
counterexample or a reported Lean error. Earlier source fixes corrected
Raw109LA454 witness order and Raw109LC354 rewrite direction. No canonical
address is removed on the basis of this candidate alone.

## Exhaustive candidate partition

| B1 | Weighted bound | Initial open leaves | Split nodes |
| --- | ---: | ---: | ---: |
| 0LD | 324 | 320 | 595 |
| 0RE | 353 | 110 | 392 |
| 0LC | 240 | 171 | 738 |
| 1RE | 119 | 670 | 445 |
| 1LB | 127 | 2132 | 766 |
| 0RF | 461 | 498 | 908 |
| 1RF | 268 | 699 | 972 |
| 1LC | 162 | 430 | 1115 |
| 0LA | 168 | 691 | 1077 |
| 1LA | 177 | 1383 | 1415 |
| 0RC | 1703 | 224 | 594 |
| 1LF | 658 | 2360 | 2112 |
| 0LF | 904 | 1617 | 1314 |

[specs.json](specs.json) specifies each open-list hash, exact first
query, and complete assignment of nonhalting/finite certificates. The
parent composition imports the initial 0LD/0RE root cut and eleven
remaining child closures.

## Hardest final leaves

For B1=0LF the 1617 open leaves consist of 1428 pooled FAR certificates,
32 extra FAR certificates, 104 n-gram certificates, 46 single-block
sweeps, 5 long-epoch sweeps, and two handwritten inductive certificates.
The independently reproduced open-list SHA-256 is
`413916c71af62ae660bf5feb4939bf663d7e0706a0c7e0b210d341f00c79455a`.

- [Leaf 1475](Raw109LF1475.lean), table
  `1RB0RB_1RC0LF_0RD0RA_1LD1RE_---1RB_1LB1LF`:
  B zipper return (P L,0) -> (P I L,0) in 532 steps, with
  P=00011011101100 and I=10011111111111, and blank entry at 643.
- [Leaf 1200](Raw109LF1200.lean), table
  `1RB0RA_1RC0LF_0RD1RA_1LD1RE_---1RB_0LB1LF`:
  use Y=1101, V=0110, Z=1011 and a B section with left Y^k
  behind the scanned head and right word W including that head.
  Blank enters at t=40, k=2, W=00. Exact arbitrary-tail base and deep
  macros increase k by two; a 22-state DFA proves closure and complete
  prefix coverage, including recursively consumed V blocks. Padding
  congruence and arbitrary live prefixes lift to original-machine
  nonhalting. Both original-source wrappers passed run 45581032451.

Earlier reusable counter arguments and finite child certificates remain
in the [historical detailed dossier](history-before-sharded.md) and
the individual Lean files.

## Reproducible, interruption-tolerant parent acceptance

Use the existing manual `agent10-four-hole.yml` target
`raw109-sharded`. Seven jobs check all thirteen child trees
independently, retaining exact source/object manifests and logs, with
fail-fast disabled. The final job uses [merge_shards.py](merge_shards.py)
to reject source, compiler, revision, generated-input or object
disagreements; it restores generated sources into the original paths
without overwriting changed tracked files. The strict shared compiler
then rechecks dependency identities and compiles only Raw109Closed.
The final artifact is accepted only if every dependency is reused and
the exact exported parent axiom profile contains solely standard Lean
axioms. No monolithic rerun is needed after a successful shard.

The merger passed a local seven-shard positive fixture and a conflicting
shared-object rejection fixture. A minimal Lean 4.36.0-rc2 object compiled
in two distinct local directories had identical hashes; this is a
preflight, not a guarantee that the actual distributed objects match.
Local Git clone remains blocked by DNS resolution, so exact repository
source compilation is delegated to this focused CI target.

Once the final assembly is source-accepted, provide the full artifact
and manifest to the canonical roster maintainer. Exact compatibility of
raw109 with a retained canonical representative must be separately
checked at the common bound B. Until that graft succeeds, the global
residual count and BB(6) status remain unchanged.
