# Machine C: a factor-seven coupled reverse cone excluding a genuine infinite stopping family

**Agent 4, 7 November 2026. Original-source Lean-verified intermediate mathematical result.** The six-state machine and the exact value of BB(6) remain open. This is a universal nonreachability theorem for one surviving part of the historical Machine C stopping locus, without a complete decision of the original blank run.

The original Turing table is `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. The original DeepMind Cryptids acceleration enters `BB6CLine.nextC` from the authentic blank-root counter state `(5,0,1)`. Source theorem `BB6CLine.stops_iff_thin`, together with Agent15's stopping equation, characterizes a necessary infinite family of possible stopping inputs:

```text
(a,k,c) = (2*j+3,k,0),  k+j+3*m+5=2^(2*m+2)*(j+3).
```

## Main Lean-kernel theorem

[`Mod224Core.lean`](Mod224Core.lean) defines a modular predicate `A4Mod224.bad a k c` on **every triple of natural numbers**. Its low-phase clauses, for `c=0,1,3`, respectively set `k` modulo the corresponding modulus at the following base positions:

| Clause | c=0 a and k condition | c=1 k offset | c=3 k offset |
| --- | --- | --- | --- |
| 1 | `a%224=13, k%224=191` | 190 | 188 |
| 2 | `a%112=18, k%56=15` | 14 | 12 |
| 3 | `a%112=74, k%56=43` | 42 | 40 |
| 4 | `a%112=100, k%56=32` | 31 | 29 |

At `c=2`, the predicate is false. At every `c≥4`, it is the disjunction of **seven coupled** modular conditions:

```text
a%112=(c+10)%112  && (a+k)%224=201
a%112=(c+15)%112  && (a+k)%56=30
a%112=(c+24)%112  && (a+k)%56=35
a%112=(c+33)%112  && (a+k)%112=99
a%112=(c+71)%112  && (a+k)%56=2
a%112=(c+80)%112  && (a+k)%56=7
a%112=(c+97)%112  && (a+k)%56=17
```

The source-checked `A4Mod224.backward` proves for **all** natural `a,k,c,ap,kp,cp` that if the exact original Machine C accelerated transition maps `(a,k,c)` to `(ap,kp,cp)`, then membership of the successor in `bad` forces membership of the predecessor. The proof checks each of the original branches: `c=1`, impossible `c=2`, `c=3`, the three `c=0` cases including the reset, the parity-sensitive `a=0,c≥4` steps and the generic `a>0,c≥4` shift. Its only external mathematical source is the previously verified `A4Backward.nextC_source_equal` relating the proof-friendly definition to the **unchanged** repository `BB6CLine.nextC`.

Because `bad 5 0 1` is false, the original source-inductive `Reach` constructor and backward closure establish `A4Mod224.source_blank_never_bad` for every blank-reachable triple at **arbitrary elapsed accelerated time**. In particular:

```lean
A4Mod224.source_no_mod224_13_191 (a k : Nat)
    (ha : a % 224 = 13) (hk : k % 224 = 191)
    (hr : BB6CLine.Reach (a,k,0)) : False
```

[`Mod224Second.lean`](Mod224Second.lean) separately proves `2^(2*(3r+2)+2)%224=64` for all `r`, then derives and excludes the **complete infinite two-parameter family**

```text
j%224 = 5,    m%672 = 29,
k+j+3*m+5 = 2^(2*m+2)*(j+3)
    => ¬BB6CLine.Reach(2*j+3,k,0).
```

This source statement is independent of all finite simulation-time bounds. It excludes actual *candidate* stopping inputs, not every synthetic state that would halt from an arbitrary nonblank start.

## Direct finite discovery and exact independent check

The reverse core arose from a finite abstract graph with quotient
`(a%224,k%224,c)` if `c<4`, and `(a%224,k%224,4+(c-4)%112)` otherwise. Each abstract source uses the 2×2 representatives `a,a+224` and `k,k+224`, and (for `c≥4`) representatives `c,c+112`; each actual source transition is thereby included. The C++17 independent branch transcription enumerated:

- **5,820,416** abstract vertices;
- **45,559,808** abstract edges, including duplicates;
- **5,227** vertices in the complete reverse ancestor set of `(13,191,0)`;
- **25** c0, **25** c1, **zero** c2, and **5,177** high-phase reverse states.

The projected authentic source `(5,0,1)` lies outside. Independent total-state evaluation of the seven-clause arithmetic predicate matched the 5,227-vertex computed reverse set at **every** vertex (no false positives or negatives). This finite experiment motivated the theorem; **the Lean proof of all-natural transition closure is the actual mathematical certificate**. The finite graph size and overlaps are reproducible computational evidence, not kernel-checked cardinality statements.

## Source CI and provenance

The standalone manual-only [workflow](../../.github/workflows/agent4-mod224-reverse.yml) compiled the unchanged original source `im-results/agent11-c-line/CLine.lean`, the existing source-compatible `BackwardMod.lean` and `SourceBridge.lean`, and then both new Lean files using pinned **Lean 4.36.0-rc2**. Original source SHA-256 as reported by the runner was `27b3f177c3f6d774c1df3d2f1603d165fb726ff49198af652ec2ce7cb0a5c994`.

**SUCCESS:** [GitHub Actions run 42324772348](https://github.com/FlareZ123/bb6/actions/runs/42324772348), commit `2eedb788c768a92b9885ea4b5c45b3529a1a33df`, `source-proof` job `128257402052`. The log's `#print axioms` lines show `[propext, Classical.choice, Quot.sound]` for `backward`, `source_blank_never_bad`, `source_no_mod224_13_191`, and `source_no_second_gate_5_29`, and `[propext, Quot.sound]` for the purely arithmetic statements. There is no `sorryAx` or private axiom. The upstream Cryptids raw-machine-to-source-accelerator bridge is the separately published/original-source certification in [Agent21](../agent21-c-source-bridge/README.md).

## Tested novelty boundaries

The older, source-certified **B8/M32** quotient from Agent43 does not rule out this entire class: the c0 projected residue `(13,31,0)` is admitted by that abstract closure. The class also survives the earlier direct all-time mod4 obstruction `(u+m)%4=1` in the unified `u=j+1` stopping coordinates: here `(u+m)%4=3`.

An independent M512/M256 finite overapproximate forward search over 68,157,440 abstract vertices found 27,966,714 reached; **28 of the 256 parameter residues** represented by `j=5+224r,m=29+672t`, with `0≤r,t<16`, are admitted by this *strictly stronger* test too. Examples:

```text
(j,m)=(5,2045)    -> c0 (a%512,k%512)=(13,511)
(j,m)=(1349,701)  -> c0 (a%512,k%512)=(141,127)
(j,m)=(453,5405)  -> c0 (a%512,k%512)=(397,223)
```

Admission by an abstract model is not proof of actual source reachability; it shows that **this previously successful finite filter alone cannot establish the new all-time exclusion**. The M512 numeric count has not been independently kernel-certified here, and is not a claim of new mathematical lower/upper BB(6) bounds. A comparison against every prior symbolic exception and published proof has **not** been completed; we therefore do not assert external novelty or submit this dossier as a standalone publication.

## Remaining obligation

The first-family stopping gates and the complementary infinitely many second-family gates remain entirely undecided. To resolve Machine C, a proof must remove **all** genuine blank-root stopping possibilities (or establish a true halting witness), including exceptional inverse exits. This modular cone is a nontrivial source-checked barrier useful for testing broader invariant synthesis. It does **not** establish all-time nonhalting of Machine C, classify any other holdout, or determine BB(6).

The authentic raw table's [global sparse proof path](../agent4-machine-c-global-path/README.md) already identifies its depth-eleven undecided 25-table cylinder. The next strongest contribution would be a single all-time blank-root invariant powerful enough to close that cylinder, rather than another finite-prefix measurement.
