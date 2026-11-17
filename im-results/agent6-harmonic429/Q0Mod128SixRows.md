# Six q0 root-inverse sectors on the line b = 2a - 13

**Status: derived candidate; not yet compiled against the repository's full Lean dependency closure.** This is an intermediate result, not a claim that the q0 family is closed.

## Claim to formalize

For the #429 accelerated blank-root reachability predicate `BB429NewResidue.Reach`, the following appears to follow from the already-established inverse equations, `BB429Mod8.Allowed`, and `BB429RootEven8.rooted_positive_even_eight`:

[
a\ge 10^6,\quad a\bmod128\in\{5,53,69,85,101,117\}
\quad\Longrightarrow\quad
\neg\operatorname{Reach}(a,2a-13).
]

The six residues correspond to the following q0 sectors. With
[
n=23+32u,\qquad a=13\cdot2^n-24u-19,\qquad b=2a-13,
]
we have (a\equiv-24u-19\pmod{128}), since (n\ge23). Thus:

| (u\bmod16) | (a\bmod128) |
|---:|---:|
| 1 | 85 |
| 5 | 117 |
| 7 | 69 |
| 11 | 101 |
| 13 | 53 |
| 15 | 5 |

So these six entire infinite subfamilies of the outstanding ((n\bmod32,d\bmod16)=(23,7)) class are candidates for exclusion. Ten residue classes of (u\bmod16) remain untouched by this argument.

## Exact inverse tree

Start at (P_0=(a,b)=(a,2a-13)). All six (a\bmod128) values are (5\bmod16), so (a) is odd and (b\bmod4=1). The first inverse is forced to be F:
[
P_1=\left(\frac{a-3}{2},3a-13\right).
]
Here the first coordinate is odd and the second is (2\bmod4), so the inverse splits into F and S:
[
P_{2,F}=\left(\frac{a-9}{4},\frac{7a-29}{2}\right),\qquad
P_{2,S}=\left(\frac{5a-45}{4},\frac{3a-9}{2}\right).
]
Both are odd with second coordinate (3\bmod4), hence each has only an F predecessor:
[
P_{3,F}=\left(\frac{a-21}{8},\frac{15a-67}{4}\right),\qquad
P_{3,S}=\left(\frac{5a-57}{8},\frac{11a-63}{4}\right).
]
Both first coordinates are positive even numbers. Their second-coordinate residues are:

| (a\bmod128) | (P_{3,F}.2\bmod8) | (P_{3,S}.2\bmod8) |
|---:|---:|---:|
| 5 | 2 | 6 |
| 53 | 6 | 2 |
| 69 | 2 | 6 |
| 85 | 6 | 2 |
| 101 | 2 | 6 |
| 117 | 6 | 2 |

Every row therefore has exactly one child immediately excluded by the positive-even-eight root invariant (second coordinate must be (2\bmod8)). The other child has a unique E inverse. Its coordinates simplify to:

- E after (P_{3,F}):
  [
  P_{4,F}=\left(\frac{17a-165}{16},\frac{15a-67}{8}\right).
  ]
- E after (P_{3,S}):
  [
  P_{4,S}=\left(\frac{21a-233}{16},\frac{11a-63}{8}\right).
  ]

The surviving E-parent residues and their closure are:

| (a\bmod128) | surviving branch | (P_4\bmod8) | final obstruction |
|---:|:---:|:---:|---|
| 5 | F | (3,1) | Its forced F child is positive even with second coordinate (4\bmod8). |
| 53 | S | (7,1) | Violates `Allowed` directly: (7\bmod8) requires second coordinate (2\) or (3\bmod4). |
| 69 | F | (7,1) | Same direct `Allowed` contradiction. |
| 85 | S | (1,5) | Forced F reaches an odd split state ((3,6)\bmod8); both F and S children are positive even with second coordinate (1\bmod4), contradicting the positive-even-eight invariant. |
| 101 | F | (1,5) | Same ((3,6)\bmod8) split and positive-even contradiction. |
| 117 | S | (3,1) | Its forced F child is positive even with second coordinate (4\bmod8). |

The two reusable terminal checks are elementary:

1. From an odd state ((r,s)) with ((r,s)\equiv(3,1)\pmod8), the forced F predecessor has even first coordinate and second coordinate (4\bmod8), so it is not a blank-root state.
2. From an odd state with ((r,s)\equiv(1,5)\pmod8), the forced F predecessor is odd and (\equiv(3,6)\pmod8). Its F child is even with second coordinate (1\bmod4); its S child is even with second coordinate (1\bmod4). Both violate the positive-even-eight invariant.

All states used in this finite tree remain above the inverse-lemma thresholds when (a\ge10^6). For the q0 family, (a\ge10^6) follows from (n=23+32u) and (u\ge0).

## What is and is not established

- The arithmetic tree above is a proposed exact proof from the existing inverse and root-invariant lemmas; it is not a numerical simulation.
- One row ((a\bmod128=69), equivalently (u\bmod16=7)) was proof-body checked locally against declaration stubs matching the repository theorem signatures.
- The full source dependency closure has **not** been compiled locally, so no Lean source certificate or CI claim is made here.
- This does **not** close the q0 family. The ten remaining (u\bmod16) sectors require separate treatment, including the unbounded FSFE valuation branch.
