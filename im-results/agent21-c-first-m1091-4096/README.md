# Machine C low first-stop inverse exclusions

<badge>Not a BB(6) decision</badge>

**Status: original-source Lean verified.** The focused manual workflow [45154176898](https://github.com/FlareZ123/bb6/actions/runs/45154176898) completed successfully with Lean 4.36.0-rc2. The axiom reports for both final theorems contain only `propext`, `Classical.choice`, and `Quot.sound`; neither contains `sorryAx`.

## Theorem

For the unchanged Machine C section transition `BB6.Agent46.secNext`, starting from the blank-origin section state `(5,1)`, consider a low first-stop target `(1,k)) satisfying

[
k+3m+4=2^{2m+3}.
]

The original blank-origin orbit never reaches `(1,k)) if either

[
m\equiv1091\pmod{4096}
\qquad\text{or}\qquad
m\equiv12355\pmod{16384}.
]

The formal results are:

- `BB6.Agent21Low1091.first_stop_m1091_mod4096`
- `BB6.Agent21Low1091.first_stop_m12355_mod16384`

Each theorem excludes the target at every finite section-run time. This is not a bounded simulation result.

## Shared exact inverse chain

Writing (k=1024q+819), the complete original-source inverse classification forces the following five predecessor edges:

[
egin{aligned}
(1,1024q+819)
&\leftarrow(512q+408,768q+612)\\
&\leftarrow(1280q+1018,384q+305)\\
&\leftarrow(832q+659,608q+481)\\
&\leftarrow(720q+568,664q+523)\\
&\leftarrow(692q+543,678q+532).
end{aligned}
]

The arrows point from a target to its uniquely classified immediate source parent. The final state has even right coordinate. The source-certified even-right theorem forces the direct predecessor
[
(x,y)\longmapsto(x+y-2,(y-2)/2)
]
whenever (y\ge6) is even and ((x+y)\bmod8\notin\{0,7\}).

### First cylinder: (q\equiv0\pmod4)

For (m=4096r+1091), the stopping equation implies
[
q+12r+4=2^{2m-7},
]
so (q\equiv0\pmod4). One further direct even-right reduction reaches
[
(1370q+1073,339q+265).
]
Its right coordinate is odd and its coordinate sum is (2\pmod4).

### Second cylinder: (q\equiv11\pmod{16})

For (m=16384r+12355), the stopping equation implies
[
q+48r+37=2^{2m-7},
]
so (q\equiv11\pmod{16}). Writing (q=16v+11), three further direct even-right reductions reach
[
(30056v+22129,1356v+997).
]
Again, the right coordinate is odd and the coordinate sum is (2\pmod4).

The source-verified all-time blank-section theorem `BB6.Agent38.blank_section_mod4` forbids such a state when the right coordinate is at least five. Both terminal right coordinates satisfy that bound.

## Relation to the exact Machine C criterion

Both progressions pass the previously maintained low restrictions: in particular, they have (m\equiv67\pmod{1024}), (m\equiv3\pmod{16}), and (m\not\equiv0\pmod{128}). Thus these are additional exclusions, not restatements of the earlier `jointLowAllowed`, `Agent11Joint.lowAllowed`, or `lowAllowedValSixFull` predicates.

The next useful step is to compose these two exclusions into a separate strengthened low-parameter predicate around `ValSixJointFull.lean`, while preserving its existing exact equivalence. The remaining low and high parameter existentials are still unbounded. Machine C halting and BB(6) remain unresolved.

## Reproduction

- Proof source: [`Low1091Source.lean`](Low1091Source.lean)
- Manual source workflow: [`agent21-low1875-source.yml`](../../.github/workflows/agent21-low1875-source.yml)
- Successful original-source verification: [GitHub Actions run 45154176898](https://github.com/FlareZ123/bb6/actions/runs/45154176898)
