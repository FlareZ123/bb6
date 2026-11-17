# #429 branch-10 q0: residue-level blank-root inverse coverage

**Status: intermediate mathematical derivations, not yet Lean-compiled as a combined theorem.** This note consolidates Agent 6's six odd-u sectors with Agent 1's additional four even-u sectors. It does not decide the entire q0 family, machine #429, or BB(6).

## Family and residue parameter

For branch-10 q0, write
\[
n=23+32u,\qquad d=7,\qquad
a=13\cdot2^n-24u-19,\qquad b=2a-13.
\]
Here \(a>10^6\) for every \(u\ge0\). Since \(n\ge23\),
\[
a\equiv-24u-19\pmod{128}.
\]
The 16 values are:

| \(u\bmod16\) | \(a\bmod128\) | Candidate status |
|---:|---:|---|
| 0 | 109 | open as a family; the single seed \(u=0\) has a separate finite inverse-tree draft |
| 1 | 85 | excluded by Agent 6 six-sector tree |
| 2 | 61 | open |
| 3 | 37 | open |
| 4 | 13 | excluded by Agent 1 even-sector extension |
| 5 | 117 | excluded by Agent 6 six-sector tree |
| 6 | 93 | excluded by Agent 1 even-sector extension |
| 7 | 69 | excluded by Agent 6 six-sector tree |
| 8 | 45 | open |
| 9 | 21 | open; contains the unbounded FSFE valuation subfamily |
| 10 | 125 | open |
| 11 | 101 | excluded by Agent 6 six-sector tree |
| 12 | 77 | excluded by Agent 1 even-sector extension |
| 13 | 53 | excluded by Agent 6 six-sector tree |
| 14 | 29 | excluded by Agent 1 even-sector extension |
| 15 | 5 | excluded by Agent 6 six-sector tree |

Thus the current paper-level candidate reductions cover ten entire \(u\bmod16\) classes. Four additional \(u\bmod64\) cylinders inside the open classes 2 and 8 are excluded below, giving 44 of 64 residue classes (density 11/16). The six remaining full mod-16 classes are \(u\equiv0,2,3,8,9,10\pmod{16}\); classes 2 and 8 are only partially open after the mod-64 refinement. The table is a research map, **not** a formal theorem until the derivations are compiled against the real dependency closure.

## Six odd-u sectors (Agent 6)

The provisional derivation in [Agent 6's Q0Mod128SixRows.md](../agent6-harmonic429/Q0Mod128SixRows.md) handles
\[
u\bmod16\in\{1,5,7,11,13,15\},
\quad
a\bmod128\in\{85,117,69,101,53,5\}.
\]
Its inverse tree is:
- first F is forced because \(b\equiv1\pmod4\);
- the next odd inverse splits F/S;
- both children then have forced F inverses and yield positive-even states;
- for each residue, one positive-even state has second coordinate \(6\pmod8\), impossible by BB429RootEven8.rooted_positive_even_eight;
- the surviving \(2\pmod8\) state has a unique E parent, whose residue is one of \((3,1),(7,1),(1,5)\pmod8\);
- \((7,1)\) violates BB429Mod8.Allowed; \((3,1)\) forces F to a positive-even state with second coordinate \(4\pmod8\); \((1,5)\) forces F to an odd \((3,6)\pmod8\) state whose F and S parents are both positive-even with second coordinate \(1\pmod4\).

The \(P_4\bmod8\) cases are:
\[
\begin{array}{c|c|c}
a\bmod128 & \text{surviving }P_3 & P_4\bmod8\\
5 & F & (3,1)\\
53 & S & (7,1)\\
69 & F & (7,1)\\
85 & S & (1,5)\\
101 & F & (1,5)\\
117 & S & (3,1)
\end{array}
\]
I independently checked the displayed affine formulas, branch conditions, table, and all three terminal contradictions against the actual odd_back, even_back, Allowed, and positive-even-eight theorem statements. No omitted branch was found. This remains a mathematical review, not a full source compile.

## Four even-u sectors (Agent 1 derivation)

For even \(u\), \(a\equiv13\pmod{16}\). Write \(a=13+16k\). The four classes
\[
u\equiv4,6,12,14\pmod{16}
\]
give \(k\equiv0,1,0,1\pmod4\), respectively.

The first F inverse is forced because \(b=2a-13\equiv1\pmod4\). At the next odd inverse, the two children are
\[
P_{2F}=(1+4k,31+56k),\qquad
P_{2S}=(5+20k,15+24k).
\]
Both second coordinates are \(7\pmod8\). If \(k\) is even, \(P_{2F}\) has first coordinate \(1\pmod8\) and violates Allowed, while \(P_{2S}\) has first coordinate \(5\pmod8\). If \(k\) is odd, the roles reverse. Thus exactly one child can be reachable.

A clean affine split avoids auxiliary half-parameters:

**Case \(k=4t\).** The surviving child is \(P_{2S}\). Three further F inverses are forced, giving
\[
P_3=(1+40t,20+176t),\\
P_4=(20t-1,21+216t),\\
P_5=(10t-2,20+236t).
\]

**Case \(k=4t+1\).** The surviving child is \(P_{2F}\). Three further F inverses are forced, giving
\[
P_3=(1+8t,92+240t),\\
P_4=(4t-1,93+248t),\\
P_5=(2t-2,92+252t).
\]

In both cases \(P_5\) has positive even first coordinate and second coordinate \(0\pmod4\). This contradicts the already available BB429LowOddMod8.rooted_even_parity (which requires second coordinate \(2\pmod4\) for every positive-even reachable state). The stronger positive-even-eight theorem is unnecessary for these four sectors.

Every discarded branch is rejected by Allowed; every retained predecessor is a genuine Reach predecessor by odd_back. The bound \(a>10^6\) makes \(t\) large enough for all odd_back lower bounds and positivity conditions. This extension has been sent to Agents 6 and 39 for review; it has not yet been Lean-compiled.

## Four additional mod-64 cylinders inside the open even classes

The odd-\(m\) continuation after \(P_5\) does not close all of \(u\equiv2,8\pmod{16}\), but it does close four specific lifts. The exact \(P_5\) states are
\[
P_5=((5k-4)/2,20+59k)\quad(k\text{ even},\ u\equiv8\pmod{16}),\\
P_5=((k-5)/2,29+63k)\quad(k\text{ odd},\ u\equiv2\pmod{16}).
\]
In these two classes, \(P_5\) is odd with second coordinate \(2\pmod8\). Its F parent is positive even with second coordinate \(1\) or \(5\pmod8\), hence impossible by rooted_positive_even_eight. The S parent is odd with second coordinate \(3\pmod4\), so its next inverse is forced F. The resulting \(P_7\) residues depend only on \(u\bmod64\):

| \(u\bmod64\) | \(k\bmod32\) | \(P_7\bmod32\) | Result |
|---:|---:|---:|---|
| 2 | 27 | (25,24) | survives this depth |
| 18 | 3 | (22,30) | even first, second 6 mod8: impossible |
| 34 | 11 | (23,28) | Allowed fails: first 7 mod8, second 0 mod4 |
| 50 | 19 | (24,26) | survives this depth |
| 8 | 18 | (24,18) | survives this depth |
| 24 | 26 | (29,8) | survives this depth |
| 40 | 2 | (14,6) | even first, second 6 mod8: impossible |
| 56 | 10 | (19,28) | Allowed fails: first 3 mod8, second 0 mod4 |

Therefore the four cylinders \(u\equiv18,34,40,56\pmod{64}\) are additionally excluded. The other four lifts of the \(u\equiv2,8\pmod{16}\) classes remain open at this depth. This raises the paper-level residue coverage to 44/64, or 11/16. This refinement is also uncompiled and must not be mistaken for a full exclusion of either mod-16 class.

## Relation to the 2-adic FSFE block

The existing [FSFE-2adic-block.md](FSFE-2adic-block.md) derives
\[
v_2(z+1)=3+v_2(3u+5),\qquad z=b-a-9.
\]
For \(u\equiv9\pmod{16}\), \(v_2(3u+5)\ge4\), and this valuation is unbounded on the class. This is the genuinely unbounded repeated-FSFE branch. For \(u\equiv3\pmod{16}\), \(v_2(3u+5)=1\); for even \(u\), the valuation is zero. The six-sector proof does not touch \(u\equiv9\pmod{16}\), and the four even-sector extension uses a different inverse path.

The FSFE block is only one candidate branch: its competing F sibling at each S split must still be handled. The concrete \(u=0\) finite tree in [the q0 inverse-tree note](../agent1-429-q0-23-7-inverse-tree.md) is not a proof for all \(u\equiv0\pmod{16}\).

## Evidence boundary and next work

- The all-time source-equivalent root invariants Allowed, rooted_even_parity, and rooted_positive_even_eight have prior source-check history in the repository. The four even sectors need only the weaker rooted_even_parity theorem, already imported by Agent 1's BB429Q0Row237.lean.
- The six odd sectors and four even sectors above are not yet integrated into one Lean module with the full unchanged dependency closure.
- No local Lean compile or new CI run was possible during this review; do not call the ten-sector coverage source-certified.
- Next: have Agent 6/39 independently check and compile the even-sector extension; integrate the six+four proof modules against the actual BB429NewResidue and BB429RootEven8 imports; then attack the six remaining \(u\bmod16\) classes without fixed-depth simulation. Prioritize \(u\equiv3\pmod{16}\) separately from the unbounded \(u\equiv9\pmod{16}\) valuation branch.

All material remains in im-results/. No BB(6) value, #429 halting decision, or universal upper bound is established.
