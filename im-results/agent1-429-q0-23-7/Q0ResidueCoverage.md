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

Thus the current paper-level candidate reductions cover ten of the sixteen \(u\bmod16\) classes. The six remaining classes are \(u\equiv0,2,3,8,9,10\pmod{16}\). The table is a research map, **not** a formal theorem until the two proof families are compiled against the real dependency closure.

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

The first F inverse is forced:
\[
P_1=((a-3)/2,3a-13)=(5+8k,26+48k).
\]
At \(P_1\), the odd inverse splits F/S, giving
\[
P_{2F}=(1+4k,31+56k),\\
P_{2S}=(5+20k,15+24k).
\]
Both second coordinates are \(7\pmod8\). If \(k\) is even, \(P_{2F}\) has first coordinate \(1\pmod8\) and violates Allowed, while \(P_{2S}\) has first coordinate \(5\pmod8\). If \(k\) is odd, the roles reverse. Thus exactly one child can be reachable; its first coordinate is \(5+8m\), with
\[
m=5k/2\quad(k\text{ even}),\qquad
m=(k-1)/2\quad(k\text{ odd}).
\]
For \(k\equiv0,1\pmod4\), \(m\) is even.

The next three inverses are forced F, because the successive second coordinates are \(7\pmod8\), \(4\pmod8\), and \(5\pmod8\). The resulting states satisfy
\[
P_3=(1+4m,\,4\pmod8),\qquad
P_4=(2m-1,\,5\pmod8),\qquad
P_5=(m-2,\,2m+4\pmod8).
\]
For even \(m\), \(P_5\) has positive even first coordinate and second coordinate \(0\) or \(4\pmod8\), hence \(0\pmod4\). This already contradicts BB429LowOddMod8.rooted_even_parity (which requires \(2\pmod4\)); the stronger positive-even-eight theorem also suffices but is unnecessary for this four-sector extension. This gives the four additional candidate exclusions \(u\equiv4,6,12,14\pmod{16}\).

Every discarded branch is rejected by Allowed; every retained predecessor is a genuine Reach predecessor by odd_back. The bound \(a>10^6\) comfortably supplies all lower bounds and positivity conditions. This extension has been sent to Agents 6 and 39 for review; it has not yet been Lean-compiled.

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
