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

Thus the current paper-level candidate reductions cover ten entire \(u\bmod16\) classes. The six remaining mod-16 classes in this provisional derivation are \(u\equiv0,2,3,8,9,10\pmod{16}\). The older manual mod-64 table is superseded by the independent depth-16 computation below. The table is a research map, **not** a formal theorem until the derivations are compiled against the real dependency closure.

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

## Corrected fine-residue coverage

Agent 6's [depth-16 sieve](../agent6-harmonic429/Q0Depth16InverseSieve.md) uses the exact F/S/E inverse grammar together with the listed source-certified root invariants. Its computed surviving base classes number 31,376 modulo 2^22, with projection modulo 64:

    0,2,8,9,16,19,24,25,26,35,41,42,50.

Thus the finite computation reports 51 excluded mod-64 cylinders, with the 13 above still open (the u=0 point is checked separately). It is a computational necessary-condition sieve, not a Lean theorem or a reachability proof.

**Correction to the former manual table:** for even u, a=13+16k and k=(-24u-32)/16 mod 32; u=26 mod 64 gives k=23 mod 32, not 7. The latter belongs to u=58 mod 64. Moreover a residue for k modulo 32 cannot in general determine all divided-coordinate residues modulo 32. The previous 49/64 paper-level count and finer tables are withdrawn. Agent 6 gives the counterexample u=2330 with a depth-16 invariant-compatible inverse path, so the entire u=26 cylinder cannot be excluded by the old table.

The broad four-even-sector formulas above remain provisional paper derivations. No combined original-source Lean theorem is claimed.

## Unbounded tail obstruction

The [FSFE valuation clock](FSFE-2adic-block.md) is not the only obstacle to a fixed-depth inverse proof. The [corrected FSFE sibling analysis](FSFE-valuation-tail.md) and [Q0SecondarySpine.lean](Q0SecondarySpine.lean) give an all-depth arithmetic theorem: for every K some actual q0 parameter admits (FSFE)^3 F^K while passing the full depth-16 sieve's residue predicates. No fixed cap on the suffix length after three blocks suffices. See [the exact theorem and scope](Q0SecondarySpine.md).

The missing quantifier is genuine blank-root ancestry for every surviving parameter. Do not extend the same bounded sieve without a new invariant or an accelerated, fully covered recursive tail argument. No #429 decision or BB(6) value follows.
