# M16 quotient: a two-parameter high-family exclusion

**Status:** the finite quotient certificate is kernel-checked in Agent 43's M16 bundle. The parameter pullback below is an exact arithmetic derivation, but the final source-level wrapper importing the bundle's generic reachable_seen theorem has not yet been added to this directory. Do not treat the displayed Reach conclusion as a separately compiled theorem until that wrapper is checked.

## Statement

Let
\[
P_m=2^{2m+2},\qquad
a=2j+3,\qquad
k=P_m(j+3)-(j+3m+5).
\]
For all natural numbers \(m,j\) satisfying
\[
m\ge 3,\qquad j\ge3,\qquad m\equiv3\pmod4,\qquad
j\equiv m+3\pmod8,
\]
the M16 quotient maps the state \((a,k,0)\) to one of six abstract states which are absent from its certified reachable set:
\[
(15,12,0),\ (15,20,0),\ (7,20,0),\
(23,12,0),\ (7,12,0),\ (23,20,0).
\]
Consequently, once the source-Reach embedding is composed with CCert.reachable_seen, this gives
\[
\neg\operatorname{Reach}_{\mathrm{CLine}}
\bigl(2j+3,\ 2^{2m+2}(j+3)-(j+3m+5),\ 0\bigr).
\]

This is a genuinely new exclusion relative to the current highAllowedValSixFull parameter gate. It generalizes the special case \(m=3,\ j\equiv6\pmod8\).

There is also an independent \(m=0\) family with three progressions:
\[
m=0,\qquad j\ge3,\qquad j\bmod16\in\{2,3,11\}.
\]
Then \(a=2j+3\) and \(k=3j+7\). The q-state is one of
\[
(23,13,0),\ (9,16,0),\ (9,8,0),
\]
all absent from the certified seen table. For \(j=16t+2\) with \(t\ge1\), the q-state is \((23,13,0)\); for \(j=16t+3\) it is \((9,16,0)\); for \(j=16t+11\) it is \((9,8,0)\).

The full high gate accepts all three progressions: every positive-\(m\) threshold is false, the universal dyadic condition has no index because \(n+4\le2m+2=2\) is impossible, and the Agent 11 condition holds since \(j\bmod4\in\{2,3\}\). For \(j=16t+2\), \(k=48t+13\) is odd, so affineNormalize is the identity. For \(j=16t+3\), the one forced normalization step sends \((a,k)\) to \((80t+23,24t+7)\), whose right coordinate is odd; for \(j=16t+11\), it sends \((a,k)\) to \((80t+63,24t+19)\), again with odd right coordinate. In all cases the normalized right coordinate is not 4.


## Quotient and certified finite facts

Agent 43's quotient uses
\[
q(x)=
\begin{cases}
x,&x<8,\\
8+((x-8)\bmod16),&x\ge8,
\end{cases}
\]
with one representative for abstract values below 8 and the two representatives \(u,u+16\) for \(u\ge8\). Its abstract state space has \(24^3=13,824\) states.

The checked bundle reports 7,115 reachable abstract states and 34,992 representative edges. Its manual workflow is .github/workflows/agent43-c-quotient16-kernel.yml; successful run [41412951906](https://github.com/FlareZ123/bb6/actions/runs/41412951906) compiled the original CLine.lean, the M16 quotient modules, and CSourceBridge16.lean. The job checked the bundle SHA256 1cc951976c75457e35dd6ab62888cfced14e64fbf3c067d4de14f7af2fba540e.

The log records:
- CCert.reachable_seen: [propext, Classical.choice, Quot.sound];
- CCert.qMap_nextC and CCert.real_step_seen: [propext, Classical.choice, Quot.sound];
- CCert.published_next_agrees16: no axioms;
- CCert.published_reset_unreachable16: [propext, Classical.choice, Quot.sound].

The six c=0 abstract states listed above are all absent from the certified seen table. An independent exact-source-formula BFS reproduced the same 7,115-state / 34,992-edge census and checked those six absences.

## Pullback to the high parameter family

Since \(m\equiv3\pmod4\), \(m\) is odd and \(m\bmod8\in\{3,7\}\). The condition \(j\equiv m+3\pmod8\) therefore gives
\[
j\bmod8\in\{2,6\},\qquad j\bmod4=2.
\]
For \(m\ge3\), \(P_m\) is divisible by 16. Also \(a=2j+3\ge9\), and \(k>4\): using the standard bound \(P_m\ge4m+4\) and \(j\ge3\), we have \(k\ge(4m+4)(j+3)-(j+3m+5)=4mj+9m+3j+7>4\). The q-images are determined by the residues of \(m,j\) modulo 16; because \(j\ge3\), all coordinates in this high family are at least 8.

The cases are:

| \(m\bmod16\) | \(j\bmod8\) | Possible q-state(s) at c=0 |
|---:|---:|---|
| 3 | 6 | \((15,12,0),(15,20,0)\) |
| 7 | 2 | \((23,12,0),(23,20,0)\) |
| 11 | 6 | \((15,20,0),(15,12,0)\) |
| 15 | 2 | \((23,20,0),(23,12,0)\) |

Every listed state is absent from seen. The q-state of k follows from
\[
k\bmod16\equiv -j-3m-5\pmod{16},
\]
and \(k\ge8\), so \(q(k)=8+((-j-3m-13)\bmod16)\).

## Why the existing full high-parameter gate accepts the family

The current highAllowedValSixFull j m is a conjunction of the joint, Agent 11, Agent 19, Agent 29, ValSix, and affine-normalization restrictions. Each component is satisfied:

1. **Joint modular exclusions.** Here \(j\bmod4=2\), so the clauses requiring \(j\bmod4=1\) or 3, or odd \(j\), do not trigger. Also \(m\bmod4=3\), so the clause requiring \(m\bmod4\in\{0,1\}\) and the rectangle clause \(m\bmod32=5\) do not trigger. The \(m=1\) clause is inapplicable.

2. **Universal dyadic obstruction.** We have
   \[
   j+3m+3\equiv (m+3)+3m+3
   =4m+6\equiv2\pmod8.
   \]
   It is not divisible by 4. Every forbidden dyadic congruence in the universal condition requires divisibility by \(2^{n+2}\), hence by 4. Thus none can occur.

3. **Odd-special clauses.** All four require \(j\bmod8\in\{1,3,5,7\}\), whereas this family has \(j\bmod8\in\{2,6\}\).

4. **Agent 11 and Agent 19 additions.** We have \(j+m\equiv1\pmod8\), so \((j+m)\bmod4=1\), not 0. Moreover \((j+m)\bmod16\in\{1,9\}\), never 6. Since \(m\bmod4=3\), the extra \(m\bmod16=10\) clause is also false.

5. **Agent 29 and ValSix additions.** Their conditions require, respectively, \(j\bmod8=5\), \(j\bmod32=17\), \(j\bmod64=57\), or \(m\bmod32=6\); and \(m\bmod8=4\), \(j\bmod128=81\), or \(j\bmod32=1\). None can hold here.

6. **Full-gate additions.** These require \(j\bmod32=31\), \(j\bmod8=5\), or \(m\bmod32=21\), all incompatible with the family.

7. **Affine normalizer.** With \(P_m\equiv0\pmod4\),
   \[
   a+k\equiv 2j+3-j-3m-5
   =j-3m-2
   \equiv j+m-2
   \equiv3\pmod4.
   \]
   Thus the first guard \(4\le k\land k\bmod2=0\land(a+k)\bmod4=1\) is false, so affineNormalize is the identity. Also \(k>4\), so its right coordinate is not 4.

Therefore highAllowedValSixFull j m holds throughout the family, while the M16 quotient rules out its c=0 root state.

## Low-family check

The analogous low-family residues from the M16 c=0 slice are already excluded by lowAllowedValSixFull: residues 1,5,9,13 by its \(m\bmod4\ne1\) clause; 7 by \(m\bmod16\ne7\); 14 by the existing joint low predicate; and 4,12 by its \(m\bmod8\ne4\) clause. The M16 quotient contributes no new low-family exclusion over the current full gate.

## Next formalization step

Reuse the checked bundle's generic CCert.reachable_seen together with the source-Reach embedding from CSourceBridge16.lean. Add a short theorem that checks the six finite q-state absences and pulls them back through the table above. Keep the bundle SHA pinned; do not reimplement the quotient or replace the original BB6CLine.nextC.
