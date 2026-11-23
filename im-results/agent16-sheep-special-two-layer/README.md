# Sheep: two-layer exclusions for exceptional targets $3\cdot2^a$

**Agent 16, 23 November 2026.** This dossier proves exact source-law inverse grammars in several low-hidden-valuation sectors. The previous disjoint certificate excluded $158/243$ of exponents $a$ for $Y_a=3\cdot2^a$. The new [h=4 odd-sector root-leaf theorem](H4-ODD-ROOT-LEAF.md) adds a disjoint family of density $44579/172186884$, raising the stated union to $112001483/172186884\approx65.0465\%$. On that family the exact inverse chain is $Y_a\leftarrow X_a\leftarrow x_a$, with $x_a$ having no even predecessor. The new two-layer composition has an exact paper proof and a Python-integer arithmetic audit, but is not yet compiled as one Lean source-importing theorem. These are intermediate exceptional-state exclusions, not halting-power exclusions; Sheep and BB(6) remain unresolved.

## Uniform all-hidden-length generic valuation cutoff

The five explicit grammars below are instances of a **single unbounded inverse-source bound**. For every odd $a\ge3$, every even legal generic parent $x=2^b v$ of $X_a=4(2^{a+1}-1)/3$ with hidden odd-block length $h\ge0$ satisfies
$
h=0\implies b\le5,\qquad h\ge1\implies b\le2h+4.
\tag{U}
$
In particular, once $h$ is known, all source valuations can be exhaustively tested in a finite range **without a magnitude bound on $a$**. This is a paper-level lemma derived from the existing signed binary residue gap, not a new Lean-certified theorem. It works also for higher $h$ sectors not yet classified in the dossier.

**Proof.** From the exact $E$ source equations and $X_a-1=(2^{a+3}-7)/3$, an incoming generic edge must satisfy
$
3^{h+1}(2^{b+1}+1)v+
\underbrace{3^{h+1}(2b-3)+7\cdot2^{h+1}}_{K(h,b)}
=2^{a+h+4}.
\tag{U1}
$
For $b$ sufficiently large, $K(h,b)$ is a positive odd integer strictly between $1$ and $2^b$. Modulo $2^{b+1}+1$, equation (U1) would then equate $K(h,b)$ with a signed power residue $\pm2^r$, $0\le r\le b$, which is impossible: the only positive odd residue below $2^b$ is $1$. It remains to establish the claimed *uniform numeric cutoff*.

For $h=0$, at $b=6$, $K(0,6)=41<64$, with $K(0,b+1)-K(0,b)=6<2^b$ thereafter. Thus every $b\ge6$ is excluded.

For $h=1$, at $b=7=2h+5$, $K(1,7)=127<128$. For every $h\ge2$ put $B=2h+5$. The elementary inequality
$
3^h(4h+7)\le9\cdot4^h \qquad(h\ge2)
$
holds at $h=2$ ($135\le144$) and is preserved by induction, since $3(4h+11)\le4(4h+7)$ for $h\ge2$. Therefore
$
K(h,B)=3^{h+1}(4h+7)+7\cdot2^{h+1}
\le27\cdot4^h+\tfrac72\,4^h
<32\cdot4^h=2^B.
$
For any fixed $h\ge1$, increasing $b$ increases $K$ by exactly $2\cdot3^{h+1}$, and $2\cdot3^{h+1}\le6\cdot4^h<32\cdot4^h\le2^b$ whenever $b\ge B$. Hence the inequality $1<K(h,b)<2^b$ holds for all $b\ge2h+5$. The signed-power gap then proves (U). QED.

## Theorem: complete second-parent grammar

Let $E$ be the genuine Sheep first-even successor on legal even, nonterminal section counters $x=2^b v$, with $b\ge1$, $v\ge3$ odd. From the source-certified section, write $F(x)=x+b+(v-1)/2$ for $v\ge5$, $F(3\cdot2^b)=3\cdot2^b+b+3$; whenever $F(x)-1=2^h w$ with (w) odd, $E(x)=1+3^h w$.

For every **odd** integer $a\ge3$ with $a\equiv3$ or $5\pmod6$, put

$$
Y_a=3\cdot2^a,\qquad X_a=\frac{4(2^{a+1}-1)}{3}.
$$

The complete set of **even** predecessors of $X_a$ is:

| Source branch | Exact candidate | Occurs if and only if |
|---|---|---|
| Generic $h=0,b=2$ | $4(2^{a+4}-17)/27$ | $a\equiv11\pmod{18}$ |
| Generic $h=0,b=4$ | $16(2^{a+4}-29)/99$ | $a\equiv3\pmod{30}$ **and** $a\ge33$ |

No other generic valuation and no exceptional cofactor-three source is possible. The two occurrences cannot coincide because their congruences force different residues modulo 6. Every candidate in its stated range has integer odd cofactor at least five and genuinely satisfies $E(x)=X_a$.

## Companion theorem: even exponents divisible by four

For every $a\ge4$ with $a\equiv0\pmod4$, the unique legal even predecessor of $Y_a=3\cdot2^a$ is
$
Z_a=\frac{2(3\cdot2^{a+1}-1)}5.
$
The complete set of **even predecessors of $Z_a$** consists of the following two candidate branches, each present exactly under its stated condition:

| Source | Exact predecessor of $Z_a$ | Occurs iff |
|---|---|---|
| $h=0,b=1$ | $2(3\cdot2^{a+3}-9)/25$ | $a\equiv4\pmod{20}$ |
| $h=0,b=4$ | $16(3\cdot2^{a+3}-39)/165$ | $a\equiv8\pmod{20}$ |

Both formulas have legal odd cofactors $\ge5$ at the least permitted exponents $a=4$ and $a=8$. All other generic valuations and all exceptional sources are impossible. Therefore $Z_a$ is predecessor-free whenever $a\equiv0,12,16\pmod{20}$. The universal proof is given below.

## Third theorem: odd exponents with exactly one hidden odd step

Let $a\ge7$, $a\equiv1\pmod6$ and $a\not\equiv13\pmod{18}$. The direct parent of $Y_a$ in the $b=2$ sector is again $X_a=4(2^{a+1}-1)/3$. Here $v_3(X_a-1)=1$, so an incoming even $E$-edge must have $h=0$ or $h=1$. The first theorem's $h=0$ congruences cannot hold when $a\equiv1\pmod6$; the **complete** $h=1$ predecessor list is:

| Source branch | Exact candidate | Occurs iff |
|---|---|---|
| $h=1,b=1$ | $2(2^{a+5}-19)/45$ | $a\equiv1\pmod{12}$ |
| $h=1,b=2$ | $4(2^{a+5}-37)/81$ | $a\equiv37\pmod{54}$ |
| $h=1,b=3$ | $8(2^{a+5}-55)/153$ | $a\equiv13\pmod{24}$ |

There are no exceptional sources and no other generic valuations; each displayed candidate satisfying its congruence is legal and gives exactly $E(x)=X_a$. In particular, all three possible branches are eliminated if $a\not\equiv1\pmod{12}$, $a\not\equiv37\pmod{54}$ and $a\not\equiv13\pmod{24}$. The last exclusion already follows from $a\not\equiv5\pmod8$, which is also needed for $Y_a$ to have only the $b=2$ immediate parent. The complete modular proof follows below.

## Fourth theorem: exact two-hidden-step odd-sector parents

Let $a\ge31$ satisfy $a\equiv13\pmod{18}$ and $a\not\equiv13\pmod{54}$, equivalently $a\equiv31$ or $49\pmod{54}$. Then $v_3(X_a-1)=2$ and any incoming even $E$-edge to $X_a$ has hidden length $h=0,1$, or $2$. The $h=0$ branch is absent. The $h=1$ branches are still those from the third theorem ($b=1$ if $a\equiv1\pmod{12}$; $b=3$ if $a\equiv13\pmod{24}$; its $b=2$ condition $a\equiv37\pmod{54}$ cannot occur here). The **only additional possible even predecessor** is
$
x=\frac{4(2^{a+6}-83)}{243}
$
on branch $h=2,b=2$, present exactly when $a\equiv103\pmod{162}$. There are no exceptional/cofactor-three sources and no other $h=2$ generic valuations. This is a complete all-exponent source-law classification in this 3-adic stratum, proved below.

## Fifth theorem: exact three-hidden-step odd-sector parents

Suppose $a\ge13$, $a\equiv13\pmod{54}$, and $a\not\equiv67\pmod{162}$, equivalently $a\equiv13$ or $121\pmod{162}$. Then $v_3(X_a-1)=3$ and the only incoming even $E$-edge branches to $X_a$ have hidden length $h=1$ or $3$ (the earlier $h=0$ family is absent, and the $h=2,b=2$ gate requires $a\equiv103\pmod{162}$). The $h=1$ branches are $b=1$ iff $a\equiv1\pmod{12}$ and $b=3$ iff $a\equiv13\pmod{24}$. **The complete extra $h=3$ branches are**:

| Source | Exact candidate | Occurs iff |
|---|---|---|
| $h=3,b=1$ | $2(2^{a+7}-31)/405$ | $a\equiv13\pmod{108}$ |
| $h=3,b=2$ | $4(2^{a+7}-193)/729$ | $a\equiv445\pmod{486}$ |

There are no exceptional sources and no other generic valuations at $h=3$. Both candidate formulas are genuinely legal even predecessors in their congruence classes. This gives further all-time blank-root exclusions in a new, disjoint exact 3-adic stratum.

## New all-time blank-root exclusions

Define the following **disjoint** exponent sets:

$$
\begin{aligned}
A_5&=\{a\ge3:\ a\equiv5\pmod6,\ a\not\equiv5\pmod8,\ a\not\equiv11\pmod{18}\},\\
A_3&=\{a\ge3:\ a\equiv3\pmod6,\ a\not\equiv5\pmod8,\ a\not\equiv3\pmod{30}\},\\
A_0&=\{a\ge4:\ a\equiv0,12,16\pmod{20}\},\\
A_1&=\{a\ge7:\ a\equiv1\pmod6,\ a\not\equiv13\pmod{18},\
a\not\equiv5\pmod8,\ a\not\equiv1\pmod{12},\ a\not\equiv37\pmod{54}\},\\
A_2&=\{a\ge31:\ a\equiv13\pmod{18},\ a\not\equiv13\pmod{54},\
a\not\equiv5\pmod8,\ a\not\equiv1\pmod{12},\ a\not\equiv103\pmod{162}\},\\
A_3'&=\{a\ge13:\ a\bmod162\in\{13,121\},\ a\not\equiv5\pmod8,\
a\not\equiv1\pmod{12},\ a\not\equiv445\pmod{486}\}.
\end{aligned}
$$

**Corollary.** For every $a\in A_0\cup A_1\cup A_2\cup A_3\cup A_3'\cup A_5$,
$$
\neg\mathrm{SheepEven.EvenReach}\ 10\ (3\cdot2^a).
$$
These are true blank-root reachability exclusions, not a synthetic-state classification. The initial even state is $10$, while every listed first-level parent $X_a,Z_a$ and target $Y_a$ exceeds $10$.

The already known complete direct-parent grammar of [Agent 22](../agent22-sheep-special-targets/README.md) says that for odd $a\ge3$, the only possible even parents of $Y_a$ are $X_a$ and an additional $b=3$ parent precisely when $a\equiv5\pmod8$. Both sets $A_3,A_5$ exclude the latter congruence, so $X_a$ is the **unique** actual even parent of $Y_a$. Our first, third, fourth, and fifth theorems say $X_a$ has **no** even parent, excluding the five odd-sector sets $A_1,A_2,A_3,A_3',A_5$. Similarly, for every $a\in A_0$ the unique even parent is $Z_a$, which our companion theorem proves has **no** even parent. Each first-level parent differs from the blank entry $10$, so neither it nor its exceptional target can lie in the blank even-reachability orbit. Crucially, only even sources are claimed: the original `EvenEdge` constructor may admit odd source states outside the authentic even-root subgraph. The already source-certified `even_reach_preserves_even` closes this parity premise for the genuine path.

The allowed residues are exactly

$$
\begin{aligned}
A_5\pmod{72}&=\{17,23,35,41,59,71\},\\
A_3\pmod{120}&=\{9,15,27,39,51,57,75,81,87,99,105,111\},\\
A_0\pmod{20}&=\{0,12,16\},\\
A_1\pmod{216}&=\{7,19,43,55,79,115,127,151,163,187\},\\
A_2\pmod{648}&=\{31,139,211,247,319,355,463,535,571,643\},\\
A_3'\pmod{1944}&=\{175,283,499,607,823,1147,1255,1471,1579,1795\}.
\end{aligned}
$$

Thus the **new** six-sector union gives **$6/72+12/120+3/20+10/216+10/648+10/1944=389/972$** of exceptional target exponents. These are strictly disjoint from Agent 22's previously source-compiled no-direct-parent family $a\equiv2\pmod4$, of density $1/4$. The union of **these stated certificates** excludes **$1/4+389/972=158/243\approx65.021\%$** of exceptional-exponent indices; this is not a probabilistic statement about Sheep and is not necessarily disjoint from every other result in the repository.

## Proof of the complete second-parent theorem

**1. Hidden length $h=0$.** Since
$$
X_a-1=\frac{2^{a+3}-7}{3},
$$
and $a\equiv3$ or $5\pmod6$, $a+3\equiv0$ or $2\pmod6$. The powers $2^{a+3}\pmod9$ are respectively $1$ or $4$, so $X_a-1\equiv1$ or $2\pmod3$. An incoming even $E$-edge must have $h=0$, hence $F(x)=X_a$.

**2. No exceptional source.** Let $f(b)=3\cdot2^b+b+3$, strictly increasing. For every $a\ge3$,
$$
f(a-1)<X_a<f(a)
$$
because
$$
3(X_a-f(a-1))=7\cdot2^{a-1}-3a-10>0,
\qquad
3(f(a)-X_a)=2^a+3a+13>0.
$$
The first strict inequality holds at $a=3$ and is preserved when (a) increases, since its positive term doubles while the negative linear term rises by three. Thus $X_a\ne f(b)$ for any natural $b\ge1$.

**3. All generic valuations $b\ge6$ are impossible.** The exact generic equation $F(2^b v)=X_a$ becomes
$$
3(2^{b+1}+1)v+6b+5=2^{a+4}.
\tag{1}
$$
Modulo $M_b=2^{b+1}+1$, equation $1$ requires $2^{a+4}\equiv K_b=6b+5\pmod{M_b}$. But $K_b$ is odd and $1<K_b<2^b$ for every $b\ge6$ (base case (41<64), then induction). Since $2^{b+1}\equiv-1\pmod{M_b}$, every binary power residue is represented by $+2^r$ or $-2^r$, $0\le r\le b$. Among their representatives in $[0,M_b$), the only positive odd one below $2^b$ is $1$; negative representatives are at least $2^b+1$. Therefore none equals $K_b$, contradicting $1$. This is the standard signed-power residue-gap lemma, applied with the new linear offset $6b+5$.

**4. Check exactly five low valuations.** Equation $1$ also requires
$$
2^{a+4}\equiv6b+5\pmod{3(2^{b+1}+1)}.
\tag{2}
$$

| (b) | Modulus | Target residue | Exact binary-power condition |
|---|---:|---:|---|
| 1 | 15 | 11 | Impossible: powers give 1,2,4,8 |
| 2 | 27 | 17 | $a+4\equiv15\pmod{18}$ |
| 3 | 51 | 23 | Impossible: period-eight residues omit 23 |
| 4 | 99 | 29 | $a+4\equiv7\pmod{30}$ |
| 5 | 195 | 35 | Impossible modulo 5 |

The displayed multiplicative periods are respectively (4,18,8,30,12), all verifiable by elementary modular exponentiation; the only successful residues are $15\pmod{18}$ and $7\pmod{30}$. Rearranging $1$ gives the two candidate formulas. Their cofactors are odd because the numerator and denominator are odd, and they are at least five at the smallest legal exponents $a=11$ and $a=33$. The isolated congruent exponent $a=3$ in the $b=4$ branch produces cofactor **1**, so it is not a legal generic source. Substituting the legal sources into $F$ gives exactly $X_a$, which is even; hence its hidden length is zero and $E(x)=X_a$.

This completes a fully quantified elementary proof from the source-return equations. The unchanged original machine ↔ genuine even-return bridge has already been source-compiled independently; **this new two-generation composition remains to be compiled end-to-end**.

## Proof of the even-sector companion theorem

Let $a\ge4$ be divisible by four. Since
$
Z_a-1=\frac{3\cdot2^{a+2}-7}{5}\equiv1\pmod3,
$
every incoming even $E$-edge has hidden length $h=0$, so its ordinary intermediate successor is $F(x)=Z_a$. No exceptional cofactor-three source $x=3\cdot2^b$ can contribute: the strictly increasing function $f(b)=3\cdot2^b+b+3$ satisfies $f(a-1)<Z_a<f(a)$ because
$
5(Z_a-f(a-1))=9\cdot2^{a-1}-5a-12>0,\qquad
5(f(a)-Z_a)=3\cdot2^a+5a+17>0.
$
The first positive bound holds at $a=4$ and strengthens at every higher $a$.

A generic source $x=2^b v$ ($b\ge1$, odd $v\ge5$) must satisfy
$
5(2^{b+1}+1)v+10b-1=3\cdot2^{a+3}.
\tag{3}
$
Modulo $M_b=2^{b+1}+1$, this forces $3\cdot2^{a+3}\equiv K_b=10b-1\pmod{M_b}$. For $b\ge8$, $K_b$ is odd with $3<K_b<2^{b-1}+1$; the upper inequality is true at $b=8$ ($79<129$) and persists by induction. The binary residues of $3\cdot2^N$ modulo $M_b$ lie among $\pm3\cdot2^r$ for $0\le r\le b$, because $2^{b+1}\equiv-1$. For $r=0$, only $+3$ is a small odd residue. For $1\le r\le b-1$, positive representatives $3\cdot2^r$ are even, and negative representatives are at least $M_b-3\cdot2^{b-1}=2^{b-1}+1>K_b$. For $r=b$, the positive representative is $2^b-1>K_b$ and the negative representative is even. Hence $K_b$ cannot occur and **all generic valuations $b\ge8$ are excluded**.

For $1\le b\le7$, the necessary and sufficient congruence is
$
3\cdot2^{a+3}\equiv10b-1\pmod{5(2^{b+1}+1)}.
\tag{4}
$

| $b$ | Modulus | Decisive condition |
|---|---:|---|
| 1 | 25 | $2^{a+3}\equiv3\pmod{25}$, or $a+3\equiv7\pmod{20}$, hence $a\equiv4\pmod{20}$ |
| 2 | 45 | Impossible modulo 3 ($19\not\equiv0$) |
| 3 | 85 | Modulo 17 requires $2^{a+3}\equiv4$, so $a+3\equiv2\pmod8$, incompatible with $a+3\equiv3\pmod4$ |
| 4 | 165 | Equivalent to $2^{a+3}\equiv13\pmod{55}$; CRT gives $a+3\equiv11\pmod{20}$ and $a\equiv8\pmod{20}$ |
| 5 | 325 | Modulo 13 requires $2^{a+3}\equiv12$, so $a+3\equiv6\pmod{12}$, incompatible with $a+3\equiv3\pmod4$ |
| 6 | 645 | Impossible modulo 3 ($59\not\equiv0$) |
| 7 | 1285 | Modulo 257 requires $2^{a+3}\equiv23$, not one of the sixteen residues $\pm2^r$ for $0\le r\le7$ |

The underlying orders of two are $20$ modulo $25$ and modulo $55$, $8$ modulo $17$, $12$ modulo $13$, and $16$ modulo $257$. For the surviving cases, equation (3) explicitly gives the candidate cofactors $v=(3\cdot2^{a+3}-9)/25$ and $v=(3\cdot2^{a+3}-39)/165$. At the first legal exponents $a=4,8$ these are $15,37$, respectively; all later values remain odd integers at least five. Both candidates genuinely realize $F(x)=Z_a=E(x)$, completing the all-exponent classification. The three absent residue classes for $a$ have no predecessor of $Z_a$, hence their $Y_a$ cannot be reached from genuine even start $10$.

## Proof of the one-hidden-step odd-sector theorem

Assume $a\ge7$, $a\equiv1\pmod6$ and $a\not\equiv13\pmod{18}$. The identity $X_a-1=(2^{a+3}-7)/3$ and the binary powers modulo $27$ show that $v_3(X_a-1)=1$: for $a\equiv1\pmod6$, the numerator is divisible by $9$, and it is divisible by $27$ exactly when $a+3\equiv16\pmod{18}$, i.e. $a\equiv13\pmod{18}$. Thus an incoming even $E$-edge must have $h\in\{0,1\}$. The $h=0$ sector was completely classified above; its two congruences $a\equiv11\pmod{18}$ or $a\equiv3\pmod{30}$ are impossible when $a\equiv1\pmod6$.

In the only remaining case $h=1$, the ordinary intermediate successor is
$
F(x)=1+\frac{2(X_a-1)}3=\frac{2^{a+4}-5}{9}.
$
The exceptional source $x=3\cdot2^b$ is impossible: $f(b)=3\cdot2^b+b+3$ is strictly increasing and
$
9(F(x)-f(a-1))=5\cdot2^{a-1}-9a-23>0,\qquad
9(f(a)-F(x))=11\cdot2^a+9a+32>0
$
for every $a\ge7$. Hence no $f(b)$ can equal this required $F(x)$.

For a generic source $x=2^b v$, the exact equation is
$
9(2^{b+1}+1)v+18b+1=2^{a+5}.
\tag{5}
$
For $b\ge7$, $K_b=18b+1$ is odd and $1<K_b<2^b$ (base case $127<128$ at $b=7$ and induction). Modulo $M_b=2^{b+1}+1$, equation (5) would imply $2^{a+5}\equiv K_b$; this is impossible by the same signed binary-residue gap used in the first theorem. Thus $b\le6$.

The six finite valuations are decided by
$
2^{a+5}\equiv18b+1\pmod{9(2^{b+1}+1)}.
\tag{6}
$

| $b$ | Modulus | Complete decision in this $v_3(X_a-1)=1$ sector |
|---|---:|---|
| 1 | 45 | $2^{a+5}\equiv19$ iff $a+5\equiv6\pmod{12}$, i.e. $a\equiv1\pmod{12}$ |
| 2 | 81 | $2^{a+5}\equiv37$ iff $a+5\equiv42\pmod{54}$, i.e. $a\equiv37\pmod{54}$ |
| 3 | 153 | $2^{a+5}\equiv55$ iff $a+5\equiv18\pmod{24}$, i.e. $a\equiv13\pmod{24}$ |
| 4 | 297 | Modulo $27$ requires $a+5\equiv12\pmod{18}$ (even), while modulo $11$ requires $a+5\equiv7\pmod{10}$ (odd): contradiction |
| 5 | 585 | Impossible modulo $13$, since $91\equiv0\pmod{13}$ but powers of two are units |
| 6 | 1161 | Modulo $27$, $109\equiv1$ would require $a+5\equiv0\pmod{18}$, but here $a+5\equiv6$ or $12\pmod{18}$ |

The displayed discrete logarithms in the first three rows follow from orders of two $12$ modulo $45$, $54$ modulo $81$, and $24$ modulo $153$, respectively, and their explicit witness exponents $6,42,18$. All listed candidate cofactors are odd and at least five for legal exponents in the present sector (the first such source for each branch is at $a\ge25$). Substitution into (5) and the exact formula $F(x)-1=2(X_a-1)/3$ shows that their hidden length is exactly one, hence each is a genuine $E$-parent of $X_a$. This proves the complete grammar.

For a blank-root exclusion, Agent22's direct-parent grammar requires excluding the other $b=3$ parent of $Y_a$, i.e. $a\not\equiv5\pmod8$. That condition also rules out the $h=1,b=3$ branch because $a\equiv13\pmod{24}$ would imply $a\equiv5\pmod8$. Excluding the other two rows yields precisely the new set $A_1$, with ten residue classes modulo $216$. Since $X_a>10$ is then predecessor-free among even sources, neither it nor $Y_a$ can be reached from blank start $10$.

## Proof of the exact two-hidden-step stratum

Assume $a\ge31$, $a\equiv13\pmod{18}$, and $a\not\equiv13\pmod{54}$. The identity $X_a-1=(2^{a+3}-7)/3$ reduces $v_3(X_a-1)$ to the 3-adic valuation of $2^{a+3}-7$. The order of $2$ modulo $81$ is $54$, and $2^e\equiv7\pmod{81}$ exactly when $e\equiv16\pmod{54}$. Consequently $v_3(X_a-1)=2$ in the two stated exponent classes.

At $h=0$ the first theorem's source congruences cannot hold when $a\equiv1\pmod6$. For $h=1$, the exact generic source equation remains equation (5); its complete low-$b$ grammar from the third theorem applies. Its former $b=6$ rejection can also be seen unconditionally modulo $43$: equation (5) at $b=6$ would require $2^{a+5}\equiv109\equiv23\pmod{43}$, but $23$ is not a power of two modulo $43$ (order $14$). Thus the only $h=1$ branches are $b=1$ iff $a\equiv1\pmod{12}$ and $b=3$ iff $a\equiv13\pmod{24}$; $b=2$ requires $a\equiv37\pmod{54}$ and is absent in this stratum.

At hidden length $h=2$, the intermediate successor is
$
F(x)=1+\frac{4(X_a-1)}9=\frac{2^{a+5}-1}{27}.
$
The exceptional source $x=3\cdot2^b$ is impossible because the strictly increasing $f(b)=3\cdot2^b+b+3$ satisfies $f(a-2)<F(x)<f(a-1)$. Explicitly,
$
27(F(x)-f(a-2))=47\cdot2^{a-2}-27a-28>0,\qquad
27(f(a-1)-F(x))=17\cdot2^{a-1}+27a+55>0
$
for all $a\ge31$.

A generic source $2^b v$ must satisfy
$
27(2^{b+1}+1)v+54b-25=2^{a+6}.
\tag{7}
$
For every $b\ge9$, $K_b=54b-25$ is odd with $1<K_b<2^b$ (at $b=9$, $461<512$, and then induction). The signed-power residue gap modulo $2^{b+1}+1$ rules out all such $b$. The remaining eight source valuations are exhausted by the exact modular condition
$
2^{a+6}\equiv54b-25\pmod{27(2^{b+1}+1)}.
\tag{8}
$

| $b$ | Modulus | Exact decision |
|---|---:|---|
| 1 | 135 | Impossible modulo $5$: $54b-25\equiv4$, but $a+6$ is odd so $2^{a+6}\equiv2$ or $3$ |
| 2 | 243 | $2^{a+6}\equiv83$ iff $a+6\equiv109\pmod{162}$, i.e. $a\equiv103\pmod{162}$ |
| 3 | 459 | Modulo $17$, $54b-25\equiv1$ requires $a+6\equiv0\pmod8$, impossible for odd $a+6$ |
| 4 | 891 | Modulo $11$, $54b-25\equiv4$ requires $a+6\equiv2\pmod{10}$, impossible for odd $a+6$ |
| 5 | 1755 | Impossible modulo $5$: $54b-25\equiv0$ |
| 6 | 3483 | Modulo $43$, $54b-25\equiv41$ requires $a+6\equiv8\pmod{14}$, impossible for odd $a+6$ |
| 7 | 6939 | Modulo $257$, $54b-25\equiv96$ is not a binary-power residue $\pm2^r$, $0\le r\le7$ |
| 8 | 13851 | Modulo $81$ requires $a+6\equiv1\pmod{54}$, while modulo $19$ requires $a+6\equiv3\pmod{18}$: contradiction |

The residue $83$ has unique discrete logarithm $109$ modulo $162$ for the generator $2$ modulo $243$, whose multiplicative order is $162$. The resulting source cofactor $(2^{a+6}-83)/243$ is an odd integer at least five in the surviving class; it reconstructs the required $F(x)$ and true hidden length $h=2$, so the $b=2$ condition is sufficient.

For a blank-root exclusion, require that $Y_a$ have only its original $b=2$ direct parent, so $a\not\equiv5\pmod8$; this also eliminates the $h=1,b=3$ source since $a\equiv13\pmod{24}$ would give $a\equiv5\pmod8$. Exclude the $h=1,b=1$ and $h=2,b=2$ congruences as well, obtaining the stated $A_2$. Exactly ten residues modulo $648$ remain, namely $31,139,211,247,319,355,463,535,571,643$. Their intermediate $X_a$ is predecessor-free among even states and differs from initial $10$, so both $X_a$ and $3\cdot2^a$ are genuinely blank-unreachable. This fourth stratum contributes an additional disjoint density $10/648=5/324$, giving the aggregate $1/4+32/81=209/324$ for the explicitly stated certificate union.

## Proof of the exact three-hidden-step stratum

Let $a\ge13$ with $a\equiv13$ or $121\pmod{162}$. The order of $2$ modulo $243$ is $162$, and $2^{a+3}\equiv169$ or $88\pmod{243}$, respectively. In both cases $v_3(2^{a+3}-7)=4$, so $v_3(X_a-1)=3$. For $h=0$, the earlier $a\equiv3,5\pmod6$ generic gates are absent. For $h=1$, the existing complete modular grammar gives $b=1$ when $a\equiv1\pmod{12}$, $b=3$ when $a\equiv13\pmod{24}$, and $b=2$ only when $a\equiv37\pmod{54}$ (impossible here). For $h=2$, the exact grammar from the previous theorem requires $b=2$ with $a\equiv103\pmod{162}$, also impossible. Thus it remains to analyze $h=3$.

The forced intermediate section successor is
$
F(x)=1+\frac{8(X_a-1)}{27}=\frac{2^{a+6}+25}{81}.
$
The exceptional source $f(b)=3\cdot2^b+b+3$ is impossible by monotonicity and the strict bounds
$
81(F(x)-f(a-2))=13\cdot2^{a-2}-81a-56>0,\qquad
81(f(a-1)-F(x))=115\cdot2^{a-1}+81a+137>0.
$
The first inequality is true at $a=13$ and strengthens at larger $a$.

An incoming generic source $x=2^b v$ must satisfy
$
81(2^{b+1}+1)v+162b-131=2^{a+7}.
\tag{9}
$
For all $b\ge11$ the offset $K_b=162b-131$ is odd and $1<K_b<2^b$ (base case $K_{11}=1651<2048$, maintained by induction), ruling out the equation by the signed binary-power residue gap modulo $2^{b+1}+1$.

For $1\le b\le10$, equation (9) requires
$
2^{a+7}\equiv162b-131\pmod{81(2^{b+1}+1)}.
\tag{10}
$
The following table is exhaustive; $a+7$ is even.

| $b$ | Modulus | Exact modular decision |
|---|---:|---|
| 1 | 405 | Binary period 108: $2^{a+7}\equiv31$ iff $a+7\equiv20\pmod{108}$, i.e. $a\equiv13\pmod{108}$ |
| 2 | 729 | Binary period 486: $2^{a+7}\equiv193$ iff $a+7\equiv452\pmod{486}$, i.e. $a\equiv445\pmod{486}$ |
| 3 | 1377 | Modulo 17, $355\equiv15$ but even binary powers are only $\{1,4,16,13\}$ |
| 4 | 2673 | $517\equiv0\pmod{11}$ cannot equal a power of two |
| 5 | 5265 | Modulo 5 requires $a+7\equiv2\pmod4$; modulo 13 requires $a+7\equiv4\pmod{12}$: contradiction |
| 6 | 10449 | Modulo 43, $841\equiv24$ is not a power of two (binary order 14) |
| 7 | 20817 | Modulo 257, $1003\equiv232$ is not in $\{\pm2^r:0\le r\le7\}$ |
| 8 | 41553 | Modulo 27 forces $a+7\equiv2\pmod{18}$; modulo 19 the required residue is $6$, whereas $2^2\equiv4$ |
| 9 | 83025 | Modulo 15, $1327\equiv7$ is not among binary powers $\{1,2,4,8\}$ |
| 10 | 165969 | Modulo 683, $1489\equiv123$ is not among $\{\pm2^r:0\le r\le10\}$, since $2^{11}\equiv-1\pmod{683}$ |

The two surviving cofactors are $(2^{a+7}-31)/405$ and $(2^{a+7}-193)/729$, which are odd positive integers at least five for the smallest exponents $a=13$ and $a=445$, respectively, and grow thereafter. Substitution into (9) establishes the required intermediate $F(x)$, and the exact valuation 3 ensures these are genuine $E$ edges.

To exclude the original target $Y_a$ from blank start $10$, first rule out its alternative $b=3$ direct parent by demanding $a\not\equiv5\pmod8$. This also rules out the $h=1,b=3$ incoming parent of $X_a$, since $a\equiv13\pmod{24}$ implies $a\equiv5\pmod8$. Rule out $h=1,b=1$ and $h=3,b=1$ simultaneously by $a\not\equiv1\pmod{12}$, because in this valuation stratum the latter congruence $a\equiv13\pmod{108}$ is equivalent to $a\equiv1\pmod{12}$. Finally rule out $h=3,b=2$ by $a\not\equiv445\pmod{486}$. The $h=2$ gate was already absent. This leaves exactly the ten residues modulo 1944 displayed in $A_3'$, adding disjoint density $10/1944=5/972$.


## Fifth theorem: h=4 odd-sector root-leaf closure

The previously open residue sector \(a\equiv67\pmod{162}\) has a new exact subfamily. For \(a=1201+1458r\), with \(r\) in the explicit union \(R\) in [H4-ODD-ROOT-LEAF.md](H4-ODD-ROOT-LEAF.md), the unique inverse chain is
\[
3\cdot2^a\leftarrow X_a=\frac{4(2^{a+1}-1)}3
\leftarrow x_a=\frac{2^{a+10}-1868}{2187},
\]
and \(x_a\) has no even predecessor. The \(r\)-set has density \(44579/118098\), so the exponent density added is \(44579/172186884\). The new family is disjoint from the earlier six \(A_0,A_1,A_2,A_3,A_3',A_5\) progressions and the \(a\equiv2\pmod4\) family. The combined stated exceptional-target exclusion is now
\[
\frac{158}{243}+\frac{1649}{6377292}
=\frac{112001483}{172186884}\approx65.0465\%.
\]

This is a partial closure only: other \(k\)-residues in \(a=67+162k\), other \(r\)-classes in the \(k\equiv7\pmod9\) branch, and hidden lengths \(s\ge9\) remain open. The new proof is exact arithmetic plus a reproducible Python audit; it is not yet a Lean-kernel theorem composed with the original source.

## Reproduction and priority

Run [verify_second_layer.js](verify_second_layer.js) in Node.js for the earlier inverse grammars, and [verify_h4_root_leaf.py](verify_h4_root_leaf.py) with Python 3 for the new h=4 root-leaf family. The latter checks the exact modular periods, valuation-root classes, every small generic-parent hit, special-source interval inequalities, density, and CRT disjointness. These are exact arithmetic audits; the new two-layer composition is not yet a Lean-kernel theorem.

**Next mathematical task:** finish the remaining $h\ge4$ frontier without repeating the solved subfamily: classify other $k$-residues in $a=67+162k$, then the $r$-classes outside $R$ and hidden lengths $s\ge9$. Also close the alternative direct parent $b=3$ when $a\equiv5\pmod8$ and the surviving even cases $a\equiv4,8\pmod{20}$. The h=4 result is an intermediate-state exclusion only; the decisive BB(6) priority remains composing source-exact forbidden-state families into an obstruction for actual halting powers $2^j$.
