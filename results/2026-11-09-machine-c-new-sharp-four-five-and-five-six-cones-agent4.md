# Two new sharp Machine C image cones: exact fourth/fifth and fifth/sixth return separation

**Agent 4, 9 November 2026. Original-source Lean 4.36.0-rc2 certificates.**

## Statement and notation

Let (F=\mathrm{secNext}:\mathbb N^2\to\operatorname{Option}(\mathbb N^2)) be the **unchanged original** accelerated first-return section of the six-state two-symbol Machine C, and let (I_n) consist of states admitting exactly (n) successive successful predecessor edges starting from *any* source state. Thus (I_{n+1}\subseteq I_n). The true blank-derived section starts at ((5,1)).

The following two infinite cylinders consist of **strict, source-realizable image gaps**:

**Theorem A (sharp fourth/fifth).** For all (w,t\ge0) with (t\ge2) and (w+t\equiv1\pmod2),

\[
T_{w,t}=(64w+25,\;64t+14)\in I_4\setminus I_5.
\]

**Theorem B (sharp fifth/sixth).** For all (r,t\ge0) with (t\ge2) and (r+t\equiv0\pmod2),

\[
U_{r,t}=(64r+61,\;128t+30)\in I_5\setminus I_6.
\]

Both are permanently unreachable in the **actual blank-origin orbit**, at every natural first-return time. The two cones have asymptotic densities (1/8192) and (1/16384), respectively, in (\mathbb N^2). The lower-coordinate cutoff affects density zero. The residue pairs specifying Theorem A modulo ((128,128)) are ((25,78),(89,14)); those for Theorem B modulo ((128,256)) are ((61,30),(125,158)).

**Formal proof:** [two-parent exhaustive inverse](../im-results/agent4-c-five-image/CAltFifthArithmetic.lean), [all-time blank theorem](../im-results/agent4-c-five-image/CAltFifthSource.lean), [sharp fourth/fifth image](../im-results/agent4-c-five-image/CAltFifthStrict.lean), [sharp fifth/sixth image](../im-results/agent4-c-five-image/CAltSixthStrict.lean). All four files passed unchanged-original-source Lean CI [42642951276](https://github.com/FlareZ123/bb6/actions/runs/42642951276) and [42643884204](https://github.com/FlareZ123/bb6/actions/runs/42643884204). The imported Machine C section, complete inverse theorem, and Agent 34 image witnesses were compiled **without modification** by the workflow.

## Structural proof of Theorem A

Fix (w,t) in Theorem A and write (T=(64w+25,64t+14)). The complete original-source inverse theorem forces **every** direct predecessor of (T), including any exceptional source branch, to be one of exactly two candidates:

\[
P=(64(w+t)+37,32t+6),\qquad
H=(16(w+t)+7,24w+56t+18).
\]

The first is the genuine low/affine predecessor, and its preceding forced affine parent is

\[
Q=(64w+96t+41,16t+2).
\]

Because (t\ge2), the latter satisfies (Q_2\ge34), (Q_2\equiv2\pmod{16}) and (Q_1+Q_2\equiv3\pmod8). Agent 34's original-source theorem says (Q\in I_2\setminus I_3) and gives explicit two genuine incoming edges. The real edges (Q\to P\to T) therefore place (T\in I_4). A fifth-edge chain through (P) would give a forbidden third incoming edge to (Q).

The high-bounce parent (H) is also handled, rather than discarded: exact source inversion forces

\[
H\longleftarrow D=(40w+72t+23,12w+28t+8)
\longleftarrow E=(52w+100t+29,6w+14t+3).
\]

Since (w+t) is odd, (E_2\ge5) is odd and ((E_1+E_2)\equiv2\pmod4). The original-source odd-right image theorem forbids *any* successful incoming edge into (E). Hence the (H) branch cannot support five incoming edges to (T). Both exhaustive branches are ruled out. No finite enumeration of machine configurations or recursion-depth cutoff is used in these implications.

## Structural proof of Theorem B

Let (w=r+2t+1). Then (w+t\equiv1\pmod2), so Theorem A applies to (T_{w,t}). There is a genuine direct source return

\[
F(T_{w,t})=U_{r,t}.
\]

Moreover (U_{r,t,2}\ge6) is even and (U_{r,t,1}+U_{r,t,2}\equiv3\pmod8); the complete original-source inverse theorem forces **its sole predecessor** to be (T_{w,t}). Thus the four incoming witnesses to (T_{w,t}) extend to five for (U_{r,t}), while a six-edge chain would force five edges into (T_{w,t}), contradicting Theorem A. Source file [CAltSixthStrict.lean](../im-results/agent4-c-five-image/CAltSixthStrict.lean) also proves direct all-time blank-origin exclusion using this unique parent and the Theorem A seed obstruction.

The two cones are disjoint from the previously source-proven **Agent 4 all-depth cylinder family** (whose target first coordinate is always (3\pmod4)), because every target here has first coordinate (1\pmod4). This comparison is to that published family; it is not a claim that no other author has found overlapping restrictions.

## Genuine high-halting consequences

The original Machine C *high stopping equation* is

\[
k+j+3m+5=2^{2m+2}(j+3).
\]

This is a necessary condition for an authentic high-family stopping state ((2j+3,k)), independently of any fabricated initial tape.

**Theorem C (fourth/fifth high filter):** For all (j,m,k,n\in\mathbb N), the stopping equation and

\[
j\equiv11\pmod{32},\qquad j+m\equiv65\pmod{128}
\]

imply (F^n(5,1)\ne(2j+3,k)). The stopping equation forces (k=64t+14) with (t\ge2); the residue constraints force (t+(j-11)/32) to be odd. Formal file: [CAltFifthGate.lean](../im-results/agent4-c-five-image/CAltFifthGate.lean), checked in [CI 42642951276](https://github.com/FlareZ123/bb6/actions/runs/42642951276).

**Theorem D (fifth/sixth high filter):** For all (j,m,k,n\in\mathbb N), if

\[
j\equiv29\pmod{32},\qquad m\ge4,\qquad m\equiv j+35\pmod{256}
\]

and the same exact stopping equation holds, then (F^n(5,1)\ne(2j+3,k)). The source equation forces (k=128t+30), (t\ge2), and ((j-29)/32+t) even. Formal file: [CAltSixthGate.lean](../im-results/agent4-c-five-image/CAltSixthGate.lean), checked in [CI 42644109916](https://github.com/FlareZ123/bb6/actions/runs/42644109916).

The two high stopping parameter classes are disjoint by (j\pmod{32}), and they occupy exact asymptotic joint ((j,m))-densities (1/4096) and (1/8192), giving union density (3/8192). This is a lattice-density calculation, **not** the percentage of genuine reachable or undecided halting inputs. The complete integrated source-root sieve may remove overlapping subfamilies independently. No claim of universal novelty against that sieve is made without an exhaustive prior-filter comparison.

## Comparison with the existing forced-normalization obstruction

The repository's [full forced normalization](../im-results/agent3-c-bounce-inverse/FullForcedNormalize.lean) and its [odd-right terminal exclusion](../im-results/agent3-c-bounce-inverse/FullForcedFilter.lean) constitute a useful earlier source-exact rooted filter. **Direct symbolic substitution** into these published definitions (an arithmetic comparison, not a separate new Lean certificate) shows that neither new cone is rejected by `fullForcedExcluded` alone:

- Every (T_{w,t}) has odd first coordinate, even second coordinate, and ((T_1+T_2)\bmod8=7). Both odd-right normalization gates fail, the affine sum-one gate fails, and `sixEvenRightGate` explicitly requires sum modulo eight to differ from seven. Thus `fullForcedNormalize(T)=T`, whose even terminal right coordinate fails `fullForcedExcluded`.
- Every (U_{r,t}) has even right coordinate and sum (3\bmod8), so `sixEvenRightGate` performs the unique forced inverse step (U\mapsto T_{r+2t+1,t}). The latter is terminal as just shown, again with even right coordinate. Thus `fullForcedExcluded(U)=false`.

This is a **specific non-subsumption result relative to the existing `fullForcedExcluded` predicate**. It does not prove non-subsumption relative to every other source-certified analytic filter, and it does not imply that any new stopping parameter is blank-reachable.

### Comparison with the five original joint high exclusions

The exact original-source [Agent 3 joint high baseline](../im-results/agent3-c-bounce-inverse/JointRootQuantifier.lean) contains five universal necessary restrictions. Both new classes are retained by **all five older baseline tests**, by direct modular arithmetic:

- In the fourth/fifth class `j%32=11` and `(j+m)%128=65`, so `m%32=22`. Therefore `j%4=3`, but `(j+3*m+7)%16=4`; `m%4=2`, so neither of the mod-four multibranches applies; and `(j+3*m+5)%8=2`. The `m=1` exception is impossible.
- In the fifth/sixth class `j%32=29` and `m%256=(j+35)%256`, so `m%32=0`. Here `j%4=1`, but `(j+3*m+11)%32=8`; `(j+m)%32=29`, distinct from the older forbidden `26`; and `(j+3*m+5)%8=2`. Again `m=1` cannot occur under the required `m≥4`.

These computations give a **precise baseline non-subsumption result** for the five published `jointHighAllowed` congruences. They do not establish independence of the much stronger later Agent19/29/3/11 and physical-root filters, which must be checked separately before measuring net progress in the integrated high gate.

## A source-proven obstruction to a naive second lift

The strict fifth/sixth seed (U_{8,2}=(573,286)) has a genuine direct successor ((1,574)). The next target does **not** inherit a sixth/seventh gap. Original-source Lean [CAltSeventhCounterexample.lean](../im-results/agent4-c-five-image/CAltSeventhCounterexample.lean), passed in [CI 42646801586](https://github.com/FlareZ123/bb6/actions/runs/42646801586), constructs eight real incoming return edges:

\[
(810,143)\to(524,288)\to(997,55)\to(887,112)
\to(663,226)\to(211,454)\to(581,274)
\to(33,550)\to(1,574).
\]

The witness uses the complete unchanged-original-section inverse equivalence, including the three recursive-bounce edges with exact depths (0,1,3). It establishes ((1,574)\in I_8) and directly refutes a speculative universal (I_6\setminus I_7) claim for the next lifted class. This is a local obstruction to the *method*, not evidence of blank reachability of ((1,574)).

## Limits and research significance

These two new cones strengthen the source-realizable strict-image hierarchy, proving sharp missing fifth and sixth image bands that lie outside the previously exhibited Agent 4 bands. They exclude actual necessary high-halting states for an infinite two-parameter family **from the genuine blank start**, with no time bound. Their two-branch inverse analysis handles the high-bounce predecessor explicitly and provides a reusable pattern for other holdout cones.

They do **not** prove that Machine C never halts, resolve the remaining low or high stopping parameters, decide any other six-state holdout, or establish the exact value of BB(6). Extending the strict-image method requires control of all inverse branches where a second direct lift loses the unique-parent residue condition.
