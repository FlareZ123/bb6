# Suffix-[13] continuation from the offset-six countdown

## Status

This is a source-branch derivation for the pinned #85 stack system, not a Lean-checked theorem. It resolves the previously open next stack transition from the conditional state \(D_{447093083}(0;[13])\) by reducing it to an offset-six remainder-two token boundary. It does **not** establish that the blank-root path is correct, that the token boundary halts, or that the machine halts.

Pinned source: google-deepmind/cryptids at commit 3647718b5df22e1a61462dec0376bd204526285a, file BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean.

## Notation

Use first-coordinate stack notation, with \(0=(0,0)\) and \(1=(1,0)\). The existing countdown family is

\[
D_n(c;T)=CR([0],0^{4n+5}\mathbin{+\!\!+}[c]\mathbin{+\!\!+}T).
\]

Extend the offset-six family by

\[
E_n(x;T):=D_n(0;[x]\mathbin{+\!\!+}T)
=CR([0],0^{4n+6}\mathbin{+\!\!+}[x]\mathbin{+\!\!+}T).
\]

For \(T=[]\), this is the \(E_n(x)\) family already used in the offset-six notes.

## New suffix-preserving decrement

For every \(x\ge 3\) and finite suffix \(T\), the ordinary source clauses give

\[
E_n(x;T)\longrightarrow E_{n+1}(x-3;T),
\]

with exactly \(8n+26\) outer stack successors and \(24n+75\) primitive TM steps.

The phase decomposition is:

1. The eight-step source prefix (raw cost 21) sends
   \(CR([0],0^{4n+6}++[x]++T)\) to
   \(EL([0,1],0^{4n+7}++[x]++T)\).
2. The EL-right-zero sweep of \(4n+7\) successors (raw cost \(8n+14\)) sends this to
   \(EL(0^{4n+8}++[1],[x]++T)\).
3. EL-positive and DL-positive (two successors, raw cost 5) give
   \(DR(0^{4n+8}++[1],[1,x-3]++T)\).
4. The DR-left-zero/right-one sweep of \(4n+8\) successors (raw cost \(16n+32\)) gives
   \(DR([1],[1]++0^{4n+8}++[x-3]++T)\).
5. One DR-positive/positive successor (raw cost 3) gives
   \(CR([0],0^{4n+10}++[x-3]++T)=E_{n+1}(x-3;T)\).

The totals are
\[
8+(4n+7)+2+(4n+8)+1=8n+26,
\]
\[
21+2(4n+7)+5+4(4n+8)+3=24n+75.
\]

This is the offset-six analogue of the existing \(D_n(c;T)\) countdown. The suffix is carried literally through every phase; no token-normalizer branch is used.

Applying the decrement four times gives

\[
E_n(13;[])\longrightarrow E_{n+4}(1;[])
\]

in \(32n+152\) outer successors and \(96n+444\) raw steps.

## The offset-six remainder-one bridge

A separate ordinary-branch calculation gives

\[
E_m(1;[])\longrightarrow D_0(8m+9;[5])
\]

in \(8m+43\) outer successors and \(16m+115\) raw steps.

The exact phase endpoints are:

1. The eight-step prefix (raw 21) reaches
   \(EL([0,1],0^{4m+7}++[1])\).
2. The EL-zero sweep of \(4m+7\) moves to
   \(EL(0^{4m+8}++[1],[1])\).
3. EL-positive, DL-zero, EL-empty, CR-zero, and CR-\((1,0)\) reach
   \(CR(0^{4m+6}++[1],[0,5])\).
4. The CR-zero sweep of \(4m+6\) reaches
   \(CR([1],[8m+12,5])\).
5. CR-one/empty-tail reaches
   \(EL([0],[0,8m+15,5])\).
6. The 16-successor suffix-preserving general tail
   \(EL([0],[0,x]++T)\to D_0(x-6;T)\), raw cost 47,
   yields \(D_0(8m+9;[5])\).

For the general-tail phase, the 16 ordinary successors are: EL-zero, EL-positive, DL-positive, two DR-zero steps, DR-empty-left, EL-positive, DL-zero, two EL-zero steps, EL-positive, DL-positive, three DR-zero steps, and DR-positive/positive. The raw costs sum to 47. The suffix \(T\) is unchanged.

The outer and raw totals for the full bridge are respectively
\[
8+(4m+7)+5+(4m+6)+1+16=8m+43,
\]
\[
21+2(4m+7)+15+2(4m+6)+6+47=16m+115.
\]

## Application to the conditional root residual

Agent 24's preceding conditional derivation reaches

\[
D_{447093083}(0;[13])=E_{447093083}(13;[]).
\]

Set
\[
m=447093087,\quad
c=8m+9=3\,576\,744\,705,\quad
k=c/3=1\,192\,248\,235.
\]

The new bridge gives \(E_m(1;[])\), then \(D_0(c;[5])\). The suffix-preserving ordinary countdown
\(D_n(c;T)\to D_{n+1}(c-3;T)\), with \(T=[5]\), takes this to
\(D_k(0;[5])=E_k(5;[])\). One further offset-six decrement gives

\[
E_{1\,192\,248\,236}(2;[]).
\]

Exact conditional costs from \(D_{447093083}(0;[13])\):

| Phase | Outer successors | Raw TM steps |
| --- | ---: | ---: |
| \(E_n(13)\to E_{n+4}(1)\) | 14,306,978,808 | 42,920,936,412 |
| \(E_{447093087}(1)\to D_0(3,576,744,705;[5])\) | 3,576,744,739 | 7,153,489,507 |
| Suffix-preserving countdown to \(E_{1,192,248,235}(5)\) | 5,685,823,439,287,425,600 | 17,057,470,314,285,532,095 |
| \(E_{1,192,248,235}(5)\to E_{1,192,248,236}(2)\) | 9,537,985,906 | 28,613,957,715 |
| **Total** | **5,685,823,466,709,135,053** | **17,057,470,392,973,915,729** |

Adding Agent 24's preceding conditional blank-to-\(D_{447093083}(0;[13])\) count gives 19,848,692,768,628,691,148 raw steps to this next stack configuration. This total inherits the earlier path's conditional/uncompiled status and is not an established BB(6) lower bound.

The next natural target is the offset-six remainder-two token closure \(E_n(2)\). Agent 2's current intermediate note records the candidate map
\(E_n(2)\to D_0(8n+21)\), with \(8n+46\) outer successors and \(40n+196\) raw steps; that closure is also not yet compiled. At the present endpoint \(n=1,192,248,236\), its proposed target would be \(D_0(9,537,985,909)\).

## Offset-six remainder-two reset composition

The new endpoint \(E_n(2)\) can be carried one step farther using the existing token helper root_d2_dl_one_z1. The source-local phase chain is:

1. Corrected suffix-preserving prefix with \(c=0,T=[2]\): 8 outer / 21 raw, reaching \(EL([0,1],0^{4n+7}++[2])\).
2. EL-zero sweep of \(4n+7\): \(4n+7\) outer / \(8n+14\) raw, reaching \(EL(0^{4n+8}++[1],[2])\).
3. EL-positive on head 2: 1 outer / 1 raw, reaching DL with right head 1.
4. Apply root_d2_dl_one_z1 with parameter \(4n+7\): 1 outer macro successor, raw cost \(6(4n+7)+41=24n+83\), reaching \(CR(0^{4n+12}++[1],[0])\).
5. CR-zero sweep of \(4n+12\): \(4n+12\) outer / \(8n+24\) raw, reaching \(CR([1],[8n+24])\).
6. CR-one/empty-tail: 1 outer / 6 raw, reaching \(EL([0],[0,8n+27])\).
7. General tail with \(x=8n+27\): 16 outer / 47 raw, reaching \(D_0(8n+21)\).

Consequently the existing candidate map is explained by the helper composition

\[
E_n(2)\longrightarrow D_0(8n+21),
\]

with \(8n+46\) outer successors and \(40n+196\) raw steps. In the source-local Lean draft, the intended helpers are, in order:

- root_countdown_prefix_with_tail_fixed n 0 [(2,0)]
- root_countdown_el_zero_sweep (4*n+6) [(0,0),(1,0)] [(2,0)]
- root_countdown_el_positive_step 1 (replicate (4*n+8) 0 ++ [1]) []
- root_d2_dl_one_z1 (4*n+7)
- root_countdown_cr_zero_sweep_singleton (4*n+11) 0 [1]
- root_countdown_cr_one_empty_step [8*n+24]
- root_countdown_general_tail (8*n+27)

This is a proof composition over the existing uncompiled token helper, not an independent proof of that helper. At the current endpoint \(n=1,192,248,236\), it would reach \(D_0(9,537,985,909)\). Since \(9,537,985,909\equiv1\pmod3\), the next suffix-preserving countdown reaches \(D_{3,179,328,636}(1)\).

The raw cost of the E-reset itself is \(40n+196=47,689,929,636\) at the current \(n\). The following countdown has \(N=3,179,328,636\) steps, raw cost \(12N^2+57N=121,297,567,089,497,178,204\). These values remain conditional until the token helper and its dependency closure compile without axioms.

## Reproducibility and limitations

verify_suffix13_macro.py transcribes the ordinary CR/EL/DL/DR stack clauses and checks the decrement and remainder-one formulas at small parameters. The finite checks cover \(n=0,\ldots,4\) and \(x\in\{3,4,7,10,13,16\}\). They are bounded source-transcribed computation, not a proof of the quantified statements.

No token closure is used in the new decrement or remainder-one bridge. The existing suffix-preserving countdown and the prefix composition still require a corrected, compiled source-local Lean proof. The current root-to-\(D_{447093083}(0;[13])\) prefix is conditional. No blank-root halt/nonhalt decision, exhaustive maximality proof, or exact BB(6) value follows.
