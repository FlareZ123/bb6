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

with exactly \(8n+26\) individual mode successors and \(24n+75\) primitive TM steps.

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

A direct source-local Lean composition for this decrement can avoid the general-tail helper entirely. After the corrected prefix helper, the required existing sweep/branch lemmas are:

- root_countdown_prefix_with_tail_fixed n 0 ((x,0)::T)
- root_countdown_el_zero_sweep (4*n+6) [(0,0),(1,0)] ((x,0)::T)
- root_countdown_el_positive_step (x-1) (replicate (4*n+8) 0 ++ [1]) T
- root_countdown_dl_positive_step (x-3) (replicate (4*n+8) 0 ++ [1]) T
- root_countdown_dr_zero_sweep (4*n+7) [1] ((x-3,0)::T)
- root_countdown_dr_positive_positive_step 0 0 [] (replicate (4*n+8) 0 ++ [(x-3,0)] ++ T)

The only nontrivial arithmetic normalization is \((x-3)+2=x-1\), discharged by omega under \(3\le x\). List normalization uses List.replicate_succ, List.cons_append, and List.append_assoc. The final DR positive/positive lemma produces two leading zeros followed by \(0^{4n+8}\), hence the target \(0^{4n+10}\). This is an uncompiled composition guide, not a checked theorem.

Applying the decrement four times gives

\[
E_n(13;[])\longrightarrow E_{n+4}(1;[])
\]

in \(32n+152\) individual mode successors and \(96n+444\) raw steps.

## The offset-six remainder-one bridge

A separate ordinary-branch calculation gives

\[
E_m(1;[])\longrightarrow D_0(8m+9;[5])
\]

in \(8m+43\) individual mode successors and \(16m+115\) raw steps.

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

For the general-tail phase, the 16 ordinary successors are: EL-zero, EL-positive, DL-positive, two DR-zero steps, DR-empty-left, EL-positive, DL-zero, two EL-zero steps, EL-positive, DL-positive, three DR-zero steps, and DR-positive/positive. The raw costs sum to 47. The suffix \(T\) is unchanged. These are 16 individual source-mode successors; the current Lean helper packages them into 12 ReachesPlus sweep/branch blocks. This distinction explains the 12-block count in Agent 24's token note. Raw TM-step counts are the canonical runtime measure; mode-successor counts are auxiliary.

The outer and raw totals for the full bridge are respectively
\[
8+(4m+7)+5+(4m+6)+1+16=8m+43,
\]
\[
21+2(4m+7)+15+2(4m+6)+6+47=16m+115.
\]

## Suffix-general tail lemma for the remainder-one bridge

The 16-mode-successor, 47-raw-step tail can be generalized without fixing the suffix:

\[
EL([0],[0,x]++T)\longrightarrow D_0(x-6;T),\qquad x\ge6.
\]

A source-local Lean proof can compose the following helpers with the same suffix \(T\):

1. root_countdown_el_zero_step [0] ((x,0)::T)
2. root_countdown_el_positive_step (x-1) [0,0] T
3. root_countdown_dl_positive_step (x-3) [0,0] T
4. root_countdown_dr_zero_sweep 1 [] ((x-3,0)::T)
5. root_countdown_dr_empty_left_step ([1,0,0,x-3]++T)
6. root_countdown_el_positive_step 0 [0] ([0,0,x-3]++T)
7. root_countdown_dl_zero_step [0] ([0,0,x-3]++T)
8. root_countdown_el_zero_sweep 1 [0,1] ((x-3,0)::T)
9. root_countdown_el_positive_step (x-4) (0^3++[1]) T
10. root_countdown_dl_positive_step (x-6) (0^3++[1]) T
11. root_countdown_dr_zero_sweep 2 [1] ((x-6,0)::T)
12. root_countdown_dr_positive_positive_step 0 0 [] (0^3++[(x-6,0)]++T)

The crucial endpoint correction is step 7: after step 6, the DL right list is \(0^3++[x-3]++T\), so the zero-step helper's remainder argument must be \(0^2++[x-3]++T\). The old fixed-suffix draft omitted one of these zeros. This suffix-general version makes the E_m(1) bridge to \(D_0(8m+9;[5])\) a direct composition by taking \(x=8m+15\), \(T=[5]\).

A concrete uncompiled Lean draft, with the list arguments expanded, is:

~~~lean
theorem root_countdown_general_tail_suffix
    (x : ℕ) (T : List (ℕ × ℕ)) (hx : 6 ≤ x) :
    ReachesPlus target
      (cfg_EL_n_n [(0,0)] ((0,0) :: (x,0) :: T))
      (cfg_CR_n_n [(0,0)]
        (List.replicate 5 (0,0) ++ [(x-6,0)] ++ T)) := by
  have h1 := root_countdown_el_zero_step [(0,0)] ((x,0) :: T)
  have h2 := root_countdown_el_positive_step (x-1)
    [(0,0),(0,0)] T
  have h3 := root_countdown_dl_positive_step (x-3)
    [(0,0),(0,0)] T
  have h4 := root_countdown_dr_zero_sweep 1 []
    ((x-3,0) :: T)
  have h5 := root_countdown_dr_empty_left_step
    ((1,0) :: (0,0) :: (0,0) :: (x-3,0) :: T)
  have h6 := root_countdown_el_positive_step 0 [(0,0)]
    ((0,0) :: (0,0) :: (x-3,0) :: T)
  have h7 := root_countdown_dl_zero_step [(0,0)]
    ((0,0) :: (0,0) :: (x-3,0) :: T)
  have h8 := root_countdown_el_zero_sweep 1
    [(0,0),(1,0)] ((x-3,0) :: T)
  have h9 := root_countdown_el_positive_step (x-4)
    (List.replicate 3 (0,0) ++ [(1,0)]) T
  have h10 := root_countdown_dl_positive_step (x-6)
    (List.replicate 3 (0,0) ++ [(1,0)]) T
  have h11 := root_countdown_dr_zero_sweep 2 [(1,0)]
    ((x-6,0) :: T)
  have h12 := root_countdown_dr_positive_positive_step 0 0 []
    (List.replicate 3 (0,0) ++ [(x-6,0)] ++ T)
  have hx1 : x-1+1 = x := by omega
  have hx2 : x-3+2 = x-1 := by omega
  have hx3 : x-4+1 = x-3 := by omega
  have hx4 : x-6+2 = x-4 := by omega
  simpa [List.replicate_succ, List.cons_append, List.append_assoc,
    bumpPairHead, hx1, hx2, hx3, hx4] using
    (ReachesPlus.trans h1
      (ReachesPlus.trans h2
        (ReachesPlus.trans h3
          (ReachesPlus.trans h4
            (ReachesPlus.trans h5
              (ReachesPlus.trans h6
                (ReachesPlus.trans h7
                  (ReachesPlus.trans h8
                    (ReachesPlus.trans h9
                      (ReachesPlus.trans h10
                        (ReachesPlus.trans h11 h12)))))))))))
~~~

This draft is intended to replace the current fixed-suffix h7 proof, not to coexist with it. In particular h7 has the two-zero remainder shown above.

The intended theorem statement is:

\[
\operatorname{ReachesPlus}\;target\;
(cfg\_EL\_n\_n\;[0]\;([0,x]++T))\;
(cfg\_CR\_n\_n\;[0]\;(0^5++[x-6]++T)).
\]

The arithmetic side conditions are \(x-1+1=x\), \(x-3+2=x-1\), \(x-4+1=x-3\), and \(x-6+2=x-4\), all by omega from \(6\le x\). The helper composition has 12 ReachesPlus sweep/branch blocks, 16 individual source-mode successors, and raw cost 47. This is a proof guide only; it has not been compiled.

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
\(E_n(2)\to D_0(8n+21)\), with \(8n+46\) individual mode successors and \(40n+196\) raw steps; that closure is also not yet compiled. At the present endpoint \(n=1,192,248,236\), its proposed target would be \(D_0(9,537,985,909)\).

## Offset-six remainder-two reset composition

The new endpoint \(E_n(2)\) can be carried one step farther using the existing token helper root_d2_dl_one_z1. The source-local phase chain is:

1. Corrected suffix-preserving prefix with \(c=0,T=[2]\): 8 individual mode successors / 21 raw, reaching \(EL([0,1],0^{4n+7}++[2])\).
2. EL-zero sweep of \(4n+7\): \(4n+7\) individual mode successors / \(8n+14\) raw, reaching \(EL(0^{4n+8}++[1],[2])\).
3. EL-positive on head 2: 1 individual mode successors / 1 raw, reaching DL with right head 1.
4. Apply root_d2_dl_one_z1 with parameter \(4n+7\): 1 outer macro successor, raw cost \(6(4n+7)+41=24n+83\), reaching \(CR(0^{4n+12}++[1],[0])\).
5. CR-zero sweep of \(4n+12\): \(4n+12\) individual mode successors / \(8n+24\) raw, reaching \(CR([1],[8n+24])\).
6. CR-one/empty-tail: 1 individual mode successors / 6 raw, reaching \(EL([0],[0,8n+27])\).
7. General tail with \(x=8n+27\): 16 individual mode successors / 47 raw, reaching \(D_0(8n+21)\).

Consequently the existing candidate map is explained by the helper composition

\[
E_n(2)\longrightarrow D_0(8n+21),
\]

with \(8n+46\) individual mode successors and \(40n+196\) raw steps. In the source-local Lean draft, the intended helpers are, in order:

- root_countdown_prefix_with_tail_fixed n 0 [(2,0)]
- root_countdown_el_zero_sweep (4*n+6) [(0,0),(1,0)] [(2,0)]
- root_countdown_el_positive_step 1 (replicate (4*n+8) 0 ++ [1]) []
- root_d2_dl_one_z1 (4*n+7)
- root_countdown_cr_zero_sweep_singleton (4*n+11) 0 [1]
- root_countdown_cr_one_empty_step [8*n+24]
- root_countdown_general_tail (8*n+27)

This is a proof composition over the existing uncompiled token helper, not an independent proof of that helper. At the current endpoint \(n=1,192,248,236\), it would reach \(D_0(9,537,985,909)\). Since \(9,537,985,909\equiv1\pmod3\), the next suffix-preserving countdown reaches \(D_{3,179,328,636}(1)\).

The raw cost of the E-reset itself is \(40n+196=47,689,929,636\) at the current \(n\). The following countdown has \(N=3,179,328,636\) steps, raw cost \(12N^2+57N=121,297,567,089,497,178,204\). These values remain conditional until the token helper and its dependency closure compile without axioms.

## A 3-adic return map from the suffix-[0,0,2] residual

The residual-2 token branch admits a useful parameterized return map. Start at
\(D_n(1;[0,0,2])\), with \(n\equiv1\pmod9\).

The source-lemma prefix reaches
\(S(x_0,3)\), where \(S(x,r)=tok\_DR([2,x,1,1,1,1,0],[],0^r++[1])\) and
\(x_0=8n+12\), at raw cost \(8n+71\), including the preceding DL-right-one entry. Since \(n\equiv1\pmod9\), \(x_0\equiv2\pmod3\), so exactly

\[
N=\frac{x_0-2}{3}=\frac{8n+10}{3}
\]

subtract-three cycles reach \(S(2,r)\), with \(r=3+4N\). The batch costs \(12N^2+41N\) raw steps. The residual-2 token branch costs \(6r+46\) and reaches \(CR(0^5++[1]++0^{r+3}++[1],[0])\). The ordinary source tail costs \(2r+74\) and reaches \(D_0(2r+3;[13])\).

Now
\[
2r+3=9+8N=\frac{64n+107}{3}.
\]
For \(n\equiv1\pmod9\), this is divisible by 3. Let
\[
n'=\frac{64n+107}{9}.
\]
The suffix-preserving countdown with suffix [13] then reaches \(D_{n'}(0;[13])=E_{n'}(13)\). Thus

\[
\boxed{D_n(1;[0,0,2])\longrightarrow E_{(64n+107)/9}(13)}
\qquad(n\equiv1\pmod9).
\]

The exact raw cost is
\[
R(n)=8n+71+(12N^2+41N)+(6r+46)+(2r+74)+(12n'^2+57n'),
\]
where \(N=(8n+10)/3\), \(r=3+4N\), and \(n'=(64n+107)/9\).

For the index reached from the new E-remainder-two endpoint,
\[
n=22\,608\,559\,198,\quad
N=60\,289\,491\,198,\quad
r=241\,157\,964\,795,\quad
n'=160\,771\,976\,531.
\]
The token-return macro costs 353,789,414,252,923,615,223,500 raw steps and returns to \(E_{160771976531}(13)\).

The preceding known source macros from \(E_{1,192,248,236}(2)\) reach \(D_{22,608,559,198}(1;[0,0,2])\) through these checkpoints:

| Checkpoint | State |
| --- | --- |
| E-remainder-two reset | \(D_0(9,537,985,909)\) |
| countdown | \(D_{3,179,328,636}(1)\) |
| remainder-one reset | \(D_0(25,434,629,095;[5])\) |
| countdown | \(D_{8,478,209,698}(1;[5])\) |
| suffix-five remainder-one reset | \(D_0(67,825,677,595;[0,0,2])\) |
| countdown | \(D_{22,608,559,198}(1;[0,0,2])\) |

The total raw cost from \(E_{1,192,248,236}(2)\) through this return to \(E_{160,771,976,531}(13)\) is 360,907,035,686,332,048,624,882. This is a conditional source-lemma computation; the token proof and the preceding reset/countdown lemmas still need kernel verification.

The index map \(n\mapsto(64n+107)/9\) is a one-base-9-digit shift (two base-3 digits) with an affine unit multiplier on the domain \(n\equiv1\pmod9\). In particular, writing \(n=1+9a\) gives \(n'=19+64a\). The next residue class modulo 9 therefore depends on the next base-9 digit of \(n\); it is not constant across iterations.
## Reproducibility and limitations

verify_suffix13_macro.py transcribes the ordinary CR/EL/DL/DR stack clauses and checks the decrement and remainder-one formulas at small parameters. The finite checks cover \(n=0,\ldots,4\) and \(x\in\{3,4,7,10,13,16\}\). They are bounded source-transcribed computation, not a proof of the quantified statements.

No token closure is used in the new decrement or remainder-one bridge. The existing suffix-preserving countdown and the prefix composition still require a corrected, compiled proof in the original source module. The local RC2 archive is complete and Lean 4.36.0-rc2 is available; the full upstream source module was not compiled here because the container has no network access to obtain its Mathlib/cryptids dependency checkout. The current root-to-\(D_{447093083}(0;[13])\) prefix is conditional. No blank-root halt/nonhalt decision, exhaustive maximality proof, or exact BB(6) value follows.
