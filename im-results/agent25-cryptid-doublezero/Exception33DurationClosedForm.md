# Exception 33 q=5: closed-form primitive duration

## Scope

This note simplifies the exact runtime already certified by
`BB6.Agent25Exception33Q5.exception33_q5_rejoin`. It is an arithmetic
corollary of the source-certified EAllDouble → E-three → A-code composition,
not a new blank-root reachability result.

For every natural parameter \(u\), the original-machine source path starts
at \(L(27u+7,5,1)\) and reaches the pure-unary section
\(L(512u+129,0,0)\), up to the repository's physical blank-extension
equivalence, in exactly

\[
\boxed{T_{33}(u)=57036u^2+28201u+3628}
\]

primitive transitions.

## Derivation

The three already-proved source segments have parameters:

1. EAllDouble: \(k=9u+1\), \(q=4\), hence
   \[
   T_E(u)=12(9u+1)^2+49(9u+1)+76
         =972u^2+657u+137.
   \]
2. E-three: \(k=24u+3\), hence
   \[
   T_3(u)=12(24u+3)^2+49(24u+3)+58
         =6912u^2+2904u+313.
   \]
3. A-code: \(k=64u+10\), with codeword
   \[
   w=(0,0,1,1,0,1,1).
   \]

For this word, the exact token statistics in
`im-results/agent32-cryptid-padding/TokenCostNormal.lean` are:

| Statistic | Value |
|---|---:|
| Number of 10-pairs \(\mathrm{pairsN}(w)\) | 3 |
| Number of 111-triples \(\mathrm{triplesN}(w)\) | 4 |
| Mixed inversions \(\mathrm{mixedInv}(w)\) | 10 |
| \(\mathrm{triangular}(4)\) | 6 |
| Counter increment \(\mathrm{wordInc}(w)\) | 19 |

The kernel-certified formula `BB6.Parikh.wordCost_closed` therefore gives,
at \(m=4(64u+10)+3=256u+43\),

\[
\begin{aligned}
\mathrm{wordCost}(256u+43,w)
 &=2(3)+(6(256u+43)+41)(4)+6(10)+24(6)\\
 &=6144u+1406.
\end{aligned}
\]

The final A-code closure contributes
\[
2((256u+43)+19)+6=512u+130.
\]
Consequently,
\[
\begin{aligned}
T_A(u)
 &=12(64u+10)^2+41(64u+10)+32\\
 &\quad+6144u+1406+512u+130\\
 &=49152u^2+24640u+3178.
\end{aligned}
\]

Adding the three segment durations yields
\[
T_E(u)+T_3(u)+T_A(u)
 =57036u^2+28201u+3628.
\]

## Reproducible source dependencies

- `Exception33Q5Rejoin.lean`: exact original-machine composition and
  `exception33_q5_rejoin`; source CI [44740066064](https://github.com/FlareZ123/bb6/actions/runs/44740066064).
- `TokenCostNormal.lean`: general closed word-cost identity and token
  statistics; source CI [41422121853](https://github.com/FlareZ123/bb6/actions/runs/41422121853).

The polynomial is a simplification of those already-verified definitions;
this note does not claim a new Lean kernel check of the displayed
specialization. It does not resolve the upstream root prefix: the
`BlankThirtyThirdRejoin` composition remains conditional on the earlier
episode-19–30 and Seed31/32 source lifts. It also gives no global
nonhalting invariant or exact BB(6) value.
