# Corrected token-memory accounting for the suffix-[0,0,2] root branch

**Status:** intermediate source-level derivation; not Lean-compiled. This note corrects the fixed-memory notation in the residual-two continuation and extends the token path to a concrete ordinary-stack configuration.

## 1. The essential state parameter

The token suffix is not invariant through a zero-remainder branch. Define

\[
U_k(x,r)=\operatorname{tokDR}
\bigl([2,x]\mathbin{+\!\!+}1^k\mathbin{+\!\!+}[0],\ [],\ 0^r\mathbin{+\!\!+}[1]\bigr).
\]

Here \(1^k\) means a list of exactly \(k\) ones. The source lemmas used below are in the pinned Cryptids file

- commit: \`3647718b5df22e1a61462dec0376bd204526285a\`
- file: \`BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean\`

The relevant exact source clauses are \`tok_DR_zero\`, \`tok_DR_1_nil_28\`, \`tok_EL_1\`, \`tok_EL_0_cons\`, \`tok_CR_zero\`, \`tok_CR_1_nil_33\`, \`tok_EL_add3\`, \`tok_EL_2\`, and \`tok_EL_exit_zero\`.

## 2. Three reusable transitions

### Subtract-three

For \(x\geq3\),

\[
U_k(x,r)\longrightarrow^+ U_k(x-3,r+4).
\]

The source sequence is:

1. \(r\) applications of \`tok_DR_zero\`;
2. one \`tok_DR_1_nil_28\`;
3. \(r+1\) applications of \`tok_EL_1\);
4. one \`tok_EL_add3\).

It uses \(2r+3\) individual token successors and costs

\[
4r+28+2(r+1)+5=6r+35
\]

raw TM steps. Starting at \(r=3\), \(q\) such cycles cost

\[
4q^2+5q\quad\text{token successors},\qquad
12q^2+41q\quad\text{raw steps}.
\]

### Zero remainder: the memory decreases

For \(k\geq1\),

\[
\boxed{U_k(0,r)\longrightarrow^+U_{k-1}(2r+7,3).}
\]

After the \(r\) DR-zero steps, DR-one terminal step, and \(r+1\) EL-one steps, the state is

\[
\operatorname{tokEL}([0,1^k,0],[],0^{r+4}1).
\]

The next source rule is decisive:

\[
\operatorname{tokEL}([0,1^k,0],[],0^{r+4}1)
\longrightarrow
\operatorname{tokCR}([2,1^{k-1},0],[],0^{r+4}1).
\]

This is \`tok_EL_0_cons\`. It consumes one of the \(k\) trailing ones. It does **not** preserve \(k\).

Then \(r+4\) CR-zero steps, \`tok_CR_1_nil_33\`, and \`tok_EL_add3\` give \(U_{k-1}(2r+7,3)\). The total is

\[
3r+9\quad\text{individual token successors},\qquad
8r+77\quad\text{raw steps}.
\]

This is the correction to a fixed-\(k\) reading of the earlier \(S(0,r)\) notation.

### Residual two

For \(k\geq0\),

\[
U_k(2,r)\longrightarrow^+
\operatorname{CR}(0^{k+1}1\,0^{r+3}1,[0]).
\]

After the DR-zero sweep, DR-one terminal step, and EL-one sweep, apply \`tok_EL_2\`, then \(k\) applications of \`tok_EL_1\), then \`tok_EL_exit_zero\`. The \`tok_EL_2\` clause consumes the leading zero and inserts the pair \(0,1\), leaving \(r+3\) zeros after that inserted one.

The cost is

\[
2r+k+4\quad\text{individual token successors},\qquad
6r+38+2k\quad\text{raw steps}.
\]

When two zero-remainder branches have occurred, \(k=2\), so the output has three leading zeros and \(r+3\) zeros in its second run.

## 3. Application to the outstanding root input

The conditional root dossier reaches

\[
D_{8\,841\,438}(1;[0,0,2]).
\]

Its ordinary source prefix reaches the DL-right-one state with left list \(0^3 1 0^{4n+6}1\) and right list \([1]\). The prefix costs \(4n+19\) individual source-mode successors and \(8n+45\) raw steps. The DL-right-one token entry costs one further successor and four raw steps.

The resulting token input is

\[
\operatorname{tokDR}([2,0],[],0^3 1\,0^{4n+6}1),
\qquad n=8\,841\,438.
\]

The initial token prefix reaches \(U_4(8n+12,3)\), costing \(4n+13\) token microsteps and \(8n+67\) raw steps.

| Stage | State | Batch count | Resulting \(r\) |
|---|---|---:|---:|
| Initial | \(U_4(70\,731\,516,3)\) | — | 3 |
| First subtract-three batch | \(U_4(0,94\,308\,691)\) | 23,577,172 | 94,308,691 |
| First zero branch | \(U_3(188\,617\,389,3)\) | — | 3 |
| Second subtract-three batch | \(U_3(0,251\,489\,855)\) | 62,872,463 | 251,489,855 |
| Second zero branch | \(U_2(502\,979\,717,3)\) | — | 3 |
| Third subtract-three batch | \(U_2(2,670\,639\,623)\) | 167,659,905 | 670,639,623 |

Thus the token memory evolves \(4\to3\to2\). The corrected residual-two exit is

\[
\operatorname{CR}(0^3 1\,0^{670\,639\,626}1,[0]).
\]

## 4. Ordinary-stack continuation

Put \(R=670\,639\,626\). The pinned ordinary CR clauses give

\[
\begin{aligned}
\operatorname{CR}(0^3 1\,0^R1,[0])
&\longrightarrow^+ \operatorname{CR}(1\,0^R1,[6])\\
&\longrightarrow^+ \operatorname{CR}(0^R1,[0,9])\\
&\longrightarrow^+ \operatorname{CR}([1],[2R,9])\\
&\longrightarrow^+ \operatorname{EL}([0],[0,2R+3,9])\\
&\longrightarrow^+ D_0(2R-3;[9]).
\end{aligned}
\]

The final suffix-preserving general tail has 16 individual source-mode successors and 47 raw steps. The preceding ordinary steps cost \(2R+17\) raw steps. Therefore the full ordinary continuation costs \(R+21\) individual successors and \(2R+64\) raw steps.

The corrected endpoint is

\[
\boxed{D_0(1\,341\,279\,249;[9])}.
\]

This is a concrete stack configuration with CR left head zero; it is not a halting configuration.

## 5. Correction to the earlier residual-two note

The earlier TokenResidual2Continuation.md keeps a fixed four-one suffix through both zero-remainder branches and consequently applies the residual-two exit with \(k=4\). The source clause tok_EL_0_cons consumes one of those ones at each zero branch, so this branch reaches \(k=2\).

The earlier note's c-coordinate \(1\,341\,279\,249\) is correct, but its suffix \([13]\) is not correct for this branch. The corrected endpoint is \(D_0(1\,341\,279\,249;[9])\). A separate branch that reaches residual two without any zero-remainder stage can still use \(k=4\) and suffix \([13]\).

## 6. Conditional exact step arithmetic

The suffix-preserving countdown from \(D_0(26\,524\,315;[0,0,2])\) to \(D_n(1;[0,0,2])\), \(n=8\,841\,438\), costs

\[
4n(n+5)=312\,684\,280\,460\,136
\]

individual source-mode successors and

\[
12n^2+57n=938\,052\,814\,856\,094
\]

raw steps.

The complete segment from \(D_0(26\,524\,315;[0,0,2])\) to the corrected \(D_0(1\,341\,279\,249;[9])\) endpoint has:

- 312,684,986,465,555 stack-mode successors (counting the DL-to-token closure as one);
- 130,474,697,235,840,285 token-machine microsteps;
- 130,787,382,222,305,840 combined individual source-mode successors;
- 392,362,152,160,071,712 raw TM steps.

The preceding conditional blank-root arithmetic in RootRemainderOneTail.md reports 51,166,575,478,679 outer stack-mode successors and 153,499,683,790,849 raw steps. Adding only comparable stack-mode counts gives 363,851,561,944,234 stack-mode successors from the blank-root checkpoint to the corrected endpoint. The raw-step total is 392,515,651,843,862,561.

Do not add the combined segment count to the prior outer stack-mode count: the former includes token-machine microsteps, while the latter does not. These are arithmetic totals for the stated source-level composition, not a certified runtime lower bound. The upstream root connection, suffix-preserving lemmas, and token composition remain uncompiled.

The phase formulas are reproducible with integer arithmetic:

~~~js
const n = 8841438n;
const x0 = 8n*n + 12n, q0 = x0/3n, r0 = 3n + 4n*q0;
const x1 = 2n*r0 + 7n, q1 = x1/3n, r1 = 3n + 4n*q1;
const x2 = 2n*r1 + 7n, q2 = (x2-2n)/3n, r2 = 3n + 4n*q2;
const R = r2 + 3n;
~~~

## 7. Next proof obligations

1. Formalize the parameterized \(U_k\) subtract-three, zero-remainder, and residual-two compositions in the same source module as the private token declarations, or expose the required declarations safely.
2. Add the corrected suffix-preserving prefix and general-tail lemmas to the source-local Lean proof.
3. Establish the next suffix-[9] reset from \(D_0(1\,341\,279\,251;[9])\); do not reuse the suffix-[13] return map without a new source derivation.
4. Reconnect the corrected endpoint to the blank-root proof and independently audit every raw-step count.

Local Lean was not run in this invocation: the available shell/runtime calls returned a concrete ClientError. No CI run was used as a substitute for the required local preflight. Nothing here establishes halting, nonhalting, a universal six-state upper bound, or the exact value of BB(6).


## 8. Generic singleton-suffix remainder-two reset

The independent source composition for a singleton suffix remains

\[
D_n(2;[t])\longrightarrow^+D_0(8n+t+20).
\]

The fixed prefix and EL-zero sweep leave \(DL(0^{4n+7}1,[1,t])\). The DL token closure uses \(R_3=[t]\), so root_d2_tok_dr_z1 exits to \(CR(0^{4n+11}1,[t+1])\). The CR-zero sweep, CR-one-empty step, and general tail give the stated output. The costs are independent of \(t\):

- \(8n+44\) stack-mode successors;
- \(8n+17\) token-machine microsteps inside the DL closure;
- \(40n+186\) raw TM steps.

This map does **not** apply immediately to the corrected root endpoint: \(1\,341\,279\,249=3\cdot447\,093\,083\), so the next state is \(D_{447\,093\,083}(0;[9])\), not a remainder-two state. The next unresolved transition for this branch is the suffix-[9] zero-remainder case \(D_n(0;[9])\).

## 9. Zero remainder with suffix [0,0,2]

The independently derived suffix reset

\[
D_n(0;[0,0,2])\longrightarrow^+D_0(8n+23)
\]

remains valid. After the fixed eight-step prefix and the \(4n+6\)-zero EL sweep, the two zeros in the suffix are consumed by two further EL-zero steps. EL-positive on 2 reaches the DL-right-one state with left list \(0^{4n+9}1\). Apply the existing token lemma with \(m=4n+9\) leading zeros and empty \(R_3\); it exits to \(CR(0^{4n+13}1,[0])\). The CR-zero sweep, CR-one-empty step, and general tail give \(D_0(8n+23)\).

Its costs are \(8n+48\) stack-mode successors, \(8n+21\) token-machine microsteps inside the DL closure, and \(40n+206\) raw TM steps.

The previously reported chain from \(D_{22\,608\,559\,088}(1)\) through \(D_0(9\,146\,139\,064\,807;[5])\) is withdrawn. It depended on the incorrect \(D_0(1\,341\,279\,251;[9])\) endpoint and is not connected to the corrected root branch. The generic suffix-[0,0,2] zero-reset map above is independent of that withdrawn chain.

## 10. Bounded 3-adic normalization for the whole \(D_n(1;[0,0,2])\) family

The preceding token lemmas give a finite normalizer for every \(n\), not just the \(n=8\,841\,438\) instance. The source prefix reaches

\[
U_4(x_0,3),\qquad x_0=8n+12.
\]

At a stage \(U_k(x,3)\), write \(x=3q+s\), \(s\in\{0,1,2\}\). The subtract-three batch reaches \(U_k(s,r)\), where \(r=3+4q\). Its costs are \(4q^2+5q\) token microsteps and \(12q^2+41q\) raw steps.

- If \(s=0\) and \(k>0\), the zero branch reaches \(U_{k-1}(2r+7,3)\). Thus the next integer is
  \[
  f(x)=2(3+4x/3)+7=\frac{8x+39}{3},
  \]
  and \(k\) decreases by one.
- If \(s=1\), the residual-one token exit gives \(CR(0^{r+k+5}1,[0])\), then the ordinary tail gives
  \[
  D_0(2r+2k+7).
  \]
  The token exit costs \(2r+k+4\) microsteps and \(6r+2k+33\) raw steps.
- If \(s=2\), the residual-two exit gives \(CR(0^{k+1}1\,0^{r+4}1,[0])\), then the ordinary tail gives
  \[
  D_0(2r+3;[2k+5]).
  \]
  The token exit costs \(2r+k+4\) microsteps and \(6r+2k+38\) raw steps.
- If \(s=0\) when \(k=0\), the final token exit gives \(CR(0^{r+4}1,[0])\), then the ordinary tail gives \(D_0(2r+5)\). The token exit costs \(2r+3\) microsteps and \(6r+31\) raw steps.

Since \(k\) starts at four and decreases at every zero branch, there are at most four zero-remainder reductions before a terminal residual-one, residual-two, or \(k=0\) residual-zero exit. This is a bounded deterministic normalization procedure for every \(D_n(1;[0,0,2])\).

Equivalently, the only repeated arithmetic operation is \(f(x)=(8x+39)/3\), applied when \(x\) is divisible by three. The first residue is determined by \(x_0=8n+12\); subsequent zero residues are determined by iterating \(f\). In particular, \(n\equiv1\pmod3\) gives an immediate residual-two exit, \(n\equiv2\pmod3\) gives an immediate residual-one exit, and \(n\equiv0\pmod3\) starts the bounded \(f\)-iteration.

As a second concrete instance, take \(n=8\,129\,901\,390\,942\). The residue sequence is \(0,1\):
\[
\begin{aligned}
x_0&=65\,039\,211\,127\,548=3(21\,679\,737\,042\,516),\\
r_0&=86\,718\,948\,170\,067,\\
x_1&=2r_0+7=173\,437\,896\,340\,141\\
&=3(57\,812\,632\,113\,380)+1.
\end{aligned}
\]
Here the first zero branch reduces \(k:4\to3\); the residual-one exit at \(k=3\) gives
\[
D_0(462\,501\,056\,907\,059).
\]

The arithmetic normalizer and concrete instances are kernel-checked in verify_token_normalizer_arithmetic.lean by GitHub Actions run 45015701109 using Lean 4.36.0-rc2. The source-rule correspondence (the U_k transitions as compositions of the pinned token clauses) and the full source-module composition still await a Lean proof. The normalizer resolves the token behavior of the entire \(D_n(1;[0,0,2])\) family into explicit stack states, but does not prove that those resulting stack states halt or do not halt.
