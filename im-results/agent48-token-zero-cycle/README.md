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
\operatorname{CR}(0^{k+1}1\,0^{r+4}1,[0]).
\]

After the DR-zero sweep, DR-one terminal step, and EL-one sweep, apply \`tok_EL_2\`, then \(k\) applications of \`tok_EL_1\), then \`tok_EL_exit_zero\`.

The cost is

\[
2r+k+4\quad\text{individual token successors},\qquad
6r+38+2k\quad\text{raw steps}.
\]

In particular, when two zero-remainder branches have already occurred, \(k=2\), not \(k=4\). The residual-two endpoint then has three leading zeros and \(r+4\) zeros in the second run.

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

The initial token prefix (three DR-zero steps, DR-succ, \(4n+7\) CR-zero steps, CR-one terminal step, and EL-add-three) reaches \(U_4(8n+12,3)\), costing \(4n+13\) token successors and \(8n+67\) raw steps.

The exact arithmetic is:

| Stage | State | Batch count | Resulting \(r\) |
|---|---|---:|---:|
| Initial | \(U_4(70\,731\,516,3)\) | — | 3 |
| First subtract-three batch | \(U_4(0,94\,308\,691)\) | 23,577,172 | 94,308,691 |
| First zero branch | \(U_3(188\,617\,389,3)\) | — | 3 |
| Second subtract-three batch | \(U_3(0,251\,489\,855)\) | 62,872,463 | 251,489,855 |
| Second zero branch | \(U_2(502\,979\,717,3)\) | — | 3 |
| Third subtract-three batch | \(U_2(2,670\,639\,623)\) | 167,659,905 | 670,639,623 |

Thus the token memory evolves \(4\to3\to2\). The residual-two exit is

\[
\operatorname{CR}(0^3 1\,0^{670\,639\,627}1,[0]).
\]

## 4. Ordinary-stack continuation

Put \(R=670\,639\,627\). The pinned ordinary CR clauses give

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
\boxed{D_0(1\,341\,279\,251;[9])}.
\]

This is a concrete stack configuration with CR left head zero; it is not a halting configuration.

## 5. Correction to the earlier residual-two note

The earlier \`TokenResidual2Continuation.md\` keeps a fixed four-one suffix through both zero-remainder branches and consequently applies the residual-two exit with \(k=4\). That is inconsistent with \`tok_EL_0_cons\`: each zero branch consumes one of those ones.

For this \(n=8\,841\,438\) input, the correct sequence is \(U_4\to U_3\to U_2\), so the endpoint is \(D_0(1\,341\,279\,251;[9])\), not \(D_0(1\,341\,279\,249;[13])\). The later suffix-[13] continuation is not connected to this particular root branch until a valid path to its starting state is established. A separate branch that reaches residual two without any zero-remainder stage may still use \(k=4\).

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

The complete segment from \(D_0(26\,524\,315;[0,0,2])\) to the corrected \(D_0(1\,341\,279\,251;[9])\) endpoint has three distinct counts:

- 312,684,986,465,556 stack-mode successors (counting the DL-to-token closure as one);
- 130,474,697,235,840,285 token-machine microsteps;
- 130,787,382,222,305,841 combined individual source-mode successors;
- 392,362,152,160,071,714 raw TM steps.

The preceding conditional blank-root arithmetic in RootRemainderOneTail.md reports 51,166,575,478,679 **outer stack-mode successors** and 153,499,683,790,849 raw steps. Adding only comparable stack-mode counts gives 363,851,561,944,235 stack-mode successors from the blank-root checkpoint to the corrected endpoint. The raw-step total is 392,515,651,843,862,563.

Do not add the combined segment count to the prior outer stack-mode count: the former includes token-machine microsteps, while the latter does not. These are arithmetic totals for the stated source-level composition, **not a certified runtime lower bound**. The upstream root connection, suffix-preserving lemmas, and token composition remain uncompiled.

The phase formulas are reproducible with integer arithmetic:

~~~js
const n = 8841438n;
const x0 = 8n*n + 12n, q0 = x0/3n, r0 = 3n + 4n*q0;
const x1 = 2n*r0 + 7n, q1 = x1/3n, r1 = 3n + 4n*q1;
const x2 = 2n*r1 + 7n, q2 = (x2-2n)/3n, r2 = 3n + 4n*q2;
const R = r2 + 4n;
const cycleOuter = q => 4n*q*q + 5n*q;
const cycleRaw = q => 12n*q*q + 41n*q;
~~~

## 7. Next proof obligations

1. Formalize the parameterized \(U_k\) subtract-three, zero-remainder, and residual-two compositions in the same source module as the private token declarations, or expose the required declarations safely.
2. Add the corrected suffix-preserving prefix and general-tail lemmas to the source-local Lean proof.
3. Establish the next suffix-[9] reset from \(D_0(1\,341\,279\,251;[9])\); do not reuse the suffix-[13] return map without a new source derivation.
4. Reconnect the corrected endpoint to the blank-root proof and independently audit every raw-step count.

Local Lean was not run in this invocation: the available shell/runtime calls returned a concrete ClientError. No CI run was used as a substitute for the required local preflight. Nothing here establishes halting, nonhalting, a universal six-state upper bound, or the exact value of BB(6).


## 8. The corrected suffix-[9] branch reconnects to the suffix-[5] family

The same existing token lemma handles a singleton suffix. For \(t\in\mathbb N\), the source composition gives

\[
D_n(2;[t])\longrightarrow^+D_0(8n+t+20).
\]

Indeed, the fixed prefix and EL-zero sweep leave \(DL(0^{4n+7}1,[1,t])\). The DL token closure uses \(R_3=[t]\), so \`root_d2_tok_dr_z1\` exits to

\[
CR(0^{4n+11}1,[t+1]).
\]

The CR-zero sweep, CR-one-empty step, and 16-step general tail give \(D_0(8n+t+20)\). The reset costs are independent of \(t\):

- \(8n+44\) stack-mode successors;
- \(8n+17\) token-machine microsteps inside the DL closure;
- \(40n+186\) raw TM steps.

For \(t=9\), the corrected endpoint therefore continues as follows:

\[
\begin{aligned}
D_0(1\,341\,279\,251;[9])
&\to D_{447\,093\,083}(2;[9])\\
&\to D_0(3\,576\,744\,693)\\
&\to D_{1\,192\,248\,231}(0)\\
&\to D_0(9\,537\,985\,861)\\
&\to D_{3\,179\,328\,620}(1)\\
&\to D_0(25\,434\,628\,967;[5]).
\end{aligned}
\]

The maps used after the suffix-[9] reset are the already-derived zero reset \(D_n(0)\to D_0(8n+13)\) and remainder-one reset \(D_n(1)\to D_0(8n+7;[5])\).

One further already-known suffix-[5] reset gives

\[
D_0(25\,434\,628\,967;[5])
\to D_{8\,478\,209\,655}(2;[5])
\to D_0(67\,825\,677\,265)
\to D_{22\,608\,559\,088}(1).
\]

This reaches a remainder-one state with index \(22\,608\,559\,088\), which differs by 110 from the \(22\,608\,559\,198\) index used as the starting point in the current suffix-[13] return-map note. The two chains must not be conflated: the corrected suffix-[9] route gives the former index.
