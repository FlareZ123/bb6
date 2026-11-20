# A=2 terminal boundary: z=1 diagnostic

**Status:** reproducible finite computation, not a uniform proof. This is an intermediate result and belongs in \`im-results/\`, not \`results/\`.

## Exact input

Specialize the A=2 odd-\(q\) residual from \`im-results/agent24-champion-time/P2Q4TailToS0Identity.md\) to \(z=1\). Then

\[
m=16,\quad n=2,\quad K=2^z+z+3=6,\quad H=m+2+3n=24.
\]

For an even test parameter \(L\), the residual word is

\[
\ell_{34}
=d_1^6\Vert 01\Vert d_0^2\Vert d_1^2
 \Vert d_0^{L+1}\Vert lh,
\]

where \(d_0=001\), \(d_1=111\), and \(lh=110111\). The simulated initial configuration is exactly

\[
\operatorname{s0Config}(\ell_{34},1,1,0,24).
\]

Its left-facing stream is \(d_0\Vert\ell_{34}\), because
\(\operatorname{binDec}(1,1)=d_0\). Its right-facing stream is
\(011100111\), the \(b=0\) instance of the S0 right encoder.

The replay uses the original TM63/TM2 transition table, with absent tape cells blank and a sparse map for the infinite tape. The complete executable is [a2_terminal_basecase_z1.js](a2_terminal_basecase_z1.js).

## Observed terminal sections

The simulator checks the exact \`SectionBits\` shape used by
\`im-results/agent42-champion-terminal/TerminalEncoderBridge.lean\):
the head-facing left word is

\[
d_1^a\Vert 01\Vert d_0\Vert d_1^{L_{\rm term}}\Vert lh,
\]

and the first seven cells to the right are \(0111001\). It then continues
the original machine until the halting transition is encountered.

| Input \(L\) | \(L_{\rm term}\) | \(a_{\rm term}\) | Moves to SectionBits | Terminal head | \(11110000\) events | Halt moves |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 6 | 159 | 63,042 | 480 | 28 | 65,081 |
| 4 | 8 | 671 | 1,040,298 | 2,016 | 124 | 1,048,505 |
| 6 | 10 | 2,719 | 16,745,874 | 8,160 | 508 | 16,778,681 |

The three terminal outputs satisfy the observed relations

\[
L_{\rm term}=L+4,\qquad
a_{\rm term}=\frac{2^{L+7}-35}{3},
\qquad
h_{\rm term}=3a_{\rm term}+3=2^{L+7}-32.
\]

Writing \(N=2^{L+4}-7\), the measured prefix lengths also fit

\[
T_{\rm prefix}=16N^2+194N-12L+24.
\]

The number of state-4/head-1 checkpoints whose local window at offsets
\([-3,4]\) is \(11110000\) is \(2^{L+3}-4\) in all three runs.
These are empirical formulae from three finite instances, not proved
identities for all even \(L\).

## Why this matters for the A=2 boundary

The A=2 residual is not another instance of the guard-bearing
\(A\mapsto A-2\) recurrence. After the first six-cell shift, the remaining
tail begins \(1\Vert d_1\Vert d_0^{L+1}\), not \(100\). In the replay the
next relevant state-4 checkpoint has head \(1\), local window
\(11110000\), and a right-side prefix beginning \(000111\ldots\).
Thus the usual P2 postlude guard does not recur at this boundary. A
separate terminal macro for this \(11110000\) branch is needed.

The z=1 computation gives a concrete finite target for that macro:
convert the A=2 residual to the terminal SectionBits interface with
\(L_{\rm term}=L+4\), while the unary terminal parameter grows according
to the observed formula above.

## Limitations and next proof obligation

This is **not** the authentic blank-root trajectory. The root's positive
parameter has \(z\ge 3\); here \(n=2\), and the recurrence
\(n\mapsto 2^{n-1}\) is fixed at \(2\). Consequently these runs do not test
the nested positive-z counter growth that dominates the actual root.

The next mathematical task is to prove a uniform source-level A=2 terminal
macro for arbitrary admissible positive-z \(m,n\), establish its exact
step count and tape frame, and compose it with the q4Tail-to-S0 adapter.
Do not promote this diagnostic to \`results/\`, and do not describe it as
a proof that the authentic TM63 root halts.
