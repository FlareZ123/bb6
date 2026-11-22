# Conditional E(13) continuation to the next residual-one token branch

**Status:** exact integer propagation through the existing source-stack macros, using the 3-adic token lemma in `agent24-cryptid-token-3adic-termination.md`. The source macro chain is not yet compiled as one Lean theorem. This note is an intermediate continuation, not a halting/nonhalting proof.

## Macro rules used

Write:
- (C(c)=D_0(c)), with no suffix;
- (B(c)=D_0(c;[5]));
- (Q(c)=D_0(c;[0,0,2])).

The existing source-stack notes give the following parameter maps, whenever (c=3k+r):

| Source family | Remainder | Successor |
|---|---:|---|
| (C(c)) | (r=0) | (C(8k+13)) |
| (C(c)) | (r=2) | (C(8k+19)) |
| (C(c)) | (r=1) | (B(8k+7)) |
| (B(c)) | (r=0) | (C(8k+29)) |
| (B(c)) | (r=2) | (C(8k+25)) |
| (B(c)) | (r=1) | (Q(8k+11)) |

Also,
[
E_n(13)\to E_{n+4}(1)\to B(8n+41).
]
The (Q(c)) remainder-one case (c=3k+1) enters (D_k(1;[0,0,2])). Its token input is (S(x_0,3)) with (x_0=8k+12). The 3-adic lemma gives the exact number of zero branches and the terminal residual.

These maps are conditional on the source-derived lemmas in `RootSuffix13Continuation.md`, `RootRemainderOneTail.md`, and `RootCountdownSweep.md`.

## First continuation: (E_{160771976531}(13)) reaches (E_{50976043225396505578331}(13))

The exact (C/B) parameter chain is:

| Step | Family parameter (c) | (c\bmod3) | Successor parameter |
|---:|---:|---:|---:|
| 0 | (B(1286175812289)) | 0 | (C(3429802166133)) |
| 1 | (C(3429802166133)) | 0 | (C(9146139109701)) |
| 2 | (C(9146139109701)) | 0 | (C(24389704292549)) |
| 3 | (C(24389704292549)) | 2 | (C(65039211446811)) |
| 4 | (C(65039211446811)) | 0 | (C(173437897191509)) |
| 5 | (C(173437897191509)) | 2 | (C(462501059177371)) |
| 6 | (C(462501059177371)) | 1 | (B(1233336157806327)) |
| 7 | (B(1233336157806327)) | 0 | (C(3288896420816901)) |
| 8 | (C(3288896420816901)) | 0 | (C(8770390455511749)) |
| 9 | (C(8770390455511749)) | 0 | (C(23387707881364677)) |
| 10 | (C(23387707881364677)) | 0 | (C(62367221016972485)) |
| 11 | (C(62367221016972485)) | 2 | (C(166312589378593307)) |
| 12 | (C(166312589378593307)) | 2 | (C(443500238342915499)) |
| 13 | (C(443500238342915499)) | 0 | (C(1182667302247774677)) |
| 14 | (C(1182667302247774677)) | 0 | (C(3153779472660732485)) |
| 15 | (C(3153779472660732485)) | 2 | (C(8410078593761953307)) |
| 16 | (C(8410078593761953307)) | 2 | (C(22426876250031875499)) |
| 17 | (C(22426876250031875499)) | 0 | (C(59805003333418334677)) |
| 18 | (C(59805003333418334677)) | 1 | (B(159480008889115559143)) |
| 19 | (B(159480008889115559143)) | 1 | (Q(425280023704308157723)) |

The final (Q)-parameter is (3k+1) with
[
k=141760007901436052574.
]
Its token input has
[
x_0=8k+12=1134080063211488420604,
]
[
5x_0+39=5670400316057442103059,
qquad v_3(5x_0+39)=4.
]
The 3-adic token theorem gives four zero branches and terminal residual 2:
[
N=19116016209523689591873,qquad
r=3+4N=76464064838094758367495.
]
The residual-two outer tail gives
[
c_{\rm tok}=2r+3=152928129676189516734993,
]
which is divisible by 3. Countdown to (E_{c_{\rm tok}/3}(13)) therefore returns
[
E_{50976043225396505578331}(13).
]

This is a return to a new (E(13)) parameter, not a cycle.

## Second continuation: the new (E(13)) reaches a residual-one token endpoint

Starting from (E_{50976043225396505578331}(13)), the next source macros give:
[
egin{aligned}
E_{50976043225396505578331}(13)
&\to B(407808345803172044626689)\\
&\to C(1087488922141792119004533)\\
&\to C(2899970459044778984012101)\\
&\to B(7733254557452743957365607)\\
&\to Q(20622012153207317219641627).
end{aligned}
]
The final (Q)-parameter is (3k+1), where
[
k=6874004051069105739880542.
]
Its token input is
[
x_0=8k+12=54992032408552845919044348,
]
[
5x_0+39=274960162042764229595221779,
qquad v_3(5x_0+39)=1.
]
There is exactly one zero branch. The terminal parameter is
[
x_1=146645419756140922450784941\equiv1\pmod3,
]
with
[
N=48881806585380307483594980,
qquad
r=3+4N=195527226341521229934379923.
]
Thus this traversal exits through the **residual-one** token branch, whose recorded endpoint is
[
\operatorname{CR}(0^{r+9}1,[0]).
]

The exact outer-stack continuation from this residual-one endpoint is not yet derived. This is the current frontier of this conditional path; do not infer a cycle or a halting/nonhalting conclusion from the return to the intermediate (E(13)) parameter.

## Next mathematical task

Derive the source-exact continuation of
[
\operatorname{CR}(0^{195527226341521229934379932}1,[0])
]
(or the corresponding token-normalizer configuration) through `mode_CR_n_n_closed` and the `bounce_len` descent. Determine whether it reaches a halt, a new (B/C/Q) family, or a smaller token state. The source module's `bounce_len` theorem supplies a well-founded token-bounce alternative, but the exact successor for this concrete residual-one input still needs to be extracted.

No blank-root reachability theorem is supplied here. The entire chain is conditional on the upstream (E_{160771976531}(13)) state and on the listed source-stack macros.


## Source-mode reduction of the residual-one endpoint

The pinned source module's stack-mode closure lemmas give a further exact reduction. Interpret the endpoint as
[
\mathrm{cfg\_CR\_n\_n}(L,R),\quad
L=[(0,0)]^{r+9}++[(1,0)],\quad R=[(0,0)].
]
Repeated use of `mode_CR_n_n_closed` on the (r+9) leading zero pairs removes them and increments the first coordinate of (R) twice per pair. The remaining configuration is
[
\mathrm{cfg\_CR\_n\_n}([(1,0)],[(2r+18,0)]).
]
The (a_1=1,L_3=[]) case of `mode_CR_n_n_closed` then gives
[
\mathrm{cfg\_EL\_n\_n}([(0,0)],[(0,0),(2r+21,0)]).
]
The exact `mode_EL_n_n_closed` and `mode_DL_0_n_closed` branches give
[
\mathrm{EL}([(0,0),(0,0)],[(2r+21,0)])
\to^*
\mathrm{DL\_0\_n}([(0,0),(0,0)],[(2r+20,0)])
\to^*
\mathrm{DR\_n\_n}([(0,0),(0,0)],[(1,0),(2r+18,0)]).
]
Finally, the (a_1=0,r_1=1) branch of `mode_DR_n_n_closed` invokes the source theorem
[
\texttt{tok\_DR\_2\_0\_closed}\bigl([(2r+18,0)], [0]\bigr).
]
For the concrete residual-one parameter
[
r=195527226341521229934379923,
]
the token subproblem is therefore exactly
[
\texttt{tok\_DR\_2\_0\_closed}
\bigl([(391054452683042459868759864,0)], [0]\bigr).
]

The upstream theorem `tok_DR_2_0_closed` proves that this token subproblem reaches either a halted configuration or a configuration in the main stack system. It does **not** by itself identify which alternative occurs or give the exact successor stack state. Extracting that concrete endpoint is now the decisive local task. In particular, do not claim the tempting (+5) right-counter recurrence until the `tok_DR_2_0_closed`/ `bl_terminates_le` output has been evaluated and checked.


## Update: the residual-one growth macro is now explicit

The previous paragraph's request to extract the output of `tok_DR_2_0_closed` is superseded. The concrete input is `tok_DR([2,0],[(s,0)],[0])) with (s=2r+18). Unfolding the specific (L=[0]) branch of `bounce_len` gives the 15-step token prefix to
[
\mathrm{cfg\_CR\_n\_n}([(0,0),(0,0),(1,0)],[(s+1,0)]).
]
The exact CR/EL/DL/DR branches then take 21 steps back to `tok_DR([2,0],[(s+5,0)],[0])). Hence the residual-one endpoint is now connected to the infinite (+5) growth family by the 36-step macro proved in `ResidualOneGrowthMacro.md`.

The only remaining qualification is formal verification: the 36-step source-level macro has not yet been compiled as a standalone Lean theorem, and the upstream blank-root reachability chain remains conditional.
