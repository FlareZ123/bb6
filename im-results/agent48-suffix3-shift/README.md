> **2026-11-24 correction:** The separate universal token nonhalting drafts are withdrawn. T(s) reaches the mirrored I_(s+8), and infinitely many T(s) halt. See [corrected raw reduction](../agent48-token-return-correction/README.md). Accepted suffix shift and residual-zero/two results below remain valid.

# Cryptid D: certified universal ternary singleton-suffix shift

**Status (2026-11-23):** The universal shift and its finite iteration have **passed the original-source Lean kernel build and axiom audit** on the pinned DeepMind #85 source. [Successful CI run 45119240956](https://github.com/FlareZ123/bb6/actions/runs/45119240956) compiled the entire modified original module, and \`#print axioms\` for both theorems returned **only** \`propext\`, \`Classical.choice\` and \`Quot.sound\` (no \`sorryAx\` or \`native_decide\`). The residual-zero source extension has **also passed original-source Lean compilation and axiom audit** ([run 45120434674](https://github.com/FlareZ123/bb6/actions/runs/45120434674)); the residual-two source extension **has passed source-kernel compilation and axiom audit** ([run 45121525070](https://github.com/FlareZ123/bb6/actions/runs/45121525070)), while the **arbitrary-tail extension has now also passed original-source kernel compilation and axiom audit** ([run 45120508529](https://github.com/FlareZ123/bb6/actions/runs/45120508529)). This work does **not** decide whether the original blank-tape six-state machine halts, or determine BB(6).

## Source-coordinate theorem

Let

$$
Q(n,t)=\operatorname{cfg\_CR\_n\_n}\bigl([(0,0)],
 0^{4n+5}++[(0,0),(t,0)]\bigr)
$$

inside the original source namespace \`BusyBeaver.M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA\`. The kernel-checked theorem \`s3_universal_suffix_shift\` is

$$
\boxed{\forall n,t\in\mathbb N,\quad Q(n,t+3)\longrightarrow^+Q(n+1,t).}
\tag{1}
$$

The kernel-checked theorem \`s3_iterated_suffix_shift\` iterates it: for every $n,t,k\in\mathbb N$,

$$
\boxed{Q(n,t+3(k+1))\longrightarrow^+Q(n+k+1,t).}
\tag{2}
$$

Here $\longrightarrow^+$ is the original module's \`ReachesPlus target\`; it is **not** a surrogate stack simulator. There are no assumptions about the size of $t$, and no generic existential token-closure theorem is needed. This reduces the *first singleton suffix digit* to residue $0$, $1$ or $2$ modulo $3$.

## Exact source-branch derivation and clause counts

The original source's eight-successor CR/EL/DL/DR prefix transforms $Q(n,t+3)$ into an EL state with left pair stack $[0,1]$ and right $0^{4n+6}[0,t+3]$. Sweeping the next $4n+7$ zeros in EL gives $\operatorname{EL}(0^{4n+8}1,[t+3])$. Because $t+3\ge3$, EL-positive and DL-positive lead to $\operatorname{DR}(0^{4n+8}1,[1,t])$. Sweep $4n+8$ left zeros in DR and apply DR-positive-positive to reach

$$
\operatorname{CR}([0],0^{4n+10}[t])=Q(n+1,t).
$$

Each individual clause is explicitly matched to an original source theorem. The corrected prefix uses \`s3_dr_zero [] ((0,0)::tail)\`, not the older incomplete boundary, and the proof's zero-run commutations are established by the new \`s3_zero_push\` induction lemma.

The original source's clause lengths sum to **$8n+26$ outer accelerated transitions** and **$24n+75$ primitive Turing-machine steps** for one shift. Summing $k\ge1$ shifts yields

$$
\begin{aligned}
N_{\rm outer}(n,k)&=8nk+4k^2+22k,\\
N_{\rm raw}(n,k)&=24nk+12k^2+63k.
\end{aligned}
\tag{3}
$$

The *reachability* theorems are Lean kernel-checked. The numerical formulas are independently derived by exact source-clause summation but **have not yet been expressed as counted-run Lean theorems**. Do not misrepresent them as a proved bound on total BB(6) runtime.

## Original-source formal artifact

[RootSuffixThreeShift.append.lean](RootSuffixThreeShift.append.lean) is standalone: it uses only the pinned upstream source module's private stack and token definitions. To reproduce, insert the file **before** the upstream module's final namespace \`end\`, at commit \`google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a\`, with upstream Lean \`v4.35.0-rc4\`; run \`lake build BusyBeaver.BB6.Accelerations.M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA\` and \`#print axioms\` for both exported \`s3_*\` shift theorems. The existing manual workflow \`.github/workflows/agent24-cryptid-root-reset-lean.yml\`, dispatched with input \`proof_target=suffix3-shift\`, performed exactly this check on [run 45119240956](https://github.com/FlareZ123/bb6/actions/runs/45119240956).

An independent V8 interpreter transcribed from the upstream CR/EL/DL/DR clauses also reached $Q(n+2,t)$ from $Q(n,t+6)$ for all tested $n=0,1,2$ and $t=0,1,2,3,4,5,6,7,11,20$, with $16n+60$ outer and $48n+174$ raw steps and **no token branch before the endpoint**. This finite test is supporting evidence; source-kernel acceptance, not empirical replay, is decisive.

## Both residual-zero and residual-two source theorems kernel certified

The original-source Lean kernel-certified base cases are

$$
\begin{aligned}
Q(n,0)&\longrightarrow^+D_0(8n+15),\\
Q(n,2)&\longrightarrow^+D_0(8n+21).
\end{aligned}
\tag{4}
$$

The first uses the same eight-step prefix, the zero-right EL sweep, CR-zero sweep, CR-one-empty and the 16-step general tail. The second uses the exact source token \`tok_DR_zero\` / \`tok_DR_1_nil_28\` / \`tok_EL_1\` / \`tok_EL_exit_zero\` cascade from a DL-right-one entry, not a hypothetical token output.

- [RootSuffixBaseZero.append.lean](RootSuffixBaseZero.append.lean) contains source-local \`s3_zero_suffix_reset\` and the entire residue-zero family, **both kernel accepted** on run 45120434674 with axiom profiles exactly \`[propext, Classical.choice, Quot.sound]\`.
- [RootSuffixBaseTwo.append.lean](RootSuffixBaseTwo.append.lean) contains a separately composed local DL-one token closure, \`s3_two_suffix_reset\`, and the entire residue-two family, **both kernel accepted** on run 45121525070 with exactly the standard Lean axiom profile. Neither file depends on the older large RootCountdownSweep/RootRemainderTwoToken research appends.

**Both base cases are source-kernel certified.** Thus equations (1)–(4) yield, for all $k\ge0$,

$$
\begin{aligned}
Q(n,3k)&\longrightarrow^+D_0(8(n+k)+15),\\
Q(n,3k+2)&\longrightarrow^+D_0(8(n+k)+21).
\end{aligned}
\tag{5}
$$

The corresponding source-clause primitive-step totals (not yet counted-path formalized) are

$$
\begin{aligned}
C_0(n,k)&=24nk+12k^2+79k+16n+109,\\
C_2(n,k)&=24nk+12k^2+103k+40n+196.
\end{aligned}
$$

The outer transition totals are $8n(k+1)+4k^2+30k+43$ and $8n(k+1)+4k^2+30k+46$. None of these sums is yet a kernel-checked counted-path theorem. The residual-one family $Q(n,1)$ is not covered by (4) and displays much harder 3-adic token behavior; do not assume a simple universal affine reset there.

## Arbitrary finite suffix tails

[RootSuffixWordShift.append.lean](RootSuffixWordShift.append.lean) **proves in the original-source Lean kernel** the stronger rule

$$
Q(n,t+3;T)\longrightarrow^+Q(n+1,t;T)
$$

for **every finite further pair-stack tail** $T$. The source transitions never inspect $T$. The word-family Lean theorem `s3_universal_word_suffix_shift` and its iterated version **both passed CI 45120508529** with axiom profiles exactly `[propext, Classical.choice, Quot.sound]`. Thus the modular reduction is already an accepted contextual source transition, not merely a singleton-suffix fact.

## Connection to the conditional blank-root research

The earlier [suffix-[5] calculation](../agent48-suffix5-reset/README.md) is the $t=2$ case of (1) composed with the separate residual-two rule (4), giving $Q(n,5)\to^+D_0(8n+29)$. This accounts for the root-corridor conditional step

$$
Q(428\,725\,269\,581,5)\ \longrightarrow^+\
Q(428\,725\,269\,582,2)\ \longrightarrow^+\
D_0(3\,429\,802\,156\,677).
$$

**Both arrows are kernel-checked as uniform theorems.** Their blank-root precursor is still conditional. The upstream blank-root reachability route itself remains unaccepted. There is **no exact BB(6) solution** from these results alone.
