# Cryptid D: source-certified contextual ternary suffix reduction

*23 November 2026 · Original-source Lean theorems · Exact BB(6) remains unresolved.*

## Result

Inside the **original** six-state, two-symbol machine encoded at \`google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a\`, module \`BusyBeaver.BB6.Accelerations.M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA\`, define

\[
Q(n,t;T)=\operatorname{cfg\_CR\_n\_n}
\left([(0,0)],\;[(0,0)]^{4n+5}\mathbin{+\!\!+}
[(0,0),(t,0)]\mathbin{+\!\!+}T\right).
\]

Let \(Q(n,t)=Q(n,t;[])\) and
\(D_0(z)=\operatorname{cfg\_CR\_n\_n}([(0,0)],[(0,0)]^5++[(z,0)])\).
The arrow \(\to^+\) denotes the original \`ReachesPlus target\`, i.e. a nonempty finite path of the actual source Turing machine.

**Theorem A (contextual ternary shift).** For all \(n,t\in\mathbb N\), all finite pair-stack tails \(T\), and all \(k\ge1\),

\[
\boxed{Q(n,t+3k;T)\;\to^+\;Q(n+k,t;T).}
\]

This holds even with arbitrary untouched suffix \(T\). The kernel-checked source declarations are \`s3_universal_word_suffix_shift\`, \`s3_iterated_word_suffix_shift\` in [RootSuffixWordShift.append.lean](../im-results/agent48-suffix3-shift/RootSuffixWordShift.append.lean), whose original-source compilation and \`#print axioms\` succeeded in [CI 45120508529](https://github.com/FlareZ123/bb6/actions/runs/45120508529). Independently, the special case \(T=[]\) is kernel checked as \`s3_universal_suffix_shift\` and \`s3_iterated_suffix_shift\` in [RootSuffixThreeShift.append.lean](../im-results/agent48-suffix3-shift/RootSuffixThreeShift.append.lean), [CI 45119240956](https://github.com/FlareZ123/bb6/actions/runs/45119240956).

**Theorem B (residue-zero return).** For every \(n,k\in\mathbb N\),

\[
\boxed{Q(n,3k)\;\to^+\;D_0(8(n+k)+15).}
\]

The \(k=0\) base \`s3_zero_suffix_reset\` and positive-\(k\) \`s3_zero_residue_family\` both passed source-exact Lean and axiom audit in [CI 45120434674](https://github.com/FlareZ123/bb6/actions/runs/45120434674); see [RootSuffixBaseZero.append.lean](../im-results/agent48-suffix3-shift/RootSuffixBaseZero.append.lean).

**Theorem C (residue-two return).** For every \(n,k\in\mathbb N\),

\[
\boxed{Q(n,3k+2)\;\to^+\;D_0(8(n+k)+21).}
\]

The \(k=0\) base \`s3_two_suffix_reset\`, with explicit original \`tok_DR_zero\`, \`tok_DR_1_nil_28\`, \`tok_EL_1\`, \`tok_EL_exit_zero\` source token closure, and \`s3_two_residue_family\` both passed original-source kernel compilation in [CI 45121525070](https://github.com/FlareZ123/bb6/actions/runs/45121525070). See [RootSuffixBaseTwo.append.lean](../im-results/agent48-suffix3-shift/RootSuffixBaseTwo.append.lean).

Every exported theorem above has \`#print axioms\` equal to **only** \`[propext, Classical.choice, Quot.sound]\`: no \`sorryAx\`, no surrogate interpreter, no unverified native-decision oracle. All CI checks compile the pinned original module with source-local Lean append fragments and Lean \`v4.35.0-rc4\`.

## Mathematical mechanism

The contextual shift uses the corrected eight-successor CR/EL/DL/DR prefix to expose \(\mathrm{EL}([0,1],0^{4n+6}[0,t+3]++T)\), followed by a right-to-left EL zero sweep, EL-positive and DL-positive, a left-to-right DR zero sweep, and DR-positive-positive. None of these transitions examines \(T\). The base-zero proof handles an empty EL-right tape and then ordinary CR, EL, DL, DR sweeps; the base-two proof replaces the DL-right-one token entry with a full original-source token cascade. Thus the rule genuinely reduces an infinite-state family to the two explicit returns above and one unresolved residue-one class.

Source-clause primitive-step sums (not yet certified as counted-run Lean theorems) are \(24n+75\) for one ternary shift, \(16n+109\) for the zero base, and \(40n+196\) for the two base. Composing \(k\) shifts gives respectively \(24nk+12k^2+79k+16n+109\) and \(24nk+12k^2+103k+40n+196\) raw primitive steps for the zero and two congruence classes.

An immediate certified corollary is
\[
Q(n,5)\to^+Q(n+1,2)\to^+D_0(8n+29),
\]
including the **conditional** pair-stack continuation \(Q(428725269581,5)\to^+D_0(3429802156677)\) if that input configuration is ever reached.

## Limits and open objective

The residue-one singleton family \(Q(n,3k+1)\) only reduces to \(Q(n+k,1)\); no decision is claimed for it. More importantly, these theorems alone do not establish a blank-tape orbit into the \(Q\) family, prove this six-state holdout halts/nonhalts from blank, or yield a global six-state upper bound. Thus **the exact value of BB(6) is still open**.

See the [research dossier](../im-results/agent48-suffix3-shift/README.md) for source proofs, additional uncompiled strengthening ideas, and method-level reproducibility.
