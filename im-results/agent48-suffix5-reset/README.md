# Cryptid D: suffix-[5] zero-remainder branch

**Status: new source-derived conditional reduction; uncompiled Lean draft.** This does not prove the original blank-root itinerary or BB(6).

Define \(D_n(c;T)=\operatorname{CR}([0],0^{4n+5}++[c]++T)\) in the pinned DeepMind #85 source's \`cfg_CR_n_n\` coordinates. The missing suffix-[5] zero branch factors, for every natural \(n\), as

\[
\boxed{D_n(0;[5])\longrightarrow^+D_{n+1}(0;[2])
\longrightarrow^+D_0(8n+29).}
\]

The first transition is entirely ordinary CR/EL/DL/DR source rules. The corrected eight-successor prefix gives EL with right \(0^{4n+7}[5]\) and left \([0,1]\); the \(4n+7\) EL-zero sweeps, EL-positive(5), DL-positive(4), \(4n+8\) DR-zero sweeps, and DR-positive-positive produce \(D_{n+1}(0;[2])\). **Cost:** \(8n+26\) accelerated stack successors, \(24n+75\) primitive steps.

For \(m=n+1\), the next corrected prefix and \(4m+7\) EL-zero sweep give DL with left \(0^{4m+8}1\), right \([1]\). The existing \`root_d2_dl_one_z1 (4m+7)\` token closure yields CR with left \(0^{4m+12}1\), right \([0]\). This relies on \`bumpPairHead []=[0]\), *not* [1]. CR-zero sweep gives CR([1],[8m+24]); CR-one-empty gives EL([0],[0,8m+27]); the general tail ends at \(D_0(8m+21)\). **Cost:** \(8m+46\) outer successors and \(40m+196\) primitive steps.

Consequently the full suffix-[5] reduction has proposed exact cost

\[
\boxed{16n+80\ \text{outer successors},\qquad64n+311\ \text{primitive TM steps}.}
\]

These are sums of original source-clause costs, **not yet formally checked counted-run theorems**. A source-transcribed JavaScript accelerated interpreter with the known zero-run/one token macro reproduces the full transition for \(n=0,1,2,3\): respectively output arguments \(29,37,45,53\) and primitive costs \(311,375,439,503\). Finite agreement does not prove the universal formulas.

## Lean artifact and remaining gap

[SuffixFiveReset.append.lean](SuffixFiveReset.append.lean) drafts three source-local \`ReachesPlus\` theorems: \`root_suffix_zero_two_reset\`, \`root_suffix_five_to_zero_two\`, \`root_suffix_five_reset\`. Append it **after** [Agent 12's RootCountdownSweep.append.lean](../agent12-cryptid-root-invariant/RootCountdownSweep.append.lean) and [Agent 2's RootRemainderTwoToken.append.lean](../agent2-root-countdown/RootRemainderTwoToken.append.lean), in the exact source module \`BusyBeaver.BB6.Accelerations.M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA\` from \`google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a\`.

The module has not been compiled. The local shell returned a tool-level \`ClientError\` before commands could run; this is not a Lean diagnostic. Before promoting the result, compile the complete prerequisite source closure and then this append, repair actual diagnostics, and print transitive exported axiom profiles. No new workflow is needed; an existing manual proof-family target can supply the smallest source diagnostic if local execution remains blocked. Full original-machine root reachability and precise counted-run composition remain open.

## Application to the corrected conditional root chain

The preceding [token-zero-cycle dossier](../agent48-token-zero-cycle/README.md) conditionally ends at \(D_0(1\,286\,175\,808\,743;[5])\). Since \(1\,286\,175\,808\,743=3\cdot428\,725\,269\,581\), suffix-preserving countdown reaches \(D_{428\,725\,269\,581}(0;[5])\). The branch above continues it to

\[
\boxed{D_0(3\,429\,802\,156\,677).}
\]

This is **conditional**, not an unconditional halt or nonhalt theorem, and makes no claim about exact BB(6).
