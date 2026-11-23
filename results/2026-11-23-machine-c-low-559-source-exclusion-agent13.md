# Machine C: 559/4096 authentic-source exclusions in a necessary low-stop family

**Agent 13 · 23 November 2026 · original-machine Lean 4.36.0-rc2 kernel accepted.**

## Exact mathematical claim

Let \(\mathcal R\) be the set of two-counter states reached from the actual blank-input section entry \((5,1)\) by the original six-state two-symbol Machine C section map `BB6.Agent46.secNext`. For \(z\in\mathbb N\), define
\[
m=512z+67,\qquad K_m=2^{2m+3}-(3m+4).
\]
Introduce the following disjoint modular families:
\[
\begin{split}
P(z)\quad\Longleftrightarrow\quad&
z\equiv13\pmod{16}\ \lorz\equiv5\pmod{64}\ \lorz\equiv25\pmod{32}\ \lor\\
&z\equiv9,21\pmod{128}\ \lorz\equiv65\pmod{512}\ \lor\\
&z\equiv1729\pmod{2048}\ \lorz\equiv3521\pmod{4096}\ \lor\\
&z\equiv165\pmod{256}\ \lorz\equiv105\pmod{512}\ \lor\\
&z\equiv469,869,585\pmod{1024}.
\end{split}
\]

**Theorem.** For every \(z\ge0\), if \(P(z)\), then \((1,K_m)\not\in\mathcal R\). This is a genuine original-machine blank-origin nonreachability result at **all section times**. The disjoint clauses cover exactly
\[
\frac{512+8+2+1+16+8+4+4+4}{4096}
=\boxed{\frac{559}{4096}}
\]
of the index residues in the fixed necessary low-stop parameter ray \(m=512z+67\).

The source theorem is `BB6.Agent13Low559Source.low_stop_fivehundredfiftynine_mod4096_unreachable` in [LowM67All559Source.lean](../im-results/agent13-residual-frontier/LowM67All559Source.lean). Its statement explicitly requires \(k+3m+4=2^{2m+3}\) and concludes \(\neg\mathrm{CReach}(1,k)\). The source-only case proofs were accepted in [CI 45254908517](https://github.com/FlareZ123/bb6/actions/runs/45254908517), and the final unified theorem is part of the 253-module accepted source closure [CI 45255502605](https://github.com/FlareZ123/bb6/actions/runs/45255502605). No finite-orbit cutoff or M16/M32 quotient-unreachability assumption is used.

This theorem does **not** cover \(559/4096\) of *all machine halts*, nor all six-state Turing machines. It narrows one necessary halting subfamily of one unresolved machine.

## Exhaustive inverse mechanism

The original halting-stop arithmetic gives \(K_m=256u+51\) where
\[
u=2^{2m-5}-6z-1.
\]
Four independent source-exact inverse equivalences reduce reachability of \((1,256u+51)\) to reachability of
\[
R_u=(180u+28,\ 166u+25).
\]
The explicit path is
\[
(1,256u+51)\leftarrow(128u+24,192u+36)
\leftarrow(320u+58,96u+17)
\leftarrow(208u+35,152u+25)
\leftarrow R_u,
\]
where arrows encode the forced backwards source reduction and preserve authentic blank-origin reachability. The original [two-parent proof](2026-11-23-machine-c-low-source-sixteen-agent13.md) established this connection.

For the valuation-four/five families, \(R_u\) has exactly two **possible** incoming original-source bounce depths \(n=0,2\). For the valuation-six families, it has three possibilities \(n=0,2,4\). “Possible” means that *every genuine predecessor* must be in the listed fan; no fabricated inverse edge is assumed. In either case an actual predecessor has forced arithmetic coordinates
\[
a_n=\frac{346u+54}{2^{n+1}}-3,\qquad
k_n=\frac{512u+78-a_n-7-3n}{2}.
\]
The exhaustive depth restrictions, including all exceptional small-input cases, are certified by the original-source theorems `even_odd_small_valuation_parent` and `even_odd_valuation_six_parent`. In all nine added or prior families, the depth-zero parent has odd right counter and sum \(2\pmod4\), which is excluded from the actual blank orbit by the proven odd-image invariant.

The seven **additional** disjoint classes proved in this invocation are:

| \(z\) class | Equivalent \(u\) class | Fan size | Forced inverse path for highest-depth parent | Terminal odd-right sum |
| --- | --- | ---: | --- | --- |
| \(1729\pmod{2048}\) | \(1913\pmod{4096}\) | 3 | B–O–B–B, depth 4 | \(1\pmod4\) |
| \(3521\pmod{4096}\) | \(3449\pmod{8192}\) | 3 | B–O–B–F, depth 4 | \(2\pmod4\) |
| \(165\pmod{256}\) | \(33\pmod{512}\) | 2 | O–E, depth 2 | \(2\pmod4\) |
| \(105\pmod{512}\) | \(393\pmod{1024}\) | 2 | A–O–B–B, depth 2 | \(1\pmod4\) |
| \(469\pmod{1024}\) | \(1281\pmod{2048}\) | 2 | O–B–F–B, depth 2 | \(2\pmod4\) |
| \(869\pmod{1024}\) | \(929\pmod{2048}\) | 2 | O–F–A–B, depth 2 | \(2\pmod4\) |
| \(585\pmod{1024}\) | \(585\pmod{2048}\) | 2 | A–O–F–B, depth 2 | \(2\pmod4\) |

Here A is the original even-right affine inverse, B the original even-right six-residue inverse, O the original odd/odd low-valuation inverse, E the even/odd valuation-three inverse, and F the even/odd valuation-two inverse. Every letter denotes an exact source-checked reachability equivalence on the indicated affine state; Lean's `omega` proves its guard and equality **for every nonnegative progression parameter**, not for finitely many samples. The other depth-two branches in the two new valuation-six families take B–B–A to forbidden sum \(2\pmod4\), while the original depth-zero branch is directly forbidden.

Each terminal state has odd right counter at least five and coordinate sum \(1\) or \(2\pmod4\). The original blank section odd-image theorem forbids all of these, so the complete inverse fan is nonreachable, hence \(R_u\) and ultimately \((1,K_m)\) are nonreachable.

## Formal proof chain and exact halting integration

The source-level seven-family proofs are [LowM67D4SecondSource.lean](../im-results/agent13-residual-frontier/LowM67D4SecondSource.lean), [LowM67D4ThirdSource.lean](../im-results/agent13-residual-frontier/LowM67D4ThirdSource.lean), and [LowM67FiveD23Source.lean](../im-results/agent13-residual-frontier/LowM67FiveD23Source.lean). The previously accepted six clauses are [the sixteen two-parent classes](2026-11-23-machine-c-low-source-sixteen-agent13.md) and [the valuation-six class at \(z\equiv65\pmod{512}\)](2026-11-23-machine-c-low-d4-three-parent-agent13.md). Source CI results, all Lean 4.36.0-rc2 with only standard axioms and no `sorryAx`, are:

- [45252580437](https://github.com/FlareZ123/bb6/actions/runs/45252580437): first new three-parent cylinder, 62 modules.
- [45253172542](https://github.com/FlareZ123/bb6/actions/runs/45253172542): second new three-parent cylinder, 63 modules.
- [45254908517](https://github.com/FlareZ123/bb6/actions/runs/45254908517): five new two-parent cylinders, 64 modules.
- [45255502605](https://github.com/FlareZ123/bb6/actions/runs/45255502605): complete **253-module exact-halting theorem closure**. The exported `BB6.Agent13Low559Joint.blank_halts_iff_six_low559` has axiom profile **`[propext, Classical.choice, Quot.sound]`**.

The exact-halting equivalence is in [LowM67All559Criterion.lean](../im-results/agent13-residual-frontier/LowM67All559Criterion.lean). It strengthens the accepted original blank-root iff by adding modular low-parameter restrictions; it **does not change or weaken** the unbounded high-parameter existential. The novel additional banned values of \(m\) relative to the prior 65/512 source result are:
\[
\begin{gathered}
m\not\equiv885315\pmod{1048576},\quad
m\not\equiv1802819\pmod{2097152},\\
m\not\equiv84547\pmod{131072},\quad
m\not\equiv53827\pmod{262144},\\
m\not\equiv240195,444995,299587\pmod{524288}.
\end{gathered}
\]
These restrictions are **necessary** for any low-branch witness, not sufficient for halting.

## Open mathematical obligation

The original Machine C halting status is still unknown. The source-exclusion theorem removes a further seven infinite, disjoint families, but **unboundedly many low-index and high-index witnesses remain**. On the valuation-six and higher rays the complete predecessor fan becomes wider with the 2-adic valuation, so finite depth-two/three schemes alone cannot decide the full infinite problem. A full BB(6) proof additionally requires a universal maximality upper bound across all standard six-state machines and an exact attainable champion step count. No such claim is made here.

**Originality boundary:** novelty here is relative to the strongest earlier source-certified result preserved in this repository. External literature priority has not been fully assessed; the result should not be advertised as a complete Busy Beaver solution.
