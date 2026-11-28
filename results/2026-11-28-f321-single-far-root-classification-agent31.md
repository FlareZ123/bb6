# F321: exact source-root classification of the single-Far terminal family

**28 November 2026 — Agent 31.**

This result completes the arithmetic classification of the F321 terminal inverse
words consisting of a block of High moves followed by one final Far move. The
previous \`HighFarTerminalFamily.lean\` constructed an infinite family
\`H^(24k+22) F\` that survives the coarse source filters. The new converse
shows that, at an authentic source-reachable small-second state, **there are no
other members of this word class**.

The theorem is about the exact F321 source-counter relation \`CounterReach\`
from the blank-counter seed \`(1,1)\`. It does not prove F321 nonhalting or a
BB(6) upper bound.

## The exact classification

Let \`highThenFar n\` be the formal inverse word corresponding to \`n\` High
moves followed by one Far move. Suppose

- \`CounterReach 1 1 m R c\` for some authentic source time \`m\`;
- the small-second endpoint satisfies \`c=1 ∨ c=2\`; and
- \`FormalInversePath d (highThenFar n) R c\` is a genuine terminal inverse
  path to the terminal gate indexed by \`d\`.

Then
\[
  c=1,\qquad n\equiv22\pmod{24}.
\]
More strongly, there is a unique natural number \(k\) such that
\[
  n=24k+22,\qquad
  d=\operatorname{dangerT}(k),\qquad
  R=\operatorname{dangerR}(k),\qquad
  c=1.
\]
Thus the previously constructed dangerous family is converse-complete for the
entire source-root-compatible \`H^n F\` terminal class.

The formal theorem is
\`BB6.Agent31F321SingleFar.highThenFar_root_is_danger_family\` in
[\`SingleFarRootClassification.lean\`](../im-results/agent31-f321-bulk/SingleFarRootClassification.lean).

## Why the phase collapses to 22 modulo 24

The proof combines two independently exact ingredients.

First, the accepted modulo-384 source quotient implies that any source-reached
state with second counter 1 is either the initial seed or has
\[
  R\bmod24\in\{6,8,14,22\}.
\]
This is rechecked in Lean by a finite kernel decision over the already accepted
quotient mask.

Second, for \`H^n F\`, the exact terminal equation and exact inverse sum law are
\[
  7d=2^{n+4}+3,\qquad R+n+6=2d.
\]
Eliminating \(d\) gives the particularly useful root equation
\[
  \boxed{7R+7n+36=2^{n+5}}.
\]
Terminal integrality already forces \(n\equiv1\pmod3\), while for exponents at
least three powers of two modulo 24 alternate between 16 and 8 according to
parity. Combining this two-cycle with the five possible source-root residue
cases above leaves exactly
\[
  R\equiv22\pmod{24},\qquad n\equiv22\pmod{24}.
\]

A useful strengthening is that the proof does **not** need the separate
terminal phase assumption \`d % 6 = 1\`. Source reachability plus the exact
inverse equations already force the full modulo-24 phase.

## Adaptive bit-length reformulation

For the surviving family, let \(L\) be the ordinary binary bit-length of the
root anchor \(R\). Since \(n=24k+22\), the master equation places \(R\)
strictly between \(2^{n+2}\) and \(2^{n+3}\), so \(L=n+3\). Substitution gives
the equivalent digital target
\[
  \boxed{7R+7L+15=2^{L+2}}.
\]
Thus the uniform root problem for this class can be stated without the suffix
parameter \(k\): exclude source-reached second-counter-one anchors satisfying
this exact bit-length equation. This is an elementary corollary of the
kernel-checked master equation and the \(n=24k+22\) classification; the
bit-length reformulation itself is recorded here as paper arithmetic rather
than as an additional Lean theorem.

This explains why fixed shallow residue sieves are structurally inadequate:
the target carries a modulus condition of depth growing with \(L\). The next
useful invariant should therefore track an adaptive 2-adic phase of the
authentic root anchor, rather than enumerate a fixed modulus or continue
one-\(k\)-at-a-time window proofs.

## Formal verification

GitHub Actions run **46156483458** completed successfully under Lean
**4.36.0-rc2**. The dedicated source gate compiled the exact counter map,
terminal-word arithmetic, modulo-384 source quotient, the previously
constructed High/Far family, and the new classification. The gate rejects
\`sorryAx\`; the accepted run completed with no such dependency.

An earlier green run, **46156143207**, accepted the first version that still
used the redundant terminal \`d % 6 = 1\` phase assumption. The final theorem
above is the stronger assumption-free version from run 46156483458.

## Consequence for the remaining F321 proof

Within the terminal class whose last-anchor suffix is exactly \`H^n F\`, future
work no longer needs to search over arbitrary \(n\), \(d\), or small-second
anchor phases. It is enough to decide the single explicit family
\[
  (R_k,1)\xrightarrow{H^{24k+22}F}(T_k+1,T_k).
\]
The existing all-time root cuts for the first members of this family therefore
attack the exhaustive surviving branch of this word class rather than a
specially chosen subfamily.

The remaining mathematical problem is uniform: prove that no dangerous-family
anchor can occur on the authentic root orbit for any \(k\), or derive a
stronger root invariant that excludes the family at once.
