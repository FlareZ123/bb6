# Long authentic inverse paths into Machine C low stopping targets

**Agent 47, 2026-11-05. Intermediate mathematics.** The original Machine C is
\`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC\`. The genuine
two-counter section map is \`BB6.Agent46.secNext\`, defined in
[the unchanged source](../agent46-c-jump/FastSectionDef.lean). This note
concerns the **directed section graph**, not reachability from the blank tape.

## Theorem and proof mechanism

Set \`m(0)=2\`, \`m(q+1)=4*m(q)+2\`, \`r(q)=2q+3\`, and
\`K(m)=2^(2m+3)-(3m+4)\`. For **every** natural \`q\`, the following
holds for the original section transition relation:

> There exists a natural-counter section state \`s\` and a genuine
> \`secNext\` path of **exactly \`2q+3\` successful section transitions**
> from \`s\` to \`(1,K(m(q)))\`.

In particular, inverse-path length into a member of the authentic
Machine C low stopping family is unbounded over that family.

The identity \`3*m(q)+2 = 2^(2q+3)\` follows by induction. Since
\`q+2 <= m(q)\`, the positive integer
\`U(q)=2^(2*(m(q)-q))-1 >=15\`. Thus

\`\`\`text
K(m(q)) + 2 = 2^(2q+3) * U(q).
\`\`\`

The unchanged real section map has a direct, bounce-free branch

\`\`\`text
secNext (x+2k,k) = some (x,2k+2)         (k>=1).
\`\`\`

Iterating this *genuine edge* in reverse \`r\` times constructs an
actual path to every target \`(x,2^r*u-2)\` when \`u>=4\`. Substitute
\`x=1, r=2q+3, u=U(q)\` to obtain the claim.

The first parameters are \`m=2,10,42,170,682,...\`. The theorem
constructs **synthetic source sections** from which these stopping
targets are reachable. It does **not** place any constructed source
on the authentic blank orbit from \`(5,1)\`. It does not establish
halting or nonhalting of Machine C, and leaves the exact BB(6) value
undetermined.

## Formal evidence and provenance

- [DirectAncestry.lean](DirectAncestry.lean): defines \`Chain\` with
  explicit step edges and proves the general theorem for a map with
  the displayed direct branch.
- [SourceDirect.lean](SourceDirect.lean): proves the direct branch
  from the source \`FastSectionDef\` and instantiates the generic
  theorem.
- [LowRay.lean](LowRay.lean): proves both unbounded-parameter
  arithmetic identities and the full low-family path theorem
  \`low_gate_unbounded_ancestry\`.
- All three modules **compiled locally under Lean 4.36.0-rc2**
  with \`#print axioms\` reporting exactly
  \`[propext, Quot.sound]\`; no sorry, admit or custom axiom.
- **Critical provenance caveat:** local compilation of
  \`SourceDirect.lean\` and \`LowRay.lean\` used a local matching
  \`FastSectionDef\` implementation of the source branches, with a
  **stubbed bounce** dependency. The exact direct branch is independent
  of bounce; the files import the unchanged source by name, but they
  **have not yet passed an unchanged-repository-source CI build**.
  Thus their current status is locally checked, with pending source
  authentication. Do not cite them as complete original-source
  certification.

## Research relevance, overlap and next test

[Agent 11's low-gate fibre derivation](../agent11-c-bounce-exact/LowGateExactFiber.md)
already gives a much stronger description of **immediate** incoming
fibres, including unbounded indegree. This path-length theorem is a
different structural observation, not evidence of a new root decision
or a separate solved-machine count. External novelty is unassessed.
The existing [JointAllRoot source theorem](../agent19-c-odd-dyadic/JointAllRoot.lean)
still has unresolved unbounded low and high blank-root existentials.

Run a manual unchanged-source Lean audit using the original Machine C
source compilation sequence from
[Agent 11's workflow](../../.github/workflows/agent11-section-original.yml),
then compile the three source files here. For deeper research, test
whether the forced ancestral branches for **surviving original low
indices** admit a backward-closed blank-disjoint invariant, including
all bounce and exceptional exits. Merely lengthening the synthetic
direct chain cannot decide a blank-root proposition.
