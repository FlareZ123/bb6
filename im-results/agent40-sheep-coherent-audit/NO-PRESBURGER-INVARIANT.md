# No proper infinite ultimately periodic Sheep first-even invariant

**Agent 40, R010, 2026-11-03.** Intermediate mathematical corollary of the **all-even-modulus synthetic quotient strong-connectivity theorem**, independently derived by Agents 22 and 40. It does **not** require the stronger coherent single-orbit theorem. No Sheep blank-root decision or BB(6) bound follows.

## Exact theorem

Let I be an infinite subset of positive even integers. Suppose (a) I is ultimately periodic: above some threshold N its membership depends only on a residue modulo a fixed even m; and (b) for every legal **generic** nonterminal Sheep even-section input x in I, the true first-even successor E(x) also belongs to I. Then I contains **all sufficiently large even integers**.

**Proof.** Let S be the set of even residues represented by members of I above N. Infinitude makes S nonempty. The mixed graph theorem in im-results/agent22-sheep-mixed-hub/MIXED-COMPLETENESS.md proves the generic synthetic first-even graph modulo m is strongly connected; each abstract edge r to s is witnessed by **arbitrarily large** legal generic positive inputs x with x mod m=r and E(x) mod m=s. For any r in S and outgoing edge r to s, choose a witness x>=N. Then x belongs to I by ultimate periodicity. The actual edge E(x)>x is a genuine generic return, so closure yields E(x) in I. As E(x)>=N, periodicity implies s in S. Thus S is closed under every quotient edge. Strong connectivity and nonempty S force S to contain every even residue class. Hence every sufficiently large even integer is in I. QED.

**Important:** Because membership is fully determined by the residue above N, different integer witnesses may be chosen on different edges. We therefore need only the *synthetic graph* connectivity theorem, with arbitrarily large legal witnesses. The stronger single-coherent-orbit theorem is compatible and gives more information about freely chosen starts, but is **not** a premise of this corollary. An earlier draft of this note unnecessarily invoked coherent trajectories; the argument here states the simpler sufficient dependency.

## Presburger-definable certificate no-go

A standard theorem states that every one-variable Presburger-definable subset of the natural numbers is ultimately periodic; see the discussion and Corollary 2.5 at https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/dichotomy-for-kautomatic-expansions-of-presburger-arithmetic/8B56A89B78B1EF1DC6BDA34066186F5D .

Therefore no **univariate Presburger-definable predicate of the current Sheep even-section integer** can simultaneously (1) contain the authentic blank even-section entry 10, (2) be forward inductive under every defined nonterminal first-even return, including exceptional branches, and (3) exclude every halting power of two 2^j for j>=2.

**Proof.** If such a predicate existed, its closure and exclusion of all terminal powers would force the actual even orbit from 10 to remain forever in the predicate. The original-source-certified even-return accelerator provides a defined next return at every nonterminal even state; the return is strictly increasing, so the invariant set would be infinite. Since every Presburger-definable one-variable set is ultimately periodic, the theorem above would force membership of all sufficiently large even integers, including large powers of two, contradicting (3).

This rules out any globally inductive finite mixture of constant-modulus congruences and linear thresholds with finite exceptional cases, even when quantifiers over auxiliary natural numbers are allowed **inside a univariate Presburger formula**. It leaves open richer invariants using multiplication, exponentials, tape state, unbounded history, growing moduli, or other non-Presburger structure.

## Source and evidence status

Original table: 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE. Source reduction: im-results/agent16-sheep-even-return/EvenSourceBridge.lean, successful original-source CI 41505950547. Mixed graph: im-results/agent22-sheep-mixed-hub/MIXED-COMPLETENESS.md and independent all-odd-cofactor CRT proof from Agent40 recorded in communications/agent22/2026-11-03T0603Z_agent40-mixed-all-odd-proof-candidate.md. Source-connected intermediate audit: im-results/agent40-sheep-coherent-audit/README.md. The all-modulus quotient theorem remains paper proved with extensive exact checks and has not undergone complete all-parameter kernel certification or external novelty review. Keep this no-go theorem in intermediate results pending those reviews.

It does not establish nonhalting of the true Sheep blank-root orbit or determine BB(6).