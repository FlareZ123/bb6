# Machine B cross-radix congruences and residue sieve (Agent 30)

2026-11-03. New two-slot exploratory programme [R-20261103T122530Z-agent30-crossradix](../../research/issues/R-20261103T122530Z-agent30-crossradix.md). **Intermediate mathematics**. The six-state rooted machine, its blank-sampled bit, and exact BB(6) remain undecided by this investigation. No academic novelty is claimed.

## Source and result

Agent 18's exact one-dimensional encoding of Machine B `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE` is

```
G(z) = 3*(z/2) + 4 + 5*(z%2)             (Nat operations)
G^[0](z)=z,  G^[n+1](z)=G(G^[n](z)).
```

The original source is [`im-results/agent18-b-cycle/BOneDim.lean`](../agent18-b-cycle/BOneDim.lean). The all-natural theorem, proved in [`Agent30CrossRadix.lean`](Agent30CrossRadix.lean), is

```
∀ n x y m : Nat,
  G^[n](x) % (3^n*m) = G^[n](y) % (3^n*m)
    ↔ x % (2^n*m) = y % (2^n*m).
```

This includes `m=0`, interpreted using Lean's ordinary Nat modulo-zero convention. With `m=1`, the nth output residue modulo `3^n` depends **exactly** on the input residue modulo `2^n`.

The elementary one-step lemma is `G(x)≡G(y) (mod 3m) ↔ x≡y (mod 2m)`, valid for all natural x,y,m. To see this, write `x=2q+p`, `p∈{0,1}`. Then `G(x)=3q+4+5p`. The output remainder modulo 3 determines p, and after dividing by 3 its remainder modulo m determines q modulo m. Apply this lemma at n+1 and use the induction hypothesis with modulus 2m.

The derived lemmas in [`Agent30CrossRadixCantor.lean`](Agent30CrossRadixCantor.lean) prove that the canonical inputs `0≤x<2^n` have **pairwise distinct** outputs modulo `3^n`, and represent every possible nth output residue. Hence there are exactly `2^n` attainable residue classes out of `3^n`; the proportion is `(2/3)^n`. Any actual scalar orbit, after at least n steps, lies in one of these classes modulo `3^n`, regardless of its seed.

## Exact weighted parity word

[`Agent30CrossRadixWord.lean`](Agent30CrossRadixWord.lean) proves the identity

```
2^n * G^[n](z) = 3^n*z + W(n,z)
W(0,z) = 0
W(n+1,z) = 3*W(n,z) + 2^n*(8+7*(G^[n](z)%2)).
```

Therefore `2^n*G^[n](z) ≡ W(n,z) (mod 3^n)`. The residue encodes a weighted finite word of successive parity bits. This is a concrete radix description of the same output classes. It is analogous to established symbolic dynamics for generalized Collatz-type maps, whose parity vectors and finite congruence coding are classical; see Terras/Everett and Lagarias. We have not established distinct external novelty of this specific two-to-three cross-modulus formula.

## Linear-depth residue membership experiment

[`residue_membership.py`](residue_membership.py) provides `in_output_residues(n,r)`, an O(n)-arithmetic-operation algorithm to decide whether `r mod 3^n` is an nth output residue without enumerating `2^n` inputs.

At each inverse step, a residue `r mod 3^k` with `r%3==2` is forbidden. Otherwise its penultimate counter has parity `p=0` if `r%3==1`, and `p=1` if `r%3==0`. Reconstruct its residue modulo `3^(k-1)` by

```
q = (r - 4 - 5*p) / 3
r_next = (2*q+p) mod 3^(k-1).
```

The quotient is an exact signed integer, so negative intermediate values are legitimate; the Python `//` expression divides a multiple of 3. For sufficiency of each inverse step, note the exact dyadic shift `G^[k](x+2^k)=G^[k](x)+3^k`: any previously available `3^k` residue has both possible output parities on two inputs, allowing the selected predecessor parity. This shift is proved in [`Agent30CrossRadixParity.lean`](Agent30CrossRadixParity.lean), and independently existed in Agent 10's [`Agent10Shift.lean`](../agent10-b-parity/Agent10Shift.lean).

Python independently enumerated all `3^n` residues and all `2^n` canonical inputs for each n=0,...,12 and found the algorithm's accepted classes identical to the exact outputs. Additional generated-output tests for n=20,40,100 passed. **The Python decoder itself has not yet been kernel-certified as a function**; the underlying all-n output-collision theorem and exact shift are Lean proofs.

## Decisive limitation for the actual blank stop condition

[`Agent30CrossRadixParity.lean`](Agent30CrossRadixParity.lean) proves for every n,z that

```
G^[n](z+2^n) = G^[n](z)+3^n.
```

The two outputs are congruent modulo `3^n` but have **opposite parity**, since `3^n` is odd. Therefore the complete universal output-residue sieve alone cannot determine parity of `G^[n](x)` when the input seed is unconstrained. In the original rooted Machine B stopping criterion, the seed is specifically zero and the tested times are recursively sampled indices `scalarA(n)`; the seed-shift witnesses are *not* actual blank starts. They show a limitation of this proposed technique, not impossibility of a seed-specific method.

Agent 18 and Agent 10 already reduced Machine B halting to whether `G^[scalarA(n)](0)` is even at one of its particular indices. None of the results in this folder proves or refutes that property or improves a BB(6) bound. Promising future work would need a genuine seed-zero arithmetic restriction, coupling the recursive sample indices to these residues, or a substantially different approach.

## Verification and provenance

- Lean 4.36.0-rc2 local compiled `Agent30CrossRadix.lean`, `Agent30CrossRadixCantor.lean`, `Agent30CrossRadixWord.lean`, and `Agent30CrossRadixParity.lean`. Their printed theorem audits involve only `propext`, `Classical.choice` where needed, and `Quot.sound`. There is no `sorry`, `sorryAx`, or assumed theorem.
- [`Agent30CrossRadixSource.lean`](Agent30CrossRadixSource.lean) defines an equality bridge to the unmodified upstream `BB6.OneDim.iterG`. It typechecked locally **against an exact-signature scratch stub**, not a full original import. The stub is not part of this repository and is not evidence of an original-source check.
- Existing manual-only [`agent30-b-curvature.yml`](../../.github/workflows/agent30-b-curvature.yml) was extended to compile the local theorem and the bridge together with original Agent 18 files. [Run 41637502708](https://github.com/FlareZ123/bb6/actions/runs/41637502708) (2026-11-03 12:39 UTC) failed within four seconds, before build steps; targeted Actions log retrieval returned HTTP 404. **Original-source CI certification remains pending**; this failure does not refute the local proof.
- Formal theorem source SHA256 of the locally checked `Agent30CrossRadix.lean`: `d5fbd7847f81f3dd94b9c5bab7f234086a3c2139a24b2d30e781dd78b38e5879`.
- Closest established related local work: [Agent 10 B parity, dyadic shift, source bridge](../agent10-b-parity/README.md), [Agent 30 affine quotient obstruction](../agent30-b-dyadic-curvature/README.md). The latter classifies *same-modulus all-input affine formulas*, unlike this nonlinear cross-modulus property.

This dossier belongs in `im-results/` until independent external novelty and scientific significance are established. Do not use it as an unresolved-root decision.

## Complete finite congruence quotient theorem (stronger than R007)

After the initial cross-radix result, a stronger all-iterate classification was discovered and **kernel-checked locally** in [`Agent30BFiniteFactor.lean`](Agent30BFiniteFactor.lean). For every positive `n,m`,

```
(∀ x y : Nat, x%m=y%m → G^[n](x)%m=G^[n](y)%m) ↔ m ∣ 7.
```

Since m is positive, the only possibilities are m=1 and m=7. This classifies every well-defined map induced on the *standard residue ring* `Nat modulo m`, without assuming that the induced map has an affine formula. It strictly strengthens the prior [Agent30 R007](../agent30-b-dyadic-curvature/README.md) statement, which classified only all-input affine congruences. **It does not classify non-congruence finite partitions, seed-specific quotient automata, or arbitrary finite transducers.**

The key necessity witness is the pair of inputs `0` and `2^(n-1)*m`, which are congruent modulo m. The previously established exact shift identity yields

```
G^[n-1](2^(n-1)*m) = G^[n-1](0) + 3^(n-1)*m.
```

Let `z=G^[n-1](0)` and `q=3^(n-1)`, which is odd. For any `m>0`, the elementary lemma `G_odd_multiplier_obstruction` proves

```
G(z+m*q)%m = G(z)%m  →  m ∣ 7.
```

If m is even, the shift by m*q is an even input increment, and its output difference is an odd multiple of m/2, contradicting congruence modulo m. If m is odd, the input increment toggles parity and the doubled-output identity `2G(z)=3z+8+7(z%2)` reduces output congruence to `7≡0 (mod m)`. These arguments are implemented without a general quotient/affineness assumption. Sufficiency follows from `G(z)+7*(z/2)=5z+4`, which makes `G` affine modulo divisors of 7, hence all its iterates descend.

The new exact source-bridge statement is [`Agent30FiniteFactorSource.lean`](Agent30FiniteFactorSource.lean). It compiles locally against an exact-signature scratch copy of Agent18's scalar definitions; no successful *original-source* import exists yet. The existing dispatch-only CI workflow was extended to check both this theorem and the new source bridge, but [run 41640186396](https://github.com/FlareZ123/bb6/actions/runs/41640186396) again failed almost immediately before Lean could run. Treat original-source verification as **pending**.

The all-natural theorem, its exact single-pair obstruction, and its accompanying local kernel audits are genuine mathematical consequences of the exact scalar model. Their novelty outside the repository remains unestablished. They **do not settle** the true blank-seed parity sample or any BB(6) machine.
