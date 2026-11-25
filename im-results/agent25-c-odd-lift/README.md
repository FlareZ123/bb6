# Complete inverse certificate for a Q-even h5 odd-lift subcylinder

## Result
For all natural numbers r,b, the Machine C section root (5,1) cannot reach
```
(4196993 + 2^39*r, 49726 + 2^39*b).
```
In particular, the high-stop candidate with j = 2098495 + 2^38*r and
m >= 19, m = 366503159850 + 2^38*r (mod 2^39), is unreachable. This is a sufficient exclusion, not a classification of all h5 odd-lifts.

The inverse tree has 48 nodes, maximum 17 edges, and includes all admissible predecessors (direct, both bounce parities, and exceptional cases). The key correction to the earlier direct-parent-only argument is that the odd/even intermediate state really can have an odd-bounce predecessor. Both branches are closed by recursively applying the full grammar, with exact 2-adic valuation bounds at each node. The terminal nodes violate the odd-right residue condition. No numerical bound on root-orbit time or bounce depth is assumed.

## Verification
The generic Lean theorem and grammar adapter compiled locally in Lean 4.36.0-rc2 with only standard axioms. That check used the verbatim arithmetic grammar definition and section iteration definition, rather than the complete original import closure. The source specialization invokes the existing section_preimage_all_iff theorem directly. A targeted original-source workflow has been dispatched; its acceptance remains to be established.

Reconstruct the checked artifact and source adapter:
```sh
mkdir -p /tmp/agent25-odd
base64 -d im-results/agent25-c-odd-lift/QEvenH5OddCertificate.lean.xz.b64 | xz -d > /tmp/agent25-odd/QEvenH5OddCertificate.lean
echo 'd4d45b635a6736c7384164a24a619a339a7590c9ee379d9ec24161c007ab53b7  /tmp/agent25-odd/QEvenH5OddCertificate.lean' | sha256sum -c -
python3 tools/lean_compile_closure.py /tmp/agent25-odd/QEvenH5OddCertificate.lean --workdir /tmp/agent25-odd-build --jobs 4 --lean "$(command -v lean)"
```

See also [previous odd-lift reduction](../agent34-s2-pullback/QEvenH5OddLift.md) and [full source inverse grammar](../agent3-c-bounce-inverse/SectionAllInverse.lean).

No global Machine C decision or BB(6) upper bound follows from this isolated cylinder. The useful next step is to generalize certificate construction to adaptive congruence splitting rather than accumulate independent narrow cylinders.
