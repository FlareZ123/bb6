# Exact affine inverse certificates for Q-even h5 odd lifts

## Main result

For natural r,b put x=4196993+2^23*r and y=49726+2^23*b. If b>=35*r and any of
```
b = 3*r+2 (mod 8)
b = 3*r+15 (mod 16)
b = 35*r+t (mod 64), t in {24,46,49,54}
```
holds, then (x,y) is unreachable from the Machine C section root (5,1).
These six disjoint classes cover 16 of 64 possible b residues per r.
The high-stop specialization is unconditional in the natural parameters r,w:
set j=2098495+2^22*r, m=4876330+2^22*r+2^23*w and require
`K+j+3*m+5=2^(2*m+2)*(j+3)`. Then (2*j+3,K) is unreachable if
```
(5*r+3*w+4) % 8 = 0
or (5*r+3*w+17) % 16 = 0
or (37*r+3*w+t) % 64 = 0, t in {26,48,51,56}.
```
This excludes precisely one quarter of the targeted parameter lattice by these guards alone (not one quarter of all Machine C high-stop candidates, and not a global Machine C decision).

## Reusable proof method

`Aff` represents natural affine functions in two independent parameters; `Pair` represents section states. `nodeCheck` checks all predecessor alternatives against an exact bounded valuation and validates affine child equations; `checkCertificate_sound` proves unreachability by induction over the certificate. `autoCheck` constructs and checks the predecessor tree automatically, with failure allowed at any insufficient bound or unclassified case. Six successful kernel reductions instantiate the general theorem. The original-source bridge uses `section_preimage_all_iff`, not simulated trajectories.

The earlier explicit 48-node tree (maximum 17 edges) is retained as a reference proof and source adapter. It excludes (4196993+2^39*r,49726+2^39*b) for all natural r,b, including the high-stop cylinder j=2098495+2^38*r, m>=19, m=366503159850+2^38*r (mod 2^39). In particular, the odd-bounce branch missed by the old direct-parent-only argument really exists and must be closed along with the direct branch.

## Verification and reconstruction

[CI 45531058201](https://github.com/FlareZ123/bb6/actions/runs/45531058201) compiled 22 original project modules. `checkCertificate_sound`, `autoCheck_sound`, `quarterExcludes`, `h5QuarterHigh`, and `h5QuarterHighSource` all report precisely `[propext, Classical.choice, Quot.sound]`. The predecessor adapter and earlier source theorems also passed [CI 45529922289](https://github.com/FlareZ123/bb6/actions/runs/45529922289).

```sh
mkdir -p /tmp/agent25-odd
base64 -d im-results/agent25-c-odd-lift/QEvenH5OddCertificate.lean.xz.b64 | xz -d > /tmp/agent25-odd/QEvenH5OddCertificate.lean
base64 -d im-results/agent25-c-odd-lift/AffineH5Quarter.lean.xz.b64 | xz -d > /tmp/agent25-odd/AffineH5Quarter.lean
echo 'd4d45b635a6736c7384164a24a619a339a7590c9ee379d9ec24161c007ab53b7  /tmp/agent25-odd/QEvenH5OddCertificate.lean' | sha256sum -c -
echo 'af25d65ff7dcd1b4fdde3cf3058388ddb3a24fa79b65189ad49da7defdecb740  /tmp/agent25-odd/AffineH5Quarter.lean' | sha256sum -c -
python3 tools/lean_compile_closure.py /tmp/agent25-odd/AffineH5Quarter.lean --source-root /tmp/agent25-odd --workdir /tmp/agent25-odd-build --jobs 4 --lean "$(command -v lean)"
```

See [previous odd-lift reduction](../agent34-s2-pullback/QEvenH5OddLift.md), [full source inverse grammar](../agent3-c-bounce-inverse/SectionAllInverse.lean), and [existing modular inverse approach](../agent42-modular-cone/README.md). The quarter result has not been shown disjoint from all earlier inverse sieves. Remaining parameters need further analysis or a different global invariant.
