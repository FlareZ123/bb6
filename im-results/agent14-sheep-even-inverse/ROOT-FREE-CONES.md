# Four exact, seed-independent finite Sheep E inverse cones

Agent 14, 2026-11-03. **Intermediate theorem by explicit integer/modular certificates, not a new machine decision.** The original six-state Sheep machine and BB(6) remain unresolved. This note strengthens the previously established blank-10 exclusions for four exponent congruence families to statements about **every possible even starting section state**. The r=138 case overlaps Agent 40's independently derived two-predecessor, no-grandparent analysis in [its review](../agent40-r138-peer-audit/README.md); the other three infinite families and their common structural description are the extension documented here. External academic novelty and an all-four-family Lean theorem have not been established.

## Statement

Use the authentic Sheep first-even return relation \`E(x)=y\` from [Agent 16](../agent16-sheep-even-return/README.md). A successful nonhalting transition is strictly increasing and sends an even section state to an even section state. Write \`EvenReach(x,y)\` for its reflexive-transitive closure. Let \`R=2^(r+4860*k)\`, with \`k>=0\`. The following are integers and are even:

| r | A, the direct parent of R | B, the other ancestor | Edges |
| --- | --- | --- | --- |
| 138 | (8R-2)/15 | (32R-68)/81 | A→R, B→R |
| 1218 | (8R-2)/15 | (32R-68)/81 | A→R, B→R |
| 402 | (8R-2)/15 | (512R-4688)/1485 | B→A→R |
| 1738 | (8R-2)/15 | (64R-196)/135 | B→A→R |

**Exact basin assertion, all k:** For every even natural \`x>=6\`,
\[
  \operatorname{EvenReach}(x,R)\quad\Longleftrightarrow\quad
  (x=R\ \lor\ x=A\ \lor\ x=B).
\]
In particular, every listed halting-power target has exactly **three** states in its full even-section predecessor basin, including itself. There are precisely two incoming edges into \`R\` for r=138/1218, or one incoming edge into each of \`R\` and \`A\` for r=402/1738. Every leaf \`A,B\` in the fork or \`B\` in the chain has zero incoming even-section edges. Since the genuine even-section start \`10\` is outside every basin, the already-known blank-10 nonreachability follows.

This result concerns the *even-section E graph*. It classifies all possible ancestors of **these particular power targets**. It does not classify other halting powers, the actual infinite blank-10 trajectory, or the entire six-state search space.

## Proof and finite verifiable arithmetic obligations

For target node \`Y=(2^(r+4860*k+s)+b)/d\`, where \`d>0\` is odd, every even source of an E edge has an integer \`h>=0\` and one of the following disjoint source forms.

For a generic source \`x=2^a v\` with \`a>=1\`, odd \`v>=5\`, set
\[
 D=d3^h,\qquad C=2^h(b-d)+D,\qquad
 T=D(2^{a+1}+1),\qquad B_0=2C-D(2a-1).
\]
The source equations imply
\[
 D\mid 2^{r+4860k+s}+b-d,\qquad
 Tv=2^{r+4860k+s+h+1}+B_0. \tag{G}
\]
The source is valid only when \`v\` is odd and at least five. Since \`T\` is odd, its necessary and sufficient integrality/oddness congruence is
\[
2^{r+4860k+s+h+1}+B_0\equiv T\pmod {2T}.
\]
For an exceptional source \`x=3*2^a\`, the corresponding exact equation is
\[
 3D2^a+Da+3D-C=2^{r+4860k+s+h}. \tag{S}
\]
These are exhaustive by the original source-connected algebraic split [SheepEvenSourceAlgebra.lean](SheepEvenSourceAlgebra.lean), and both retain the odd-\`u\` condition from \`Y=1+3^h u\`.

Each node in the certificate has a fixed \`H\` and a finite valuation cutoff \`A_h\`. If \`h>=H\`, divisibility of \`Y-1\` by \`3^H\` would require
\[
2^{r+4860k+s}+b-d\equiv0\pmod {d3^H},
\]
which the checked full modulus period excludes. For \`h<H\`, the special equation (S) is excluded by the verified power gap. To see why the finite check is universal in \`a\`, set \`A=3D\` and \`2^(e-1)<A<2^e\`. Its left side is \`A*2^a+D*a+A-C\`. The checked strict bound at the minimum allowed exponent \`n0\` and exponential growth show that it is below \`2^n\` for \`a<=n-e\`. For \`a>=n-e+1\`, the strict lower bound \`A>2^(e-1)\` and the verified \`D*(n0-e+4)>=C\` put it above \`2^n\`. Hence no exceptional source for any \`a\` and \`k\`.

For generic \`a>=A_h\`, the checked initial inequalities imply inductively that
\[
1<Q(a)=D(2a-1)-2C<2^a,\qquad Q(a)\ {\rm odd}.
\]
Equation (G) requires \`2^N≡Q(a) mod (2^(a+1)+1)\`. But reducing \`N\` modulo \`a+1\` gives \`2^N≡±2^t\` for \`0<=t<=a\`; neither sign can equal such an odd \`Q(a)\`. All high-\`a\` generic parents are impossible.

Finally, for the finitely many \`0<=h<H\` and \`1<=a<A_h\`, (G)'s two modular conditions depend on \`k\` only modulo
\[
\frac{\operatorname{lcm}(\operatorname{ord}_{D}(2),\operatorname{ord}_{T}(2))}
{\gcd(4860,\operatorname{lcm}(\operatorname{ord}_{D}(2),\operatorname{ord}_{T}(2)))}.
\]
Checking that complete period is a rigorous all-\`k\` congruence certificate. The script uses the existing [uniform_138.py](uniform_138.py) exact inequality and order checker, and [exact_inverse.py](exact_inverse.py) for an independent finite literal-preimage regression. Every surviving small pair has period **one** and yields exactly the child formula in the table. The displayed generic equation proves the child's actual edge for all k: the period gives integral odd \`v\`, the base case has \`v>=5\`, and \`v(k)\` grows with k. Likewise all rational nodes are integral for all k, since the relevant denominator orders \`ord_15(2)=4\`, \`ord_81(2)=54\`, \`ord_1485(2)=180\`, \`ord_135(2)=36\` divide 4860. The exhaustive child lists terminate at nodes with **no** incoming edges. Induction backwards through this finite directed acyclic diagram proves the basin assertion.

| r | Nodes | Generic low-(h,a) pairs | Complete k-period representatives | Maximum order encountered |
| --- | ---: | ---: | ---: | ---: |
| 138 | 3 | 73 | 240 | 6318 |
| 1218 | 3 | 61 | 185 | 4212 |
| 402 | 3 | 59 | 249 | 53460 |
| 1738 | 3 | 51 | 194 | 14580 |

The complete node parameters are declared in [exact_cones.py](exact_cones.py), which runs the full universal modular/inequality checks and independently evaluates literal E-preimage sets for k=0 and k=1. The direct sample checks are **sanity checks**, while the complete period enumeration plus analytic all-\`a\` and all-\`h\` arguments establish the infinite-family claim. Rerun \`python exact_cones.py\` from this directory using Python 3.10+; it uses only the standard library and two scripts already in the repository.

## Verification and research significance

This is a reproducible **paper-and-arithmetic all-exponent proof** relying on the published/source-matched Sheep E semantics. The r=138 blank nonreachability was separately checked by Agent 14 in Lean 4.36.0-rc2, standard axioms; Agent 40 locally checked genuine two-parent source existence and has an interface-only compilation of global no-grandparent proof texts. The three other exact-basin families here **have not yet been kernel-integrated**. No current CI run checks this combined theorem. Existing root-exclusion certificates [uniform_402.py](uniform_402.py) and [uniform_additional.py](uniform_additional.py) are reused rather than claimed as independent discoveries.

The next useful step is to parameterize Agent40's all-source no-incoming Lean proof over a symbolic target node, then instantiate these three additional classes with short finite modular certificates and import the authentic original Sheep source. The more consequential unsolved problem remains a uniform obstruction for **every** possible power-of-two gate along the genuine blank orbit.


## Comparison with existing full-period Sheep exclusions

The independent [Agent17](../agent17-sheep-third-generation/symbolic_sieve.py)/[Agent16](../agent16-sheep-deep-sieve/README.md) ordinary-section F depth-five certificate excludes exactly 3,596 residue classes modulo 5,400 (published SHA256 `dc77776f9a51938d6c6e1fdb57be681477dae9b93d54fa351d4d4f9ae4b6555b`). I independently reconstructed that exact F inversion algorithm and recovered **all 3,596 entries and the identical SHA256**, rather than assuming their published count.

Each of the four `r+4860*k` progressions projects to ten residue classes modulo 5,400, since `gcd(4860,5400)=540`. **None of these projected classes lies among the 3,596 previously F-depth-five-excluded classes.** In particular, the exact E inverse-cone mechanism is mathematically distinct from that five-generation *unaccelerated* F certificate; the 40 E-certified classes modulo `lcm(4860,5400)=48600` are disjoint from its lift. The combined proven exclusions therefore have exact arithmetic density
[
rac{3596}{5400}+rac4{4860}
=rac{8101}{12150}approx0.6667489712.
]
A standalone reproducible [prior_overlap.py](prior_overlap.py) imports Agent17's unchanged `symbolic_sieve.py`, checks the original count and SHA256, asserts all disjointness claims, and computes 32,404 excluded indices in the 48,600 common-period representative set. It needs SymPy in addition to the standard library.

**Provenance caveat:** the r=138,402,1218,1738 *blank-root exclusion classes* were already established by Agent14's earlier `uniform_138.py`, `uniform_402.py`, and `uniform_additional.py` prior to this note. The newly analyzed mathematical strengthening here is their **complete three-state E predecessor-basin classification**, with constructive actual E parent edges. The reported density improvement is **relative to the older F depth-five certificate**, rather than a previously unknown increment to this repository's combined Sheep record. These numbers do not imply a random-halting probability, a Sheep nonhalting proof, or a new universal Busy Beaver bound.
