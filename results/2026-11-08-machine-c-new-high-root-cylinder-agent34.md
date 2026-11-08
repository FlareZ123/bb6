# A source-exact, all-time forbidden Machine C high-stopping cylinder

**Agent 34, 8 November 2026.** A new infinite high-stopping parameter cylinder, subsequently generalized to sixteen disjoint residue cylinders, is impossible on the genuine blank-origin Machine C section orbit. This is an all-time theorem and requires no finite run-time cutoff. The proof is an exact two-inverse-edge obstruction in the original source section, rather than a modular quotient that might admit spurious states.

**Verified original-source theorem.** The entire high-stopping cylinder exclusion was independently compiled against the original, unchanged \`secNext\`, \`section_preimage_all_iff\` and \`section_odd_image\` sources using **Lean 4.36.0-rc2** in [successful manual CI run 42528050049](https://github.com/FlareZ123/bb6/actions/runs/42528050049). The resulting kernel audit of \`source_parent_residue\`, \`no_two_edges\`, \`all_source_no_two\` and \`high_stop_blank_unreachable\` reports only \`[propext, Classical.choice, Quot.sound]\`; no \`sorryAx\` or external reachability assumptions. The standalone arithmetic module was also compiled locally with the exact original source predecessor grammar. This is a source-connected authentic blank-section nonreachability theorem. It does not independently resolve the whole Machine C halting problem or BB(6).


## Strongest source-certified theorem (8 November, second verification)

The earlier rectangle \(\mathcal R\) below has been **strictly generalized**. The source-connected Lean theorem
[\`BB6.Agent34Broad.high_stop_blank_unreachable\`](../im-results/agent34-c-degree-profile/ConeBroadSource.lean) proves, for every \(j,m,k,t\in\mathbb N\),
\[
\boxed{\qquad
m\bmod4=1,\quad (j+14)\bmod64=(3m)\bmod64,\quad
k+j+3m+5=2^{2m+2}(j+3)
\quad\Longrightarrow\quad
\mathrm{run}\ F\ t\ (\mathrm{some}(5,1))
\ne\mathrm{some}(2j+3,k).\qquad}
\]

This was verified against the **original, unchanged section source** in
[successful Lean 4.36.0-rc2 CI 42528787943](https://github.com/FlareZ123/bb6/actions/runs/42528787943). The kernel audit of all four source-connected theorems reports only \`[propext, Classical.choice, Quot.sound]\`, without \`sorryAx\` or source reachability assumptions. The source-connected proof is [\`ConeBroadSource.lean\`](../im-results/agent34-c-degree-profile/ConeBroadSource.lean), supported by the [exhaustive arithmetic Lean proof](../im-results/agent34-c-degree-profile/ConeBroadArithmetic.lean).

The stronger **all-source** theorem is:
\[
\boxed{\quad (x+y)\bmod64=48,\quad y\bmod8=3
\quad\Longrightarrow\quad
\mathrm{run}\ F\ (n+2)\ (\mathrm{some}(s))\ne\mathrm{some}(x,y)
\quad\text{for every }n,s.\quad}
\]
Every first incoming parent has odd right counter at least five and coordinate sum congruent to one modulo four, and therefore cannot itself be an image. This follows from the full original-source predecessor grammar, covering every exceptional source and arbitrarily deep bounce.

For transparency, let \(S=x+y\equiv48\bmod64\), \(y\equiv3\bmod8\). Both \(S\) and \(x\) are of even and odd parity respectively, and \(\nu_2(S)=4\). The only possible successful high-depth parents use even source \(a\) and depths \(n=0,2\), with
\[
(a_0,k_0)=\left(S/2-2,\ S/4+(y-5)/2\right),\quad
(a_2,k_2)=\left(S/8-2,\ 7S/16+(y-11)/2\right).
\]
The exact source guard and right-counter lower bound are handled in Lean, including boundary \(y=3\). Their residues satisfy
\[
(a_0,k_0)\equiv(2,3)\pmod4,\qquad
(a_2,k_2)\equiv(0,1)\pmod4.
\]
Hence every genuine first parent violates the original-source odd-right image constraint \((a+k)\bmod4\in\{0,3\}\). No second incoming edge can exist.

For the high stopping family \(x=2j+3\) and \(k+j+3m+5=2^{2m+2}(j+3)\), the strengthened conditions force \(m\ge1\), \(j\equiv1\bmod4\), and \(4\mid(j+3)\). Thus \(64\mid2^{2m+2}(j+3)\), even when \(m=1\). It follows that
\[
(x+k)\bmod64=(j-3m-2)\bmod64=48,\quad
k\bmod8=(-j-3m-5)\bmod8=3.
\]
The initial and first blank-origin returns \((5,1)\), \((3,4)\) both avoid the cone, proving all-time exclusion.

**Density of excluded high parameters.** For each of the 16 residue classes \(m\bmod64\) satisfying \(m\bmod4=1\), there is exactly one allowed \(j\bmod64\). Hence the displayed new family comprises **16/4096 = 1/256** of \((j,m)\) pairs in expanding parameter squares. This is a density of excluded genuine high-stopping inputs, not a density of solved Turing machines. It contains the initial \(j\equiv1,\ m\equiv5\bmod64\) class as one of sixteen disjoint parameter rectangles. Smallest new example outside the initial class: \(m=1,j=53\), \(k=835\), target \((109,835)\); its immediate section parents have no ancestors.

**Unresolved:** this theorem still does not decide Machine C halting or BB(6). Complete novelty relative to every separately built prior global sieve, and a full analytic residual exhaustion, remain open. The source certification and all-time exclusion itself are unconditional.

---

## All-source two-step exclusion

Let \(F=\mathrm{BB6.Agent46.secNext}\) be the exact Machine C first-return section function. Define
\[
\mathcal R=\{(x,y)\in\mathbb N^2:x\equiv5\pmod{64},\ y\equiv43\pmod{64}\}.
\]
**Theorem A.** For every \((x,y)\in\mathcal R\), each one-step section parent \((a,k)\), if any, satisfies
\[
k\equiv1\pmod2,\qquad a+k\equiv1\pmod4,\qquad k\ge5.
\]
Therefore \((a,k)\) has no incoming section edge, by the original-source \`section_odd_image\` theorem: every output with odd right coordinate at least five has total sum \(0\) or \(3\) modulo four. Consequently:
\[
\boxed{\ \forall s,n,x,y,\quad (x,y)\in\mathcal R
\ \Longrightarrow\ 
\mathrm{run}\ F\ (n+2)\ (\mathrm{some}\ s)\ne\mathrm{some}(x,y).\ }
\]
The maximum possible incoming section history has length **exactly one**: the depth-zero and depth-two high branches give genuine incoming edges for all \((x,y)\in\mathcal R\).

### Exact source-case proof

For every \((x,y)\in\mathcal R\), \(x+y\equiv48\pmod{64}\), \(x+y+1\) is odd, \(y\) odd and \(y\ge43\). Apply the source-certified *exhaustive iff* \`section_preimage_all_iff\`.

- The input-zero branch has \(x+y=2^n8\), incompatible with \(x+y\equiv48\bmod64\): \(n\le2\) gives sum \(8,16,32\), and \(n\ge3\) makes the sum divisible by 64.
- All input-one high branches and all odd-\(a\) high branches would make the odd quantity \(x+y+1\) a multiple of 2. Their small exceptional outputs, zero-right branches, and direct low branches have incompatible target coordinates or parity.
- Every remaining parent has even \(a\ge2\), high-source guard \(2k>a\), and a depth \(n\) with
  \[
  x+y=2^n\big(2(a-1)+6\big),\qquad
  (2k-a+3)+\big(2(a-1)+6\big)+3n=x+2y.
  \]
  The factor \(2(a-1)+6\) is divisible by 4; \(n\ge3\) would force \(32\mid x+y\), a contradiction. Thus \(n\in\{0,1,2\}\). The three source cost and sum equations combined with the target congruences yield \(k\equiv1\bmod2,\ a+k\equiv1\bmod4,\ k\ge5\). In fact \(n=1\) is also incompatible with \(x+y\equiv48\bmod64\) and \(a\) even, leaving actual depths \(n=0,2\), but this sharpening is not needed.

The standalone compiled Lean source [\`ConeArithmetic.lean\`](../im-results/agent34-c-degree-profile/ConeArithmetic.lean) implements exactly these exhaustive cases over an independently identical definition of \`sectionPreimageAll\` and concludes the three displayed properties, checking \`#print axioms\` against the standard Lean axiom set. The \`SectionAllInverse.lean\` equivalence, compiled against the original section source in [CI 41544188316](https://github.com/FlareZ123/bb6/actions/runs/41544188316), transfers it to real \(F\)-edges. The original-source \`Agent3CImage.lean\` section-odd-image theorem excludes the second predecessor.

## A forbidden genuine stopping family

The true Machine C high-stopping candidates satisfy the source-certified exact halting equation
\[
k+j+3m+5=2^{2m+2}(j+3),\qquad (a,k)=(2j+3,k).
\]
**Theorem B (new infinite high-gate exclusion).** For all natural parameters
\[
\boxed{\ j\equiv1\pmod{64},\qquad m\equiv5\pmod{64},\qquad
 k+j+3m+5=2^{2m+2}(j+3),\ }
\]
and all blank-section times \(t\),
\[
\boxed{\ \mathrm{run}\ F\ t\ (\mathrm{some}(5,1))\ne
\mathrm{some}(2j+3,k).\ }
\]
*Proof.* Every such \(m\ge5\), so \(2^{2m+2}\) is divisible by 64. The exact equation gives
\[
(2j+3)\bmod64=5,\qquad
k\bmod64=-(j+3m+5)\bmod64=43.
\]
By Theorem A, the target cannot appear after two section returns from any source. The authentic blank seed is \((5,1)\), with right coordinate 1. Its authentic first return is \((3,4)\). Neither lies in \(\mathcal R\). Hence no time can reach this stopping cylinder.

For explicit checks, \((j,m)=(1,5)\) gives \(k=16363\) and the real source target \((5,16363)\), whose exactly two immediate original-section predecessors are
\[
(8182,12271),\qquad(2044,15337).
\]
Both have odd right coordinate and coordinate sum congruent to 1 modulo 4, so both are missing from the section image. Arbitrarily large pairs \(j=1+64u,\ m=5+64v\) give distinct, genuine stopping inputs.

## Relation to previous Machine C work

This is stronger than a synthetic precursor-count observation: it unconditionally excludes a family of *actual immediate halting inputs* on the blank orbit. The entire cylinder uses the same all-source, length-two obstruction, whereas the previously published source-verified \`seven_four_no_two\` handles \(x\bmod8=7,\ y\bmod8=4\), with a disjoint \(x\bmod8=5\) class here. The new family also avoids the obvious earlier \`jointHighAllowed\` exclusion \(\{j\text{ odd},\,j+3m+5\equiv0\bmod8\}\): at these parameters the sum is \(5\bmod8\). The smallest parameter \((j,m)=(1,5)\) passes the explicitly listed Agent3 and Agent11 combined congruence predicates, and it avoids the named Agent19/29/20 C70/C23 constant-residue exclusions. **A separately kernel-certified all-prior-sieve admission statement is still needed** before claiming disjointness from every historical filter, including all later predicates.

This theorem is a step toward the Machine C stopping decision. It leaves infinitely many other high/low stopping families and does not settle Machine C's halting status or the value of BB(6).


**Formal verification:** [source-connected original Lean CI 42528050049](https://github.com/FlareZ123/bb6/actions/runs/42528050049) includes the full [ConeSource.lean](../im-results/agent34-c-degree-profile/ConeSource.lean) and its unmodified original dependencies, plus [standalone predecessor arithmetic](../im-results/agent34-c-degree-profile/ConeArithmetic.lean). The successful log records ordinary Lean foundational axioms only for all four named theorems.
