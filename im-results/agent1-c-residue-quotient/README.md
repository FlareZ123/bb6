# Machine C residue/phase quotient: exact step abstraction and pilot certificates

Agent 1, 2026-11-04. **Intermediate research, no new BB(6) decision.** The investigated source is the nine-branch `BB6CLine.nextC` of `im-results/agent11-c-line/CLine.lean` on the genuine blank-entry triple `(5,0,1)`. The arithmetic proof in this directory currently uses an independently copied transition function; original unchanged-source module linkage remains a separate verification obligation.

## Finite abstraction

For an even modulus `N`, encode states `(a,k,c)` as `(phase,x,y)`, where phases `0,1,2,3` mean exact `c<4` with `x=a%N,y=k%N`, and phase `4` means `c>=4` with `x=(a-c)%N,y=(a+k)%N`. An intentionally nondeterministic finite relation adds all successors permitted by these residues, including branches that may have no concrete predecessor.

The local Lean file `Quotient192.lean` has a **universal** proof `encode_step`: if the complete copied source `nextC s=some t`, then `encode t ∈ succs (encode s)`, for **all natural triples** and without fuel cutoff. It compiled with Lean 4.36.0-rc2. This checks the difficult soundness side of the quotient against copied equations, but does not certify its linkage with the unchanged original repo `BB6CLine.nextC`.

The modulus-8 case has a separately locally compiled complete finite-closure proof `Bits8.finite_closed` using ordinary `decide`, and an orbit-induction proof `Orbit8.source_no_zero_eight`: under the copied source, no blank-reachable `(1,k,0)` has `k%8=0`. `#print axioms` reports only `[propext, Classical.choice, Quot.sound]`. This recovers an **already known** excluded class, in line with Agent 15's original-section parity theorem, and is a software/proof-method cross-check rather than a frontier advance.

## Larger quotient status

The reproducible `make_bits.py` uses ordinary Python exact-integer BFS on the finite overapproximation and atomically emits Lean bitset certificates. For `N=192`, from `(1,5,0)`, it found **71,540** abstract reachable states. Of the 192 residues `k`, 108 states `(phase=0,a=1,k)` were outside this forward set. An independent reverse-ancestor BFS found exactly **36** of the 64 first-family `m%64` residue classes excluded by the abstraction, using `k+3m+4=2^(2m+3)` and `m>=3`. All these are **finite Python computations**: the Lean 192-bit all-states closure `Bits192.finite_closed` did **not** finish kernel reduction within a 120-second local test. **Do not claim the 36 classes as Lean-certified or novel.** One class, `m=11 mod64`, was already independently verified against unchanged original source by Agent 21; many other classes overlap known Machine C barriers. No full Machine C nonhalting statement or BB(6) bound follows.

The explicit 192-state reverse cone of target `(0,1,142)` (corresponding to first-family `m=58 mod64`) has 182 abstract states and misses the start. Its forward nonreachability is thus *algorithmically reproducible* in this overapproximation. It is **not yet a certified unbounded true-orbit theorem**, and existing prior art should be checked before any novelty claim.

## Reproduction

The SHA256-pinned compressed tar source bundle `sources.tar.xz.b64` contains `Quotient.lean`, `Quotient192.lean`, `Bits8.lean`, `Orbit8.lean`, `make_bits.py` and `rev_components.py`. Decode and extract after verifying the decoded tar SHA256 `4605e381d99e74556c3b9b563ae8b7b5c5e49b1a84384e52421f42f131f63717`. Use Lean 4.36.0-rc2 with a search path containing the extracted directory; compile `Quotient.lean`, `Bits8.lean`, and `Orbit8.lean` in that order. Compile `Quotient192.lean` independently. `python make_bits.py 192 Bits192.lean` reproduces the Python-generated quotient certificate.

## Crucial next steps

1. Prove **unchanged source identity** by importing the genuine `CLine.lean`, proving `CQuotient192.nextC=BB6CLine.nextC`, and re-checking the theorem with original imports through manual CI.
2. Replace the unwieldy 71,540-state forward closure with a Lean-verifiable **small reverse-closed bad predicate** for an actually surviving first-family class, perhaps the 182-state `m%64=58` component. Obtain an all-input arithmetic proof (or a small kernel-reduced finite certificate).
3. Compare any new excluded class with all earlier published/internal source-certified first-family barriers. Do not promote purely computational residue counts to `results/`.

All numerical conclusions above are limited to the explicitly defined finite overapproximation; an unverified finite closure cannot substitute for a mathematical theorem.
