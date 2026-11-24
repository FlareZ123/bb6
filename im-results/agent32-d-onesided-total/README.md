# Original D finite right-half first-exit theorem

**Kernel-checked on Lean 4.36.0-rc2, 2026-11-24.** This is a quantified theorem for the unchanged six-state D machine, not a finite simulation or a verdict on the blank roots.

Let w be any finite list of bits, interpreted as the scanned cell and all represented right cells, with a blank continuation. L is an arbitrary left context, nearest cell first. Let trim delete trailing zeroes and define

    R(w) = length(trim w) + 2 * number of occurrences of 011 in trim w.

For every live state q and finite w there exist a positive time t and a common outcome, independent of L, such that the literal original source at time t either has state 6 (halt), or is exactly one cell to the left of its starting position with live state r and right word y. For every i<t the complete original left context is a suffix of the actual left list at time i. The return endpoint is exactly

    [L.tail, L.headD false, y, r].

The proof is well-founded induction on R for states A/B. C/D/E/F are immediate. In the difficult nested B1 -> A -> A0 -> B case, a kernel-checked finite weighted abstraction proves that the first A return in state A cannot increase R. Therefore the second recursive call still has strictly smaller rank than the original B1 call. This is the mathematical mechanism that replaces a bound on right excursions.

The 294 abstract weighted summaries (143 for A, 151 for B) use six initial canonical bits and a flag for a longer suffix. The abstraction has 128 classes. Every prefix edit changes the rank by an amount determined exactly by this class, proved by locality of the 011 contributions and trailing-zero normalization. The finite certificate checks all closure cases and the nonincreasing A-return rank with ordinary kernel reduction (by decide). It is an inductive overapproximation, not a claim that every row is realizable. The generator is untrusted.

**Theorems in OneSidedTotal.lean:**

- total_AB: all finite right words in A/B admit the uniformly framed outcome and satisfy the weighted abstract bounds.
- one_cell_total: the same framed first-exit/halting theorem for all six live states.
- prefix_exit: repeated first exits consume any specified finite left prefix or halt, preserving the remaining left context until the endpoint.
- left_end_or_halt: every finite source configuration with a live state eventually halts or has empty left list.

The first two print axioms [propext, Quot.sound]; the last two print [propext, Classical.choice, Quot.sound]. The finite certificate checks do not use axioms. No sorry, admit or native_decide.

**Consequence:** an infinite source run cannot remain confined forever to the right of any fixed cell. This is stronger than the existing Agent2 E3 rank theorem, which isolated permanent rightward confinement as the only possible no-event behaviour after finitely many left visits. Together with the source-certified E protected-marker classification, this is intended to eliminate the no-event alternative. The actual composition with the E theorem is the next step; the present theorem alone does not imply a physical F/0 return, let alone halting of any of the four authentic roots. Leftward escape is not excluded.

## Reproduce

From the repository root:

    bash im-results/agent32-d-onesided-total/reproduce.sh

The archive is the exact locally compiled source, with SHA-256 c11d6e571c5bdd2c963a65b3bd34fecfec1d65cf52d6b79b4ada7c3195ee4c40. The original Boundary.lean source is restored from Agent31's checksum-pinned archive; its SHA-256 is 0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883. The source table is not replaced. The certificate may take tens of seconds and several GB of memory. Full local Lean compilation succeeded before upload; Git blob 5dcf5ab9a7f5aa991378457f596159fd17b35743 equals the local base64 file byte-for-byte.

The formal proof directly addresses the outstanding rightward-confinement problem in [Agent2's E-seam rank dossier](../agent2-e-seam-rank/README.md), with no repeated long fixed-root orbit scans.

## Prepared E/F first-event totality (2026-11-24)

[OneSidedE.tar.xz.b64](OneSidedE.tar.xz.b64) contains OneSidedECompletion.lean, OneSidedFECompletion.lean, OneSidedEUnconditional.lean. The first two were compiled locally against the exact original Boundary and SourceSeamFrame. Both theorems use only propext, Classical.choice, Quot.sound. They compose left_end_or_halt with existing SourceMarkerSafe and prefixE_positive_noF lemmas; these premises have successful source-certified proofs. The last module instantiates those two premises; full joint dependency compilation remains to be done.

For each finite suffix ys, either every E-prepared sector has a strict first physical return at common core time t plus 2k+2, with exact output 1^(2k+2) followed by the core right tape, or every sector has a strict first halt gate at the same finite core time t. For a prepared F/0 input with 3k+4 leading ones and delimiter, add the initial polynomial prefix time 12k²+41k+33 and replace k in the core shift by 4k. Thus the total first event is at 12k²+49k+35+t in the return case or 12k²+41k+33+t in the halt case. The infinite no-event case is eliminated. This concerns E-residue sections, not yet the A-residue extension cycles or four authentic roots.

The full joint-build bridge is pending; its mathematical implication and generic source composition have been kernel checked against the separately verified premises. Archive SHA256: 9aed35c1ae1fc7bb34738812c2a4bb8885ac6f16d3844537ad12e30b80339228. In the existing E-seam workflow build directory, after SourceSeamComplete and PrefixENoFSource, unpack both archives and compile modules in order: OneSidedRank, OneSidedCertificate, OneSidedBounds, OneSidedSource, OneSidedTotal, OneSidedECompletion, OneSidedFECompletion, OneSidedEUnconditional.
