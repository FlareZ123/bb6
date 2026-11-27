# Safe positive-tail epochs for #172

New paper lemma, independent of the earlier signed-potential inequality. It does not prove the global birth guard.

Write the particle phases as digits D=0, L=1, H=2, with the least significant particle first. A positive-tail epoch starts immediately after the all-H wrap with boundary 0, all m>=1 digits D, leading gap 1, safe internal gaps, first following gap G >= 3^(m-1), and last following gap T>=2. For m=1 the first and last following gap coincide.

**Claim.** This epoch reaches an all-H state, then performs a positive-tail birth and the subsequent wrap, without deleting the first particle or encountering a drain. The new first gap is at least 3^(m'-1)+1 where m' is the new number of particles, the new birth has charge 1, safety is preserved, and the new trailing gap is at least T-2. Hence from this start at least floor(T/2) consecutive births and wraps are certified safe, without visiting each accelerated event. Pair deletions may replenish the tail and extend the block.

Proof. Until the first boundary action, the only possible nonordinary steps are pair deletions: the signed safety invariant of Potential.lean supplies the allowed L,L pair at an exhausted internal gap. Let V be the base-3 digit value, N the current number of particles, and D=3^N-1-V. Each ordinary step decreases D by 1. For a deletion at index j, put p=3^j and let X=3^(N-j-2)-V_suffix >=1. Before deletion, D=9pX-5p, after deletion D=pX-1. The drop is 8pX-5p+1>=1. Therefore before any boundary action at most 3^m-1 nonboundary steps are possible. This argument does not assume no pair deletion.

Before any first-particle deletion, that particle cycles D,L,H,D on each nonboundary step, and its gap decreases only on L->H, by 1; a suffix deletion at index 1 can increase that gap. A first-particle deletion would require at least 3G+2 steps from all D, larger than 3^m-1. It cannot happen. In particular at least one particle survives.

Consider the current last particle. An L->H transition of the last particle can occur only when all earlier particles have been H, then reset to D. Once H, the last particle cannot be deleted (pair deletion needs L,L) or reset until a boundary action. Thus before the boundary there is at most one L->H of a last particle, even if several previous last particles have been deleted as L. A deletion of the last pair replaces the trailing gap by the old trailing gap plus the gap preceding that pair plus 1. Consequently the tail can fall by at most 1 before the boundary; since T>=2 there is no drain, and the boundary action must be the positive-tail birth at all H. It decreases the tail by a further 1, and the wrap does not change it.

The surviving first digit cycles mod 3, and the leading gap grows by exactly 1 per nonboundary step. Starting with lead 1 and digit D, the lead minus digit is 1 mod 3. At all H the lead is divisible by 3. The new front gap (lead+1) therefore has charge 1 between the new H and the old first H. All other gaps retain safety by the carry and birth-tail theorems.

For the size of the new first gap: from initial V=0, ordinary transitions increase V by 1; pair deletion at index j changes V from 5p-1+9pV_suffix to pV_suffix, a decrease. If r particles survive to the all-H boundary, the final V is 3^r-1. Thus the number of nonboundary steps is at least 3^r-1. Starting lead 1, the new front gap is at least 3^r+1. The new particle count is m'=r+1. The next wrap changes all phases H->D and lead 0->1, preserving the new front gap and safe gaps, so all hypotheses except the tail lower bound are propagated.

Induction gives the claimed block length. The proof uses the particle rules as stated in README.md and the safety lemmas in Potential.lean. A proof of every exceptional boundary episode, or a stronger invariant excluding them, is still required. The lemma neither asserts a positive tail forever nor relies on a finite simulation for its conclusion.

## Failed stronger inequalities

An attempted global strengthening requiring the new birth gap to dominate the signed potential at *every* birth is false even for charge-1 births. For example at birth event 23 (high-level pre-time 114), m=2, phases HH and gaps [9,25,31], the new front gap is 10, but 3*10+25 < 96, the signed potential of the suffix after the first old particle. This is not a bad birth. A JS exact-integer port of the existing event simulator reproduced the known single exceptional charge through 125000 events; no independent nonhalting claim follows. Front deletions at events 462 and 463 also refute immediate unconditional lead domination of the surviving suffix; their successive residues compensate. The correct missing proof must distinguish exceptional residues, not require domination for all births.

## Formal interface

ParticleWord.lean and ParticleSource.lean are new draft proof scripts, not yet kernel-accepted. They link the full projected carry and birth-tail relation to the original word scan and state precisely the remaining BirthGuard hypothesis. Source verification is pending; the prior accepted Potential.lean is unchanged.
