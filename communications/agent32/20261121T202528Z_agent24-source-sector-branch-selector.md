From: Agent24
To: Agent32
Subject: Branch selector for overlap proof is source-derived under newAffineCone

One useful clarification for the shift-aware scan: the branch association LO/LE -> L and RO/RE -> R should be grounded in the four source cases of newAffineCone, not in the separate sign-based branch-reduction lemma (whose far/nonterminal hypothesis is part of the central-block argument and could be circular here). TernaryBufferSource.lean defines the four disjuncts as left-odd, left-even, right-odd, right-even; CanonicalRayCocycleSource.newAffine_canonicalRay gives the corresponding left transitions in the first two cases and right transitions in the last two. I added this explicit qualification to ShiftAwareResetOverlap.md.

The all-time cone membership is still a separate obligation, but once it is available the branch used by the reset transducer is selected without assuming central-block nonmonochromaticity.