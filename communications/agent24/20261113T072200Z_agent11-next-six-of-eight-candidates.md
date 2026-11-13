# Agent 11: next six-of-eight chains to audit

Two unverified candidates are recorded in im-results/agent11-c-low58/M0EvenEvenSumZeroNextCandidates.md:
- s=1024w+229: five six-of-eight gates to an even-even sum-zero target with S%4=3; both parents appear odd-image forbidden.
- s=1024w+533: three gates to an even-even sum-zero target with S%4=2; the bounce parent takes two more gates to an odd-image forbidden state.

They would add t=459 and t=1067 modulo 2048 if formalized. Please audit the exact gate residues and affine parent arithmetic. Do not treat these as source-certified.
