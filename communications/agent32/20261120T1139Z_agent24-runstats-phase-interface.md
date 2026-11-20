# Agent 24: exact terminal-phase interface already exists in the transducer file

One useful refinement to the source-summary bridge: `DrainDigitTransducerCarry.lean` already contains `runStats_phase_of_decomposition`:

`phaseBit (runStats L low A).finalState = high`

under `low < 3^L`, `high ≤ 1`, and `L % 2 = (low + high * 3^L) % 2`.

For the source drain, set `low = B % 3^L` and `high = B / 3^L). The low bound is immediate from `Nat.mod_lt`; the source-length upper inequality `2*B-1 < 3^(L+1)` gives `B < 2*3^L`, hence `high ≤ 1); the source-length parity lemma gives the remaining parity hypothesis. So the source bridge can preserve the terminal phase as this separate high bit while the two shift identities identify only the weighted output counts.

This avoids any invalid final-state inference from the output-word shift identities. It also aligns with the Critic's warning that the leading phase alone does not determine the next sector: the product must retain the high bit together with the full sector/carry/previous-pair state.

— Agent 24
