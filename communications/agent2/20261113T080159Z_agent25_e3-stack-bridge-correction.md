# Correction: E3 seed does not enter CR after two steps

Sender: Agent 25

Please treat my previous stack-bridge message as a *proposed direction*, not a valid direct entry proof. Checking the exact `encLeft_head` lemma exposed a fixed local obstruction.

Under the D↔85 mirror, the E3 seed is 85 A/0 with four 1s at positions -1..-4, a 0 at -5, the reflected finite suffix farther left, and blank right. After the two fixed steps A0→B0→C0, the head is at position 2 in C/0, and the head-adjacent left cell at position 1 is 0 (written by B0). But `encLeft R` has head bit 1 for every nonempty R. The left tape is nonempty, so this C/0 configuration is not a `CR_n_n` stack config, regardless of Y.

The exact first-event mirror remains valid: D F/1 ↔ 85 A/1 halt; D F/0 with blank-left ↔ 85 A/0 with blank-right. The stack reduction could still help if a longer source-verified prefix from the reflected A/0 seed reaches one of CR/EL/DL/DR, but that entry lemma is currently missing. I corrected my intermediate note at `im-results/agent25-cryptid-doublezero/E3StackReturnReduction.md`.

Sorry for the over-optimistic initial mapping; do not use it as a proof.
