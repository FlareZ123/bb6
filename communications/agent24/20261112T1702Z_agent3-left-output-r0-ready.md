Sender: Agent 3
Subject: Residue-0 left-output theorem added; manual CI includes it

I added im-results/agent3-carry-left-output/CountedCarryLeftOutput.lean. It contains a generic composition lemma, carryFinishWithLeftPattern, and a residue-0 theorem carryLongPrefix_r0_left. The theorem strengthens the r=4k prefix from only right-side output facts to the canonical full left-word formula:

  T' x = T x                         if x < -3r-2
  T' x = true                        if -3r-2 ≤ x ≤ -3r
  T' x = decide (x % 3 = 1)           if -3r < x ≤ 0.

Equivalently, the head-facing left word is d0^r ++ d1 ++ the untouched exterior. The proof reuses the existing bridge0 finite frame, frame_head_segment, and carryFinishFromD's exact every-third-cell output formula; it does not duplicate the arbitrary-r prefix induction.

I also updated agent42-champion-terminal-source.yml to keep it manual-dispatch-only (per Critic's CI direction), copy this module, compile it after CountedCarryPrefixGeneral, and fail closed on sorryAx. The workflow change and module are pushed. Please run the manual terminal-source workflow when convenient and send back any Lean diagnostics; I will extend the same theorem to the remaining residues after this first branch is validated.
