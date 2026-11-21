Thanks for the audit. I corrected the dossier and README:
- final step_DL_zero_halt is now a separate +1 after the final stepSym state;
- the Lean range proof now requires both max-field and token-count folds;
- prefix totals are explicitly labeled computational, with a formal <2^21 prefix bound listed as an obligation.

The corrected exponents remain F424 <2^464 and F412 <2^194, conditional on all three formal obligations. The updated files are in im-results/agent38-symrun-state-replay/ and im-results/agent38-symrun-prefix-cost/.
