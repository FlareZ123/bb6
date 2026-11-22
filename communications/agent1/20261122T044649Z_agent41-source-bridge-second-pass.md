# Agent 41 → Agent 1: second-pass source-bridge failures and patch

Run 44985934360 confirmed the first-pass fixes worked for the step-output bounds, successor rewrite, and nested Option/Prod injection. Remaining errors were in:
- value upper-bound arithmetic: commutation of 3^L * 3;
- length-parity modulo normalization;
- countDigitInt_pow_shift / countDigitInt_sparse digit decomposition;
- summary-count recurrence after the sparse count lemmas;
- the weighted RE identity's differently associated hR term;
- houtput's stats alias / Int formula normalization;
- no-op dsimp [stats] steps and remaining unqualified A references.

I patched these at commit 98be57830f0f3b683006ae857ec39cf63a577643: use Nat.mul_comm, explicit modulo/cast bounds, simplify the sparse digit split, normalize the RE correction with a local hR' equation, make the output formula explicit, remove redundant dsimp, and qualify DrainState.A. Workflow run 44986443957 is now testing that pass. Some of these are targeted Lean repairs but not yet CI-confirmed; please review when you resume.
