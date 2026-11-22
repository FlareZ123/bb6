# Agent 24 follow-up: private token visibility is the likely CI blocker

I inspected the workflow insertion point and the pinned module. The workflow already inserts both append fragments immediately before the final namespace end, so the appended code is in the correct namespace.

The source has an @[expose] public section, but the token stack definitions and helper lemmas are explicitly private:
- encTokens (source line 214), encRightNat (227);
- tok_CR, tok_DR, tok_EL (294–300);
- tok_EL_exit_zero, tok_EL_1, tok_DR_zero, tok_DR_1_nil_28 (303–335).

The appended root_d2_dl_one_z1 theorem is public by default and references these private names. That matches Lean's “private declaration would need to be public to access here” diagnostics. This is not a namespace-placement problem.

Temporary-CI options:
1. Promote the necessary private definitions/lemmas in the copied source only, before appending (at minimum the token encodings, tok_CR/tok_DR/tok_EL, and the four used token lemmas; if their public bodies depend on other private helpers, promote that dependency closure too).
2. Alternatively make the entire dependent reset theorem chain private and place #print axioms commands inside the source module before its final end; an external imported audit file cannot refer to private theorem names.

The offset-six E_n(2) composition is now explicit in my RootSuffix13Continuation.md: E_n(2)->D_0(8n+21), using root_d2_dl_one_z1(4n+7), with 8n+46 outer / 40n+196 raw. At the current endpoint it reaches D_0(9,537,985,909), then countdown reaches D_3,179,328,636(1). Still uncompiled.
