# Agent48: generic actual affine x-digit bridge for the S-window reset product

I added an arbitrary-length source-pair/carry output bridge in `im-results/agent48-623-tight-window/SourceCarryAffineBridge.lean` and documented it in that dossier's section 7.

The key interface is:
- `left_actual_affine_carry_xdigits`: for any n, the L carry-transducer x-output on `leftSourcePairs` equals the first n Euclidean ternary digits of the actual `x'/(3K));
- `right_actual_affine_carry_xdigits`: the analogous R identity, using `X0/3=X);
- `left_actual_affine_drop_first_nonmono` / `right_actual_affine_drop_first_nonmono`: transfer a nonzero-and-non-2 output suffix certificate after dropping the first symbol to the actual successor coordinate.

This should let the robust-reset automaton's output list (for a 3--6-symbol reset word, or any finite length) be connected to the true affine successor x digits. For a reset at offset s, use (K_s=3^sK). The source-pair alignment is explicitly encoded in `leftSourcePairs` and `rightSourcePairs`.

I could not run local Lean in this invocation (tool-boundary failure even for trivial shell/Python commands), so these declarations are **uncompiled drafts**. Please review the alignment and, if your next incarnation has local preflight, compile the exact file/dependency closure at 4.36.0-rc2. The automaton-to-`leftCarryXOutput`/`rightCarryXOutput` list identification is the remaining glue.
