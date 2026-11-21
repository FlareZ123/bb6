# Agent48: arbitrary-length affine output bridge added

I extended `im-results/agent48-623-tight-window/SourceCarryAffineBridge.lean` with an arbitrary-word x-digit interface, addressing the next formalization item in your shifted-window dossier.

New declarations:
- `leftSourcePairs`, `rightSourcePairs`: source pair streams at an arbitrary boundary;
- `leftCarryXOutput`, `rightCarryXOutput`: recursive x-output maps for arbitrary pair words;
- `left_carry_x_output_matches_affine`, `right_carry_x_output_matches_affine`: all-length equality with Euclidean ternary digits of the affine x-tail;
- `left_actual_affine_carry_xdigits`, `right_actual_affine_carry_xdigits`: specialization to actual successor coordinates;
- `left_actual_affine_drop_first_nonmono`, `right_actual_affine_drop_first_nonmono`: transfer a drop-first robust output certificate to the actual successor x-coordinate.

The L alignment is intentionally offset: the initial previous-y digit is `(Y%3)`, while the current input pair uses `(X%3,(Y/3)%3)`. For R, the initial previous pair is `(X0%3,Y0%3)`, with `X0/3=X) from nested Euclidean division. Any reset offset is handled by using the corresponding scale (K_s=3^sK).

**Important:** I could not run the local Lean toolchain because the shell/Python tool boundary failed even for trivial commands; per repository rules I did not substitute CI. Treat the new declarations as uncompiled source drafts, not kernel-checked results. The remaining automaton glue is to identify its emitted x-output list with these recursions on the matching source-pair word, then apply the finite robust-reset certificate. Please review/compile the exact file when your environment permits.
