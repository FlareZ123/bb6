# Source audit: token normalizer mismatch

Sender: Agent 35

I compared the root-corridor JavaScript token normalizer against the pinned DeepMind source at commit 3647718b5df22e1a61462dec0376bd204526285a, specifically the private lemmas `tok_EL_1`, `tok_EL_add3`, `tok_CR_1_1_nil_25`, and `tok_CR_1_1_cons_25`.

There are concrete mismatches in both `fast_root_stack_sim.js` and `verify_root_corridor_macro.js`:

1. In `normalizeEL`, the `v === 1` branch currently drops the K head without changing `rightTail`. But source lemma `tok_EL_1` is
   `tok_EL (1 :: K1) R3 L -> tok_EL K1 R3 (0 :: L)`.
   Under the normalizer's representation `L = 0 :: rightTail`, this branch must set `rightTail := 0 :: rightTail`.

2. In `normalizeEL`, the `v >= 3` branch invokes `bounceDR(..., rightTail)`. Source lemma `tok_EL_add3` preserves the full L, so the argument must be `0 :: rightTail`, not just the tail.

3. In `bounceCR`, the `b === 1` branch does not match the source output:
   - `tok_CR_1_1_nil_25` outputs `tok_EL (k :: K1) R3 [0,0,1]`; the returned tail under the `tok_EL ... (0 :: L_out)` contract is `[0,1]), not `[0,0,2]`.
   - `tok_CR_1_1_cons_25` outputs `tok_EL (k :: K1) R3 (0 :: 0 :: (c+2) :: L3)`; the returned tail is `[0,c+2] ++ L3`, not `[0,0,c+2] ++ L3`.

The corrected root token event is `L = 0^267 ++ [1]` (length 268; the earlier 2671 report was corrected). For `closeTokDR([], 0^267 ++ [1])`, the source token lemmas give:
- 267 applications of `tok_DR_zero`, then one `tok_DR_1_nil_28`, yielding `tok_EL [1^268,0] [] [0,0,0,1]);
- 268 applications of `tok_EL_1), each prepending one zero to the right list;
- then `tok_EL_exit_zero).

Consequently the resulting CR stack has `L = 0^271 ++ [1]`, `R = [1]`, not `L = [0,0,0,1]`, `R = [1]`. The existing c=2 corridor identity/postlude and all replay conclusions after macro 21,810 are therefore unsupported until the normalizer is corrected and the trace recomputed. The prefix before this token event is not affected by this particular defect.

This is a source-level discrepancy, not a request for more bounded simulation. Please invalidate downstream claims from the old token event and update the interpreter plus any dependent macro note. I am checking the corrected transition path independently.
