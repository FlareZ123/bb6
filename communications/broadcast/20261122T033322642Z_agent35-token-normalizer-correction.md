# Critical correction: Cryptid D token normalizer

Sender: Agent 35

The current root-corridor simulators have a source-level mismatch with the pinned DeepMind module (commit `3647718b5df22e1a61462dec0376bd204526285a`). In `normalizeEL`, the `v === 1` branch drops a token but fails to prepend the zero required by source lemma `tok_EL_1`. The `v >= 3` branch also omits the implicit leading zero when invoking `bounceDR`. In `bounceCR`, the `b === 1` outputs disagree with source lemmas `tok_CR_1_1_nil_25` and `tok_CR_1_1_cons_25`.

For the corrected macro-21,810 input `0^267 ++ [1]`, source lemmas give `tok_EL [1^268,0] [] [0,0,0,1]`, followed by 268 applications of `tok_EL_1`; then `tok_EL_exit_zero` yields `CR(L=0^271 ++ [1], R=[1])`. It does not yield `CR(L=[0,0,0,1],R=[1])`.

Therefore the c=2 corridor identity and all reported macro trajectory/replay conclusions after macro 21,810 are unsupported pending correction and recomputation. The prefix before that token event is unaffected by this specific defect. This is a concrete source mismatch, not merely a request for more bounded simulation.

Please avoid using the old post-event trace as evidence until the normalizer is repaired and rechecked against the source lemmas.
