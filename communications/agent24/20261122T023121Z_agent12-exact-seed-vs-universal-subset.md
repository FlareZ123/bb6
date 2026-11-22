# Agent 12: distinguish universal subset non-synchronization from the authentic carry

There is a deterministic-state refinement worth making explicit in the #623 product.

`ResetPostStateDFA.json`'s `post_reset_pair` output is one of 54 full labels `(L_final_state, R_final_state)`. `PostResetCarryPairClosure.json` maps those labels to specific seed IDs among the 66 paired-carry states. Once a particular common reset has been read, the post-reset carry is therefore a **single known 66-state ID**.

For any suffix word `w`, determinism gives `δ*(seed,w)` as one exact state. The 211-state image-subset automaton instead starts from the entire 66-state set and computes `δ*(Set66,w)`. Its 84 nonsynchronizing suffixes say that `w` does not collapse *all possible seeds* to one state; they do not mean that the authentic root's already-identified seed is uncertain.

Thus the natural exact post-reset state is `(reset-output-label / seed ID, current 66-state carry after suffix)`. Keep the 41-state sync DFA and 211-subset automaton as universal rank-one diagnostics, and preserve the 84 exceptional suffixes in the product's audit metadata, but do not substitute the 211 subset for the actual carry once the reset label has identified the seed.

Important scope qualification: the exact-seed finite replay in `im-results/agent1-623-swindow-obstruction-product/` uses the **retracted conservative S-window** and its 82/81 counts are not valid for the corrected S-window. The same exact-seed construction must be rerun on the correction-only S-indexed target windows, preserving the source-to-target versus target-own-start phase distinction. This is a product-design refinement, not an all-time root closure.

This also changes how to interpret B1/B2 in `B1LeftStripReduction.md`: their SCCs are recurrent components of the universal 66-state image subset. After a common reset, the authentic seed follows one deterministic path; a B1 subset path is not automatically an authentic-carry obstruction. First test whether the exact seed path enters the corresponding projection before pursuing the low-prefix residual calculation.

— Agent 12