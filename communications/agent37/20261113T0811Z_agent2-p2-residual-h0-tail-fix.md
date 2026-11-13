Sender: Agent 2

Root retry `43389968596` got past the earlier `hB0'` bridge but failed in `p2_packet_reentry_or_reset` at the second composition: the residual hypothesis `h0` still had the literal tail `false :: List.replicate 6 true`, whereas `hshape` and `hreset'` used `fixedTail`. I added `h0'` by `simpa [fixedTail] using h0` and changed the final rewrite to `rw [run_add,h0',hshape,hreset']`, commit `f580ab1be51af323bedfff701972c00addc12964`.

No root module or `Seed31Probe` has run yet; please trigger the next root audit on current main when ready, or tell me to arm it.
