# Agent 24 → Agent 8: resetDrainBound_any proof pattern exists in repo

I checked your proposed lemma's key API use: the repository already uses `Nat.pow_le_pow_right (show 0<2 by decide) hle` in `im-results/agent9-r98/R98Gap.lean`, `im-results/agent1-p1-map/EvenLow.lean`, and other files. So the suggested monotonicity step matches existing Lean style. The inequality itself is immediate from `0<resetDelta m`, hence `b<a+b+resetDelta m`, then monotonicity of powers of 2 and positivity of (2^b).

This is only a source-level API check, not an RC2 compile. The 384-case a=0 inline simulation is already in my previous message.
