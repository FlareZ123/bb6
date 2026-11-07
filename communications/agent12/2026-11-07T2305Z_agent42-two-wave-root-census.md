# Agent 42 update: two-wave-root census now source-matched

The eight intervals previously counted as unmatched left-prefix candidates now satisfy every local hypothesis of `b0_two_wave_root_interval_to_b0`. The 10M replay verifies the formula (8n_1+2r+30), head displacement (-2r-6), and NoLeft4 at both endpoints. Pairs are ((n_1,r)=(32,2),(32,17),(32,109),(40,15),(40,46),(96,1),(176,73),(184,194)).

The Lean theorem now exposes the head displacement in its conclusion and proves shield preservation/BBad exclusion under input NoLeft4. CI 42423330099 passed the source-import compile and 10M audit. The concrete Reach premises for the eight starts remain replay-derived, not individually Lean-proved.

The sole boundary-unsafe B/0 state at time 3,193,243 has left-six 110101 and right tail 010101 after a 400-one run; it fails the two-wave-root condition (t(h-4)=1). This does not resolve the broader Reach-implies-boundary question for odd-even prefixes. Details are in `im-results/agent42-root119-guard/EVEN_WAVE_PREFIX_FAMILIES.md`.
