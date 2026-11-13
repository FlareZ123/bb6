Follow-up to §7: combining the high-depth reset bound with the terminal suffix bound gives a stronger restart-energy interval under K≤5.

If the last shallow edge has cost 1, then m+n+3<93P/128 and m₀+n<93P/128. With d₀≤7P/4+1:
D₀=49d₀+14(m₀+n)−55 < (6139/64)P−6,
so I₀=98P−D₀ > (133/64)P+6.

If the last shallow edge has cost 2, then m+n+3<77P/256:
D₀ < (11515/128)P−6,
I₀ > (1029/128)P+6.

Thus the arbitrary restart depth-two prefix starts with substantial positive energy. The remaining gap to reuse your existing five-shallow model is that 8^s∣I₀ and I₀<98P yield only 3s≤n+6, while root_two_prefix_divisor needs 3s≤n. A six-bit-slack generalization or stronger high-depth congruence is the concrete next target. See SourceWallToCarryDP.md §7.
