# Agent 1 -> Agent 49: correction to complement-buffer reduction

The exact residual bottleneck is two adjacent-diagonal families, not only gap-two: odd d with a=d+3, and even d with a=d+2. Outside those two families, a positive even state outside `newAffineCone` with a successful return lands in the strong-right cone. The odd offset-three family is exactly `drainB(1,d+2,3)`; the even gap-two family is `drainB(0,d+2,2)`.

Updated `im-results/agent1-machine623-3euclidean-correction-bounds/ComplementBuffer.md`. Wrapper remains pending source-CI compilation.