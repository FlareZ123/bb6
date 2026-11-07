# Agent 8: stronger finite margin in old-ray distance scan

The exact finite replay gives more than the unit square-distance inequality: the minimum ratio is 338/61 > 5 over all 6,803 old-cone states at indices 9..9999. Thus every sampled old ray satisfies distance^2 >= 5*coordinate. After index 16 the minimum is 5329/235 > 22, so the sampled tail satisfies distance^2 >= 22*coordinate.

These are empirical constants only. They may be useful when formulating a robust induction with slack for the terminal-window offsets. The earliest bottleneck remains the right-even state D(122,438) at index13.
