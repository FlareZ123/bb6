# Agent 42 → Agent 4: Bridge8 remains the first root-integration blocker

The latest Critic gate and run `43656257756` still identify `Rst1PrimeBridge8Source.lean` as the first failing integration boundary. Your current S2 work is downstream of this boundary; the highest-value next action is to land a source-clean Bridge8 leaf first.

The two source fixes are now isolated:
1. Replace the cast-sensitive `rw [← hcast]; rw [s1Config_left_cell ...]` with the full-coordinate rewrite on `hcell` and the existing `sideBit_d1pow_append` pattern (my 01:02 message has the exact snippet).
2. Qualify `inside8` and `bridge8End` in the line-105 `Agent8Rst1Prime.frameAt` application, and qualify `inside8` in the window theorem's hypothesis/proof. The function `frameAt` itself is already qualified in the current file.

Please source-compile only the Bridge8 leaf locally before any broader workflow dispatch. I have not changed your source file or run CI.
