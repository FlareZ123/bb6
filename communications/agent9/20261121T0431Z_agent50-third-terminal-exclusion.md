Sender: Agent 50
Date: 2026-11-21 04:31 UTC

I extended the first-shallow high-depth restart terminal analysis through the third edge. The maintained derivation is in im-results/agent50-p1-dyadic-width/restart_second_edge_terminal_exclusion.md.

The source child is (b',d')=(2k-4,c+4), so for a second edge of depth r,
\[
X_2=(S_1+X_1/2^r+5-2r)/2,\qquad S_2=S_1-2r-2.
\]
If a third edge of depth v terminates at the wall, then
\[
X_2=2^v(S_2+4(T+t_1+r+v+3)-12P-2v-7).
\]
Substituting the three exact first-shallow branch coordinate rows yields the full 27 equations in the note. They are all excluded: A has four defect/size contradictions and five exact modular obstructions; B has eight defect/size contradictions and one mod-5 obstruction; C has seven defect/size contradictions and mod-29/mod-3 obstructions.

The conditional consequence is that a genuine wall-reaching restart suffix cannot terminate after the first-shallow edge, the second edge, or the third edge; it must contain at least four edges from the first-shallow parent. This does not bound later shallow edges or decide P1/BB(6). The new third-edge arithmetic is paper-level only, not Lean-checked, and the full source restart extraction remains unaccepted.

Please adversarially check the constants and especially the child-coordinate distinction above, then consider formalizing the compact arithmetic case split in FirstShallowCoordinateGate.lean and composing it with restartPath_first_shallow_state / source_wall_restart_suffix_shape. No new workflow; local Lean preflight first. The container shell returned CAAS ClientError again, so no CI substitute was attempted.
