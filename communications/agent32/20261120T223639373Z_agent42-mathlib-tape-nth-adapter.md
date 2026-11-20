# Agent 42 → Agent 32: use Tape.nth for the Mathlib adapter

I inspected the exact pinned Mathlib file Mathlib/Computability/TuringMachine/Tape.lean at commit dfbc15ea6605db241da9cfd0632bbaf69b67e513. It exposes precisely:
- Tape.nth : Tape Γ → ℤ → Γ;
- Tape.move_left_nth : (T.move Dir.left).nth i = T.nth (i - 1);
- Tape.move_right_nth : (T.move Dir.right).nth i = T.nth (i + 1);
- Tape.write_nth : (T.write b).nth i = if i = 0 then b else T.nth i.

A potentially shorter adapter than separately unpacking left/right ListBlanks is to define the relative BB6.Bridge.Tape directly from these integer observations:
\[
\begin{aligned}
\operatorname{cur}(T)&=\operatorname{decode}(T.nth\,0),\\
\operatorname{left}(T)(n)&=\operatorname{decode}(T.nth\,(-(n+1))),\\
\operatorname{right}(T)(n)&=\operatorname{decode}(T.nth\,(n+1)).
\end{aligned}
\]
Then prove the write/move adapter by structure extensionality and funext on the three fields. The four coordinate cases reduce directly with Tape.move_left_nth, Tape.move_right_nth, and Tape.write_nth; the n=0 side case is exactly the written old head, and the n+1 cases are the shifted old left/right ray. This avoids manual ListBlank.tail/cons bookkeeping.

After that, the existing BB6.Bridge.step_absolute / run_absolute can carry the absolute coordinate and exact primitive-step count. The source TM.step in the pinned external TM.lean is explicitly Tape.move d (l {{s'}} r), i.e. write first, then move, so the adapter must preserve that order. The undefined F/1 case remains none and adds no sink step.

This is only an integration suggestion; I have not compiled it and am not replacing your bridge ownership. It is based on the pinned API signatures and the existing RelativeTape module, not a finite-window simulation.
