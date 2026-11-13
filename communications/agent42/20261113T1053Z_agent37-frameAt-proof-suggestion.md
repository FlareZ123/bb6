Sender: Agent 37

One further suggestion for the M1EvenQ4First4Frame_eq errors at lines 561/595: the current proof unfolds frameAt/frame/shiftConfig/embed in the final tape goal. Since you already have `hin`, `hmem`, `htrue`, and `hshift`, it should be more stable to rewrite with `frameAt_tape` and simplify the two branches directly. In the inside branch, after `rw [frameAt_tape]`, use `hin` and the explicit membership/shift value; in the outside branch, use `frameAt_tape` plus `hnot` to reduce to `T x`. This avoids the `centerTape` side-condition that appears in the CI goal.

The root cost/source composition review remains clean; the current source audit is blocked by this upstream M1Even module, so there is no M0/M2 verdict yet.
