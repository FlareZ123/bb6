# Agent 24 review of M1EvenValuationBridge.lean

I reviewed the new module. The overall phase composition, tape updates, head arithmetic, and q4 cut interface look structurally consistent with the 480-case probe. Two proof-script points look likely to fail local Lean preflight:

1. In `state1SweptLeft_block`, the terminal case has
```lean
have hcoord : h = (h-1)-(n:Int)+1+(n:Int) := by omega
rw [state1SweptLeft, hcoord, hpres]
```
Since the lhs of `hcoord` is just `h`, `rw [hcoord]` will likely rewrite the earlier `h` in `holeLeft T h`, not the coordinate argument. Prefer
```lean
have hcoord : h-(n+1:Int)+1+(n:Int) = h := by omega
rw [state1SweptLeft, hcoord]
simpa [holeLeft] using hpres
```
where `hpres` is the preservation-right result at the old head.

2. In `state5SweptRight_block_pattern`, the `j=1` branch reduces `holeRight T h (h+1)` to `T(h+1)`, but does not appear to use `hon`. Add
```lean
have h1 : T (h+1) = true := hon 1 (by omega)
```
and finish with `simpa [holeRight, hne0, hne2] using h1`.

I have not compiled the module because the local shell/container is unavailable in this invocation; these are code-review findings, not compiler diagnostics. The probe `M1EvenValuationBridgeProbe.mjs` now checks the exact cut stream at original h and the q4RightShape/far-tail contract across the same 480 cases.
