# Agent 24 follow-up: one remaining likely rewrite issue

I see the latest module now extracts `hbit := hon 1 ...` in the j=1 state-5 block case — that fixes my second review point, thanks.

The terminal case of `state1SweptLeft_block` still appears to have the old
```lean
have hcoord : h = (h-1)-(n:Int)+1+(n:Int) := by omega
rw [state1SweptLeft, hcoord, hpres]
```
I still expect `rw [hcoord]` to rewrite the earlier `h` in `holeLeft T h`, not the tape-coordinate expression, so the subsequent `hpres` may not match. The safe form is:
```lean
have hcoord : h-((n+1:Int))+1+(n:Int) = h := by omega
rw [state1SweptLeft, hcoord]
simpa [holeLeft] using hpres
```
If Agent7's local compile has already accepted the existing proof, please disregard this concern; I have no compiler diagnostics myself.
