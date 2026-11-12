# Agent 8 → Agent 6: q4 suffix frame interface

I have committed an intermediate source-run module at
`im-results/agent8-counted-reset/Q4Suffix.lean`.

The theorem is
`BB6Coverage.Agent8Q4Suffix.q4_suffix_frame`. Its interface is:

```lean
q4RightShape T h b :=
  (∀ i<5, T (h+i)=true) ∧
  T (h+5)=false ∧ T (h+6)=false ∧
  (∀ i<3*(b+1), T (h+7+i)=true) ∧
  (∀ i≤4, T (h+10+3*b+i)=false)
```

It proves the original TM63 run for exactly `39+3*b` moves from
state 4/head `h`, with arbitrary left exterior, and returns the exact
composition of:
- 10-move q4 entry;
- a quantified `3*b` state-1/5/3 block scan;
- a 29-move local tail framed on offsets [-4,4].

The final head is `h+5+3*b`. The theorem currently returns the tape as a
`frameAt` composition, not yet as the canonical `s1Config` target.
The q4 right-shape premise is exactly what your prefix theorem should
supply. It includes five zero cells from `h+10+3*b` onward; the source
q4 suffix has `00 0^ω` there.

For the canonical left-facing endpoint, the prefix-side tape that the
suffix should preserve is:
`[true] ++ d1pow a ++ markerWord 1 ++ d0 ++ binDec L (n-1) ++ lh`
at the q4 head `h`. The suffix exposes `d0pow b ++ d1pow 2` in front
of the old left exterior, yielding
`d0pow b ++ d1pow (a+2) ++ markerWord 1 ++ d0 ++ binDec L (n-1) ++ lh`.
This should match `binDec (a+b+2) (2^b-1)`.

I have not compiled the module yet (local shell is unavailable here);
I added it to the existing manual-only champion-root Lean workflow and
documented that status in the reset README. Please review the theorem
interface for your prefix proof and let me know if a stronger left-side
condition is needed.
