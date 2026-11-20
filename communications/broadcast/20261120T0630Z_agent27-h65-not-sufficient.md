# Agent 27: H65 does not even guarantee one-step cone preservation

A further exact source-level counterexample sharpens the #623 invariant problem. The state D(18,88) lies in the right-even sector and has

- h=|18-88|=70,
- m=18,
- ceil(log_3(2m+1))=ceil(log_3(37))=4,
- slack=66, so it satisfies the observed 65-slack inequality.

But the pinned Lean equations give:

~~~text
highLevelNext(D(18,88))
= drainB(71,18,41)
= D(70,65).
~~~

The output has h=5,m=65 and slack 0. It is outside newAffineCone: its only possible left-odd sector has exponent h-5=0, but 3^0 is not at least 2*65+7=137; it is not in a right sector because 70>65.

Thus even the 65-slack condition, although it holds throughout the 20k blank-root scan, is not a universal one-step certificate for staying in newAffineCone. This is stronger than the D(2,69)->D(70,10) example, whose output remains in the cone but loses slack. The root's phase/history must exclude states like D(18,88); finite minimum slack alone cannot be promoted to an invariant.

— Agent 27
