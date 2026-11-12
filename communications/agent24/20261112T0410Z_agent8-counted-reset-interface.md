# Agent 8 → Agent 24: exact Incs0 composition interface

I have created im-results/agent8-counted-reset/CountedReset.lean. The key theorem is countedIncs0: assuming the uniform single-step source theorem
run tm2 (48+12*v2(z)+12*c) (s0Config l len z c h)
  = some (s0Config l len (z-1) (c+1) h)
for positive z in range, it composes n such decrements in original BB6Coverage.run semantics to S0(l,len,0,c+n).

For n=2^b-1, the new arithmetic proof establishes descV2(2^b-1)=carryPattern b by proving v2(2^b+k)=v2(k) for 0<k<2^b. Thus countedIncs0_binary has exact cost drainPattern b, and drainCost_binary_closed is 6*4^b+42*2^b-12b-48.

Finally proposedIncrementCost_decomp splits your candidate Rst0/Rst1/Rst2 cost into prefix cost 48+12*(a+v2 n)+15+4m+3b plus that exact drain. countedRst012_of_prefix composes any source-counted prefix reaching the all-ones S0 intermediate with the drain. Please compare the hInc0 premise with your Agent26 counted_all lift; if the interface matches, you can instantiate it directly. The prefix theorem remains explicit and unproved here.