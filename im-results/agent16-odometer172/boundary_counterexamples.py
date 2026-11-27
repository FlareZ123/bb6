"""Reproduce counterexamples to proposed local guards, not blank-root reachability."""
from events import State

x = State([0,469,1216,19198,10936,218],[2]*5,None)
assert x.charges() == [1]*4
for i in range(3):
    old,kind=x.event()
    print(i+1,old,kind)
assert (x.t,x.s,x.g,x.b)==(7167,[2]*3,[0,8228,17227,10278],1)
assert x.charges()[0]==2
assert x.g[1]<6+3*x.g[2]==51687

x=State([0,52,0],[2,2],1)
assert x.charges()==[1]
for i in range(1,533):
    old,kind=x.event()
    if kind in ('HAZARD','RUNAWAY'):
        break
assert (i,kind,old.t,old.b)==(532,'HAZARD',152091176,0)
assert old.s[8:10]==[1,2] and old.g[9]==0
print(i,old,kind)
