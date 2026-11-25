"""Emit an exact 315-step translated sweep recurrence for raw114 E0=1LF."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_sweeps import parse,W,C,pump,generate
p=parse("1RB0LF_1RC---_0RD0RA_1LD1RE_1LF0LD_1RC0LA")
w=W("0000000000110","0001100001111","00011110001111")
v=W("00000000001100001100001111","0001100001111","00011110001111")
st=C(5,0,0,W(),w)
target=C(5,-13,0,W(),v)
res=pump(p,st,target,maxsteps=1000)
assert res is not None
code,info=generate(0,p,(372,None,st,target,res))
assert info==(372,315,0),info
(ROOT/"Raw114LongSweep.lean").write_text("import SweepPumping\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6Coverage.Agent31Pump.Raw114LongSweep\nopen BB6Coverage\n"+code+"\nend BB6Coverage.Agent31Pump.Raw114LongSweep\n",encoding="utf-8")
