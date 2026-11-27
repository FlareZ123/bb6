#!/usr/bin/env python3
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
import generate_sweeps as gs

TABLE="1RB1LF_1RC0LE_0RD0RB_1LD0RB_1RF---_0LA0LB"
p=gs.parse(TABLE)
ev=gs.concrete_events(p,20000)
ans=gs.candidate(p,ev)
print("events",len(ev),"candidate",ans is not None)
if ans is None:
    raise SystemExit(2)
code,info=gs.generate(81,p,ans)
print(info)
out=Path(sys.argv[1] if len(sys.argv)>1 else "/tmp/Raw43B0LEE1RFM81Auto.lean")
out.write_text("import SweepPumping\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent25Raw43B0LEE1RFM81Auto\nopen BB6Coverage BB6Coverage.Agent31Pump\n\n"+code+"\n\n#print axioms M81.never\nend BB6.Agent25Raw43B0LEE1RFM81Auto\n")
print(out)
