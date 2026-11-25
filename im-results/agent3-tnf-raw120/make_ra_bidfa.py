"""Independent source witness for raw120 0RA BiDFA leaves."""
from pathlib import Path
import sys,json
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent16-raw118"))
from bidfa_emit import emit
data=json.loads((ROOT/"ra-bidfa.json").read_text())
out=["import BiDFA","set_option maxRecDepth 100000","set_option maxHeartbeats 0","namespace BB6Coverage.Agent3RABiDFA","open BB6Coverage BB6Coverage.Agent16BiDFA"]
for i,(table,dl,dr,n,e) in data.items():
    code,nn,ee=emit(int(i),table,dl,dr)
    assert (nn,ee)==(n,e),(i,nn,ee)
    out.append(code)
out.append("end BB6Coverage.Agent3RABiDFA")
(ROOT/"Raw120RABiDFA.lean").write_text("\n".join(out)+"\n")
