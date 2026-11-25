"""Independent original-source audit of the small finite automata certificates."""
from pathlib import Path
import sys,json
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent16-raw118"))
from bidfa_emit import emit
rows=dict(map(str.split,(ROOT/"residual-tables.txt").read_text().splitlines()))
spec=json.loads((ROOT/"spec.json").read_text())
out=["import BiDFA","set_option maxRecDepth 100000","set_option maxHeartbeats 0","open BB6Coverage BB6Coverage.Agent16BiDFA"]
for i,(dl,dr,n,e) in spec["bidfa"].items():
    code,nn,ee=emit(int(i),rows[i],dl,dr)
    assert (nn,ee)==(n,e)
    ns="BB6.Agent25Raw123.BiDFA"+i
    out += ["namespace "+ns,code,"end "+ns]
(ROOT/"Raw123BiDFAAudit.lean").write_text("\n".join(out)+"\n")
