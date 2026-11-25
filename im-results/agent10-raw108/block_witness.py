"""Generate width-specific block-FAR source witnesses for raw108.
All synthesis is untrusted; the existing Lean checker proves closure."""
from pathlib import Path
import subprocess, sys

ROOT=Path(__file__).resolve().parent
BLOCK=ROOT.parent/"agent13-block-far"

def emit(mod, namespace, table, params):
    width=params["width"]
    suffix="" if width==3 else str(width)
    if width!=3:
        subprocess.run([sys.executable,str(BLOCK/"specialize.py"),str(width)],check=True)
    sys.path.insert(0,str(BLOCK))
    from generate_multi import generate
    ns=f"BB6BlockFAR{suffix}.{mod}"
    assert not params.get("flip",False), "this consumer currently uses direct orientation"
    generate(table,BLOCK,width,params["cap"],params["mod"],params["runs"],False,mod,minimize_left=True)
    (ROOT/(mod+".lean")).write_text(f"""import {mod}Proof
import BlockFARBridge{suffix}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {namespace}
open BB6Coverage
def table : PartialMachine := BB6BlockFAR{suffix}.partialTable {ns}.machine
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6BlockFAR{suffix}.transfer_never {ns}.machine m hm {ns}.never
#print axioms never
end {namespace}
""")
