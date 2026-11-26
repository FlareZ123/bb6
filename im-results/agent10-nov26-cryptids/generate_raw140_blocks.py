"""Generate the exact two-cell BlockFAR certificates for the next Raw140 cut."""
import json,sys
from pathlib import Path
from generate_raw140_deep import parse
DIR=Path(__file__).resolve().parent
sys.path.insert(0,str(DIR.parent/"agent13-block-far"))
from generate_multi import generate

def main():
    rows=json.loads((DIR/"raw140-block-parameters.json").read_text())
    imports=["import ZipThreeHoleAudit","import BlockFARBridge"]
    body=["set_option maxRecDepth 100000","set_option maxHeartbeats 0","namespace BB6.Agent10Raw140Block","open BB6Coverage BB6.Agent31ThreeHole"]
    for i,(table,args) in enumerate(rows):
        width,cap,mod,runs,flip,mode,offset=args
        assert width==2 and offset==0
        name=f"Raw140B{i:02}"
        generate(table,DIR,width=width,cap=cap,mod=mod,runs=runs,flip=flip,name=name,left_mode=mode,minimize_left=True)
        imports.append("import "+name+"Proof")
        codes=[24 if a=="---" else 4*(ord(a[2])-65)+2*int(a[0])+int(a[1]=="R") for a in parse(table)]
        ns="BB6BlockFAR2."+name
        reflected="FAR.reflectPartial p" if flip else "p"
        proof=f"BB6BlockFAR.transfer_never {ns}.machine"
        if flip:
            result=f"""  apply FAR.reflectNever m
  apply {proof} (reflectTable m)
  · rw [table_eq]
    exact FAR.reflectCompatible p m hm
  · exact {ns}.never"""
        else:
            result=f"""  apply {proof} m
  · rwa [table_eq]
  · exact {ns}.never"""
        body.append(f"""
namespace B{i}
def p : PartialMachine := FAR.fromCodes {codes}
theorem table_eq : BB6BlockFAR.partialTable {ns}.machine = {reflected} :=
  tableOK_sound _ _ (by decide)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
{result}
#print axioms never
end B{i}
""")
    (DIR/"Raw140BlockLeaves.lean").write_text("\n".join(imports+body+["end BB6.Agent10Raw140Block",""]))
if __name__=="__main__":main()
