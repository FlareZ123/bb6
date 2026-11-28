#!/usr/bin/env python3
"""Generate two collision-free exact original-source D100 exposure bounds.

This converts the separately accepted F0/B1 original-machine witnesses into
distinct importable Lean modules and builds a joint theorem interface.
No trusted computation: all original run0 source and bound proofs are checked.
"""
import argparse,hashlib,json
from pathlib import Path
from exposure_emit import generate
from emit_exposure_bound import main as make_bound

ROWS=[
 ("F0","1RB1RE_1RC1LF_0RD1RF_0LD0LA_1LA1LE_---0LB",23126,170,
  "520970e8e17cd2a0bcc882d5fe872a602616316884102444c1a45d5981085935"),
 ("B1","1RB1LE_1RC---_0RD1RF_0LD0LA_0LB0LA_1LA1RB",60671,512,
  "b7dd63eefcfab9fa14f933dcf182f97594e7e89e720c276bff1b48b1174fc456")
]

def build(out):
    out.mkdir(parents=True,exist_ok=True)
    mods=[]
    names={}
    for slot,table,n,chunk,expect in ROWS:
        mod="Raw36D100Exposure"+slot
        base=out/(mod+".lean")
        info=generate(table,n,base,chunk)
        assert info["source_sha256"]==expect, (slot,info["source_sha256"])
        bound="Raw36D100Bound"+slot
        ns="BB6.Agent7D100ExposureBound"+slot
        make_bound(base.with_suffix(".json"),out/(bound+".lean"),mod,ns)
        mods.append((mod,bound,info))
        names[slot]=(ns,info["namespace"],n+6)
    s=["import Raw36D100BoundF0","import Raw36D100BoundB1",
       "namespace BB6.Agent7D100TwoBounds",
       "open BB6Coverage"]
    for slot in ("F0","B1"):
        bns,ins,b=names[slot]
        s += [f"theorem bound{slot} (m : Machine) (hm : compatible {ins}.table m) :",
              f"    WeightedBound {b} m := {bns}.bound m hm",
              f"#print axioms bound{slot}"]
    s+=["end BB6.Agent7D100TwoBounds",""]
    src="\n".join(s)
    (out/"Raw36D100TwoBounds.lean").write_text(src)
    report={"leaves":[{"slot":slot,"source":name,"bound_module":bound,
                       "namespace":info["namespace"],"bound":info["undefined_after"]+6,
                       "source_sha256":info["source_sha256"]} for (slot,_,_,_,_), (name,bound,info) in zip(ROWS,mods)],
            "joint_sha256":hashlib.sha256(src.encode()).hexdigest()}
    (out/"joint.json").write_text(json.dumps(report,indent=2)+"\n")
    return report

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--out",type=Path,required=True)
    args=p.parse_args()
    print(json.dumps(build(args.out),sort_keys=True))
