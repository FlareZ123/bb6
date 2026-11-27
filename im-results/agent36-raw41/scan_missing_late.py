#!/usr/bin/env python3
"""Screen exactly the previously-unsolved one-hole leaves for late first holes.

Machine simulation is evidence, not a proof. A positive exact first-hole time
must be inserted into an original-source Lean audit for acceptance.
"""
from __future__ import annotations
import argparse
import json
import subprocess
from pathlib import Path

def main():
    pa=argparse.ArgumentParser()
    pa.add_argument("--batch",type=Path,required=True)
    pa.add_argument("--simulator",type=Path,required=True)
    pa.add_argument("--limit",type=int,default=2000000)
    pa.add_argument("--out",type=Path,required=True)
    args=pa.parse_args()
    batch=json.loads(args.batch.read_text())
    lines=[]
    for row in batch["rows"]:
        for m in row["missing"]:
            assert len(m["table"].replace("_",""))==36
            lines.append(f'{row["canonical_index"]} {m["leaf"]} {m["table"]}')
    inp="\n".join(lines)+"\n"
    r=subprocess.run([str(args.simulator.resolve()),str(args.limit)],
        input=inp,text=True,capture_output=True,check=True)
    out=[]
    for line in r.stdout.splitlines():
        idx,leaf,status,step,slot,table=line.split()
        out.append({"canonical_index":int(idx),"leaf":int(leaf),"status":status,
          "first_hole_time_or_limit":int(step),"hole_slot_or_current_slot":int(slot),
          "table":table})
        if status=="LATE":
            print(f"*** LATE FIRST HOLE child {idx} leaf {leaf}: {step} slot {slot} {table}",
                  flush=True)
    assert len(out)==len(lines),(len(out),len(lines))
    result={"method":"exact C++ blank prefix simulator; discovery only",
       "proof_status":"not a Lean theorem","limit":args.limit,
       "studied":len(out),"late_count":sum(x["status"]=="LATE" for x in out),
       "rows":out}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2)+"\n")
    print("SUMMARY",json.dumps({"shard":batch["shard"],"studied":len(out),
            "late_count":result["late_count"]}),flush=True)

if __name__=="__main__":
    main()
