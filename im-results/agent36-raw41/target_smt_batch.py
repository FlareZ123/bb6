#!/usr/bin/env python3
"""Target the remaining hardest one-hole children of a chosen Raw41 family.

Candidates are SAT witnesses only, never proof; all emitted compact DFAs are
independently reconstructed through Agent47's original FAR constructor, then
must still pass Lean's original source checker.
"""
from __future__ import annotations
import argparse
import json
import subprocess
import sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SMT=ROOT/"im-results/agent7-far/far_smt_compose.py"
VALID=HERE/"check_smt_log.py"

def main():
    pa=argparse.ArgumentParser()
    pa.add_argument("--batch",type=Path,required=True)
    pa.add_argument("--index",type=int,required=True)
    pa.add_argument("--out",type=Path,required=True)
    pa.add_argument("--min-dfa",type=int,default=6)
    pa.add_argument("--max-dfa",type=int,default=8)
    pa.add_argument("--timeout-ms",type=int,default=30000)
    a=pa.parse_args()
    obj=json.loads(a.batch.read_text())
    row=next(x for x in obj["rows"] if x["canonical_index"]==a.index)
    print(f"Raw41 canonical child{a.index}, open {row['opens']}, missing {len(row['missing'])}",
         flush=True)
    a.out.mkdir(parents=True,exist_ok=True)
    roster=a.out/"target.txt"
    roster.write_text("\n".join(x["table"] for x in row["missing"])+"\n")
    records=[]
    for n,leaf in enumerate(row["missing"],start=1):
        args=[sys.executable,str(SMT),str(roster),"--line",str(n),
              "--min-dfa",str(a.min_dfa),"--max-dfa",str(a.max_dfa),
              "--timeout-ms",str(a.timeout_ms)]
        try:
            r=subprocess.run(args,capture_output=True,text=True,timeout=300)
            raw=r.stdout
            stderr=r.stderr[-4000:]
            (a.out/f"smt-{n}.log").write_text(r.stdout+"\n"+r.stderr)
            test=subprocess.run([sys.executable,str(VALID)],input=raw,
                capture_output=True,text=True,check=True)
            found=test.stdout.strip()
            rec={"open_leaf":leaf["leaf"],"table":leaf["table"],
                 "candidate":found,"solver_rc":r.returncode,
                 "stderr_tail":stderr[-1500:]}
            print(f"child{a.index} leaf{leaf['leaf']}: {found}",flush=True)
        except subprocess.TimeoutExpired:
            rec={"open_leaf":leaf["leaf"],"table":leaf["table"],"candidate":None,
                 "status":"timeout"}
            print(f"child{a.index} leaf{leaf['leaf']}: timed out",flush=True)
        records.append(rec)
    result={"source_screen":"CI 46080134973","proof_status":"SMT search only",
      "index":a.index,"original_open_leaves":row["opens"],
      "previous_far":row["far"],"rows":records}
    (a.out/"summary.json").write_text(json.dumps(result,indent=2)+"\n")
    print("SUMMARY",json.dumps({"index":a.index,"previous_far":row["far"],
       "new_valid_far":sum((r.get("candidate") or "").startswith("SOURCE_FAR_VALID") for r in records),
       "original_missing":len(records)}),flush=True)
if __name__=="__main__":
    main()
