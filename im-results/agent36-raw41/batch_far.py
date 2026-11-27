#!/usr/bin/env python3
"""Profile previously UNSCREENED Raw41 five-hole cylinders by exact FAR discovery.

Consumes one accepted source-enumerator screen JSON, not guessed candidates.
Untrusted FAR discoveries are not mathematical proofs until source Lean check.
"""
from __future__ import annotations
import argparse
import contextlib
import json
import re
import runpy
import subprocess
import tempfile
from pathlib import Path
from close_candidate import ROOT, R47, R19, gather_bank

SKIP={6,17,68,81,84,88,90,123,125,140}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--screen",type=Path,required=True)
    ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--max-open",type=int,default=250)
    ap.add_argument("--dfa",type=int,default=5)
    ap.add_argument("--time",type=int,default=180)
    a=ap.parse_args()
    inp=json.loads(a.screen.read_text())
    assert inp.get("canonical_total")==153
    a.out.parent.mkdir(parents=True,exist_ok=True)
    results=[]
    with tempfile.TemporaryDirectory(prefix="raw41-batch-") as td:
        tmp=Path(td)
        cc=str(tmp/"enum")
        ff=str(tmp/"farbank")
        subprocess.run(["g++","-O3","-std=c++20",str(R19/"enumerate_canon.cpp"),"-o",cc],check=True)
        subprocess.run(["g++","-O3","-std=c++20",str(R19/"farbank.cpp"),"-o",ff],check=True)
        bank=tmp/"bank.txt"
        codes=gather_bank()
        bank.write_text("\n".join(codes)+"\n")
        for r in inp["rows"]:
            idx=r["canonical_index"]
            if idx in SKIP or r["status"]!="scanned" or r.get("open",999999)>a.max_open:
                continue
            d=tmp/f"{idx:03}"
            d.mkdir()
            table=r["table"]
            assert len(table.replace("_",""))==36
            ec=subprocess.run([cc,table],cwd=d,capture_output=True,text=True,check=True)
            opens=(d/"open.txt").read_text().splitlines()
            assert len(opens)==r["open"],(idx,len(opens),r["open"])
            jobs="\n".join(f"{i} {w.replace('_','')}" for i,w in enumerate(opens))+"\n"
            try:
                z=subprocess.run([ff,str(a.dfa),str(bank)],input=jobs,cwd=d,
                    capture_output=True,text=True,timeout=a.time,check=True)
                witnesses={}
                for line in z.stdout.splitlines():
                    k,v=line.split()
                    assert int(k)<len(opens)
                    witnesses[int(k)]=v
                missing=[{"leaf":i,"table":t} for i,t in enumerate(opens) if i not in witnesses]
                dstatus="complete-far" if not missing else "some-far"
            except subprocess.TimeoutExpired:
                witnesses={}
                missing=[]
                dstatus="timeout"
            result={"canonical_index":idx,"table":table,
                "weighted_candidate":r["maxscore"],"opens":len(opens),
                "far":len(witnesses),"missing_count":len(missing),
                "missing":missing,"status":dstatus}
            results.append(result)
            print(f"{idx:03} {len(witnesses):4}/{len(opens):4} "
                  f"{dstatus:12} {table}",flush=True)
    output={
       "source_screen_sha":"run46078926057 original unmodified enumeration",
       "proof_status":"candidate FAR discovery, not Lean certification",
       "max_open":a.max_open,"dfa_states":a.dfa,
       "shard":inp["shard"],"shards":inp["shards"],
       "solved":sum(r["status"]=="complete-far" for r in results),
       "studied":len(results),"rows":results
    }
    a.out.write_text(json.dumps(output,indent=2)+"\n")
    print("SUMMARY",json.dumps({"shard":inp["shard"],"studied":len(results),
       "new_full_far":output["solved"],"timeouts":sum(r["status"]=="timeout" for r in results)}),flush=True)

if __name__=="__main__":
    main()
