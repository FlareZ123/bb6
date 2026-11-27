#!/usr/bin/env python3
"""Reproducible screening of UNRESOLVED Raw41 canonical five-hole cylinders.

The original Raw41 two-query canonical construction and source C++ enumerator
are reused verbatim. This script is DISCOVERY ONLY: every proposed Cover must
be certified by the existing Lean canonical checker and (when needed) FAR
or original-source symbolic nonhalting certificates.
"""
from __future__ import annotations

import argparse
import contextlib
import io
import json
import re
import runpy
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GEN = ROOT / "im-results/agent47-raw41-cut/generate_two.py"
ENUM = ROOT / "im-results/agent19-raw40-cut/enumerate_canon.cpp"

# Already investigated, locally checked or assigned elsewhere; avoid rerunning.
PREVIOUS_TABLES = {
 "1RB0LC_1RC---_0RD0RA_1LD1RA_------_------",
 "1RB0LB_1RC0LC_0RD---_1LD1RA_------_------",
 "1RB0LD_1RC0LC_0RD---_1LD1RA_------_------",
 "1RB0LB_1RC0RB_0RD---_1LD1RA_------_------",
 "1RB0LC_1RC---_0RD1LB_1LD1RA_------_------",
 "1RB0LC_1RC---_0RD0LB_1LD1RA_------_------",
 "1RB0LB_1RC1RB_0RD---_1LD1RA_------_------",
 "1RB0RB_1RC0RC_0RD---_1LD1RA_------_------",
 "1RB0LB_1RC0LD_0RD---_1LD1RA_------_------",
 "1RB0LB_1RC0RE_0RD---_1LD1RA_------_------",
 "1RB0LB_1RC1LB_0RD---_1LD1RA_------_------",
 "1RB0LB_1RC1RE_0RD---_1LD1RA_------_------",
 "1RB0LC_1RC---_0RD1RE_1LD1RA_------_------",
 "1RB0LD_1RC0RE_0RD---_1LD1RA_------_------",
}
def all_representatives():
    # runpy executes the already published deterministic two-query generator.
    # A working directory is set by caller so generated temporary Lean is
    # not written to the checkout.
    with contextlib.redirect_stdout(io.StringIO()):
        g = runpy.run_path(str(GEN))
    moves = {g["move"](i): i for i in range(24)}
    residual = g["residual"]
    support, refine, T = g["support"], g["refine"], g["T"]
    reps = []
    for first, second, table in residual:
        i, j = moves[first], moves[second]
        if i % 6 <= 4 and j % 6 <= support(refine(T,1,i)):
            reps.append({"first": first, "second": second, "table": table})
    assert len(residual) == 261, len(residual)
    assert len(reps) == 153, len(reps)
    assert len({x["table"] for x in reps}) == 153
    return reps

def main():
    a=argparse.ArgumentParser()
    a.add_argument("--shard",type=int,default=0)
    a.add_argument("--shards",type=int,default=4)
    a.add_argument("--timeout",type=int,default=90)
    a.add_argument("--output",type=Path,default=Path("/tmp/raw41-screen.json"))
    p=a.parse_args()
    assert 0<=p.shard<p.shards and p.timeout>=5
    with tempfile.TemporaryDirectory() as tmp:
        tmp=Path(tmp)
        with contextlib.chdir(tmp):
            reps=all_representatives()
        exe=tmp/"enum"
        subprocess.run(["g++","-O3","-std=c++20",str(ENUM),"-o",str(exe)],check=True)
        rows=[]
        for i,x in enumerate(reps):
            if i%p.shards!=p.shard or x["table"] in PREVIOUS_TABLES:
                continue
            folder=tmp/"scan";folder.mkdir(exist_ok=True)
            try:
                r=subprocess.run([str(exe),x["table"]],cwd=folder,
                    text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                    timeout=p.timeout)
                first=r.stdout.splitlines()[0] if r.stdout else ""
                stats=dict((k,int(v)) for k,v in re.findall(r"(cycle|last|open|split):(\d+)",first))
                if r.returncode or not stats:
                    raise ValueError(f"enumerator rc={r.returncode}, output={r.stdout[-400:]!r}")
                score_match=re.search(r"maxscore=(\d+)",r.stdout)
                row={**x,"canonical_index":i,**stats,
                    "maxscore":int(score_match.group(1)) if score_match else None,
                    "status":"scanned"}
                rows.append(row)
                print(f"{i:03} opens={row.get('open',0):5} "
                      f"splits={row.get('split',0):6} score<={row['maxscore']} "
                      f"{x['table']}",flush=True)
            except (subprocess.TimeoutExpired,ValueError) as e:
                rows.append({**x,"canonical_index":i,"status":type(e).__name__,
                    "error":str(e)[:400]})
                print(f"{i:03} {type(e).__name__} {x['table']}",flush=True)
            for filename in ("tree.json","open.txt"):
                (folder/filename).unlink(missing_ok=True)
    p.output.parent.mkdir(parents=True,exist_ok=True)
    result={"method":"original two-query generator + exact canonical enumerator",
        "proof_status":"discovery only","canonical_total":153,
        "shard":p.shard,"shards":p.shards,"previous_tables_excluded":len(PREVIOUS_TABLES),
        "rows":rows}
    p.output.write_text(json.dumps(result,indent=2)+"\n")
    ranked=sorted((r for r in rows if r["status"]=="scanned"),
                  key=lambda r:(r.get("open",999999),r["canonical_index"]))
    print("BEST OPEN-LEAF COUNTS",flush=True)
    for r in ranked[:15]:
        print(f"  {r['canonical_index']:03}: {r.get('open',0)} "
              f"opens, {r['table']}",flush=True)
    print("FULL SUMMARY",json.dumps({"scanned":len(ranked),
          "zero_open":sum(r.get("open",1)==0 for r in ranked),
          "timeouts":sum(r["status"]=="TimeoutExpired" for r in rows)}),flush=True)

if __name__=="__main__":
    main()
