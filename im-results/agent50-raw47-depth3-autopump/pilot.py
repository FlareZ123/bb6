#!/usr/bin/env python3
"""Pilot existing AutoPump recurrence discovery on the 50 longest Raw47 depth-3 leaves."""
from pathlib import Path
import json, sys, time
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"im-results/agent48-raw139-f1-oneLA"))
from autopump import find, trace, js

def parse(row):
    chunks=row.split("_")
    slots=[chunks[i][j:j+3] for i in range(6) for j in (0,3)]
    out=[]
    for x in slots:
        if x in ("---","HHH"):
            out.append(24)
        else:
            out.append(4*(ord(x[2])-65)+2*int(x[0])+(1 if x[1]=="R" else 0))
    return out

def main():
    out=Path(sys.argv[1]) if len(sys.argv)>1 else Path("/tmp/raw47-autopump")
    out.mkdir(parents=True,exist_ok=True)
    rows=(ROOT/"im-results/agent50-raw47-depth3/raw47-depth3.open").read_text().splitlines()
    ranked=[]
    t0=time.time()
    for i,row in enumerate(rows):
        p=parse(row)
        ranked.append((len(trace(p,2000)),i,p,row))
    ranked.sort(reverse=True)
    selected=ranked[:50]
    candidates=[]
    for rank,(length,i,p,row) in enumerate(selected,1):
        t=time.time()
        result=find(p,lim=2000)
        if result is None:
            continue
        entry,family,sol=result
        data={"table":p,"result":(entry,family,sol)}
        path=out/f"pump-{i}.json"
        path.write_text(json.dumps(data,default=js,separators=(",",":"))+"\n")
        ops,end=sol
        candidates.append({"id":i,"trace_length":length,"entry":entry,"ops":len(ops),"fixture":path.name,"table":row})
        print(f"candidate id={i} trace={length} entry={entry} ops={len(ops)} elapsed={time.time()-t:.2f}s",flush=True)
    summary={
        "residuals":len(rows),
        "ranked_by_trace":50,
        "max_trace_length":max((x[0] for x in ranked),default=0),
        "min_selected_trace_length":selected[-1][0] if selected else 0,
        "candidates":len(candidates),
        "candidate_ids":[x["id"] for x in candidates],
        "elapsed_seconds":round(time.time()-t0,3),
        "candidates_detail":candidates
    }
    (out/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    print(json.dumps({k:v for k,v in summary.items() if k!="candidates_detail"},indent=2))
if __name__=="__main__":main()
