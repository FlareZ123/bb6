#!/usr/bin/env python3
"""Rank exact D1=0RE first-level seven-hole children by unresolved literals.

Uses only the original archived canonical tree from run 46122807180.
This is discovery, not a proof: a zero-OPEN child still needs a full
Lean-checkable audit under the original exact machine semantics.
"""
import argparse,gzip,hashlib,json
from collections import Counter
from pathlib import Path

MOVES=[w+d+q for w in "01" for d in "LR" for q in "ABCDEF"]
def stats(node):
    tag=node[0]
    if tag=="split":
        total=Counter({"split":1})
        assert len(node)==4 and len(node[3])==24,node[0]
        for kid in node[3]:total.update(stats(kid))
        return total
    assert tag in {"cycle","far","open","halt","last","skip"},tag
    return Counter({tag:1})
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--census",type=Path,required=True)
    p.add_argument("--out",type=Path,required=True)
    a=p.parse_args()
    data=json.loads(gzip.decompress(a.census.read_bytes()))
    assert data["parent"]=="1RB---_1RC---_0RD---_0LD0RE_------_------"
    assert data["cut"]==5
    root=data["tree"]
    assert root[0]=="split" and len(root[3])==24
    sums=stats(root)
    assert sums["open"]==data["stats"]["open"]
    assert sums["cycle"]==data["stats"]["cycle"]
    assert sums["far"]==data["stats"]["far"]
    assert sums["last"]==data["stats"]["last"]
    children=[]
    for i,child in enumerate(root[3]):
        counts=stats(child)
        children.append({"index":i,"move":MOVES[i],"open":counts["open"],
           "split":counts["split"],"nodes":sum(counts.values()),
           "far":counts["far"],"cycle":counts["cycle"],
           "last":counts["last"],"halt":counts["halt"]})
    keys=sorted(t.replace("_","") for t in data["opens"])
    assert len(keys)==len(set(keys))==data["stats"]["open"]
    digest=hashlib.sha256("\n".join(keys).encode()).hexdigest()
    summary={"parent":data["parent"],"source_census_sha256":
        hashlib.file_digest(a.census.open("rb"),"sha256").hexdigest(),
       "full_root_open_digest":digest,
       "stats":data["stats"],
       "zero_open_indices":[r["index"] for r in children if r["open"]==0],
       "children":sorted(children,key=lambda r:(r["open"],r["nodes"]))}
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(summary,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"open":sums["open"],
       "zero_open_indices":summary["zero_open_indices"],
       "ranked":summary["children"][:12]},sort_keys=True),flush=True)
if __name__=="__main__":main()
