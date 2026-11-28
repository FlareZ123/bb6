#!/usr/bin/env python3
"""Locate promising D1=0RE E0 subparents after exact-table FAR+RLE scans.

All classifiers here are DISCOVERY candidates. No symbolic proof is claimed
until source-generated individual witnesses pass Lean. The source C++ census,
recovered FAR and regular-stack lists must exhaustively and *disjointly*
partition the 2,638 original unresolved exact tables.
"""
import argparse,gzip,hashlib,json
from collections import Counter
from pathlib import Path
MOVES=[w+d+q for w in "01" for d in "LR" for q in "ABCDEF"]
TABLE="1RB---_1RC---_0RD---_0LD0RE_------_------"
def index(key):
    raw=key.replace("_","")
    assert len(raw)==36,(key,len(raw))
    mv=raw[24:27]
    assert mv in MOVES,(key,mv)
    return MOVES.index(mv)
def sha_lines(rows):
    return hashlib.sha256("\n".join(sorted(rows)).encode()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ("census","far_summary","far_found","structured_summary","structured_found","out"):
        ap.add_argument("--"+name.replace("_","-"),required=True,type=Path)
    a=ap.parse_args()
    source=json.loads(gzip.decompress(a.census.read_bytes()))
    assert source["parent"]==TABLE and source["stats"]["open"]==2638
    raw=source["tree"]
    assert raw[0]=="split" and raw[2]==8 and len(raw[3])==24
    exact=source["opens"]
    assert len(exact)==len(set(exact))==2638
    farstats=json.loads(a.far_summary.read_text())
    frows=[s.split() for s in a.far_found.read_text().splitlines() if s.strip()]
    assert len(frows)==1705 and all(len(r)==2 for r in frows)
    far=set(t for t,c in frows)
    assert len(far)==1705==farstats["cross_FAR_hits"]
    ststats=json.loads(a.structured_summary.read_text())
    strows=json.loads(a.structured_found.read_text())
    assert ststats["parent"]==TABLE and len(strows)==ststats["hits"]==809
    structured=set(t for t,v in strows)
    assert len(structured)==809
    exactset=set(exact)
    assert (far | structured)<=exactset
    assert far.isdisjoint(structured),len(far&structured)
    remaining=exactset-far-structured
    assert len(remaining)==124==ststats["remaining"]
    assert sha_lines(remaining)==ststats["remaining_sha256"]
    orig=Counter(map(index,exactset))
    f=Counter(map(index,far))
    st=Counter(map(index,structured))
    left=Counter(map(index,remaining))
    closed_cycles=[i for i in range(24) if orig[i]==0]
    rows=[{"i":i,"E0":MOVES[i],"orig":orig[i],"far":f[i],
           "structured":st[i],"unresolved":left[i]}
        for i in range(24)]
    rows.sort(key=lambda r:(r["unresolved"],r["orig"]))
    report={"kind":"unverified candidate discovery; no Lean Cover",
        "machine":TABLE,"source_run_id":46122807180,
        "far_run_id":46153748009,"structured_run_id":46154479283,
        "total_exact":2638,"far":1705,"structured":809,"unresolved":124,
        "remaining_sha256":sha_lines(remaining),
        "cycle_only_children":closed_cycles,
        "candidate_completed_children":[r["E0"] for r in rows if r["unresolved"]==0],
        "ranked":rows}
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps(report,sort_keys=True),flush=True)
if __name__=="__main__":main()
