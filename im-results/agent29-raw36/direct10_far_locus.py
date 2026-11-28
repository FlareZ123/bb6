#!/usr/bin/env python3
"""Rank D1=0RE first-level residuals after 1705 cross-family FAR hits.

Candidate discovery only: the literal FAR witnesses must still be
original-source Lean checked before being claimed as Covers.
"""
import argparse,gzip,hashlib,json
from collections import Counter
from pathlib import Path
MOVES=[w+d+q for w in "01" for d in "LR" for q in "ABCDEF"]
def index(table):
    raw=table.replace("_","")
    assert len(raw)==36
    move=raw[24:27]
    assert move in MOVES,(table,move)
    return MOVES.index(move)
def main():
    p=argparse.ArgumentParser(description=__doc__)
    for arg in ("census","remaining","recovery_summary","out"):
        p.add_argument("--"+arg.replace("_","-"),required=True,type=Path)
    a=p.parse_args()
    data=json.loads(gzip.decompress(a.census.read_bytes()))
    summary=json.loads(a.recovery_summary.read_text())
    assert data["parent"]=="1RB---_1RC---_0RD---_0LD0RE_------_------"
    assert summary["index"]==10 and summary["dmax"]==4
    total=set(data["opens"])
    rem=[t.strip() for t in a.remaining.read_text().splitlines() if t.strip()]
    assert len(rem)==len(set(rem))==summary["remaining"]==933
    assert set(rem)<=total
    assert len(total)==summary["canonical_OPEN"]==2638
    digest=hashlib.sha256("\n".join(sorted(rem)).encode()).hexdigest()
    assert digest==summary["remaining_sha256"]
    assert len(total)-len(rem)==summary["cross_FAR_hits"]==1705
    orig=Counter(map(index,total)); leftover=Counter(map(index,rem))
    rows=[{"index":i,"move":MOVES[i],"original_open":orig[i],
           "far_hits":orig[i]-leftover[i],"after_far_open":leftover[i]}
          for i in range(24)]
    rows.sort(key=lambda r:(r["after_far_open"],r["original_open"]))
    report={"status":"candidate FAR subtree census, not Lean proof",
            "parent":data["parent"],"source_census_run_id":46122807180,
            "far_recovery_run_id":46153748009,
            "remaining_sha256":digest,"rows":rows,
            "zero_after_far":[r["index"] for r in rows if r["after_far_open"]==0],
            "total_open":2638,"total_far_hits":1705,"total_unresolved":933}
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps(report,sort_keys=True),flush=True)
if __name__=="__main__":main()
