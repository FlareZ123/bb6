#!/usr/bin/env python3
"""Replay the exact D1=0RE structured quotient winners on Raw36 D1=1LA residual literals.

Discovery/reuse only.  Every accepted literal must still pass the independent
TwoSidedAutomata Lean checker before it is used in a parent Cover.
"""
import argparse,gzip,hashlib,json,sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"agent7-raw36-b1le"))
from stack_candidates import replay

CENSUS_SHA="cb699136a90a91f972542cdd62aa1340d42e58c39dfff867dce5e84444da7866"
FAR_SHA="93d0c64957cdf26a0458e88c8e829d747d3b6d01257055ce41b511f0b6430eb5"
D110_STRUCT_SHA="a56b0a2558ee5576ce2de4f40069a39349d06e10764ea4aec70a29ed2c9c5560"
FOUND_SHA="4f65305134b5151243d7b1ae61ae1582bc4b25f0298d65ded52680999e7c9b8d"
REMAIN_SHA="6efc697700bd538cdd552bfa35913ba7e3cbb6df38aeda10c78225f5371af8d"
PARENT="1RB---_1RC---_0RD---_0LD1LA_------_------"

def sha(p):
    with Path(p).open("rb") as f:
        return hashlib.file_digest(f,"sha256").hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--census",required=True,type=Path)
    ap.add_argument("--far-found",required=True,type=Path)
    ap.add_argument("--structured-seeds",required=True,type=Path)
    ap.add_argument("--out",required=True,type=Path)
    a=ap.parse_args()
    assert sha(a.census)==CENSUS_SHA
    assert sha(a.far_found)==FAR_SHA
    assert sha(a.structured_seeds)==D110_STRUCT_SHA
    data=json.loads(gzip.decompress(a.census.read_bytes()))
    assert data["parent"]==PARENT and data["stats"]["open"]==3841
    far={line.split("\t")[0] for line in a.far_found.read_text().splitlines() if line.strip()}
    assert len(far)==2345 and far<=set(data["opens"])
    seed_rows=json.loads(a.structured_seeds.read_text())
    params=sorted({tuple(v[:-1]) for _,v in seed_rows})
    assert len(params)==27
    found=[];missing=[]
    for table in sorted(set(data["opens"])-far):
        p=tuple(table.replace("_","")[i:i+3] for i in range(0,36,3))
        hit=None
        for spec in params:
            v=[*spec,None]
            try:
                _,n,_,_,_,_=replay(p,v)
            except (AssertionError,IndexError,ValueError,MemoryError,ZeroDivisionError):
                continue
            v[-1]=n; hit=v; break
        if hit is None: missing.append(table)
        else: found.append([table,hit])
    assert len(found)==1343 and len(missing)==153
    a.out.mkdir(parents=True,exist_ok=True)
    fp=a.out/"structured27.json"; mp=a.out/"remaining153.txt"
    fp.write_text(json.dumps(found,separators=(",",":")))
    mp.write_text("\n".join(missing)+"\n")
    assert sha(fp)==FOUND_SHA
    assert sha(mp)==REMAIN_SHA
    kinds={k:sum(v[0]==k for _,v in found) for k in ("r","m","p")}
    report={"parent":PARENT,"canonical_open":3841,"far_closed":2345,
            "structured_closed":1343,"remaining":153,"structured_seed_count":27,
            "kinds":kinds,"structured_sha256":FOUND_SHA,
            "remaining_sha256":REMAIN_SHA,
            "status":"candidate structured replay; independent Lean source gate required"}
    (a.out/"summary.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps(report,sort_keys=True))

if __name__=="__main__":
    main()
