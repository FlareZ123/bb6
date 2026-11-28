#!/usr/bin/env python3
"""Reproduce exact FAR reuse from accepted Raw36 D1=0RE candidates onto D1=1LA OPEN literals."""
import argparse,gzip,hashlib,json,subprocess
from collections import Counter
from pathlib import Path

D112_GZ_SHA="cb699136a90a91f972542cdd62aa1340d42e58c39dfff867dce5e84444da7866"
D110_FOUND_SHA="ed56aa2f9f27a140ad580d3b6f88a8bcfc70a5479eb32fdb29489663b0bdad67"
CODES_SHA="155716616620d72794e15e73bf8b01e575797b3bc9ec4da62fcfbd2b113df034"
OUTPUT_SHA="93d0c64957cdf26a0458e88c8e829d747d3b6d01257055ce41b511f0b6430eb5"
PARENT="1RB---_1RC---_0RD---_0LD1LA_------_------"

def sha(p):
    with Path(p).open("rb") as f:
        return hashlib.file_digest(f,"sha256").hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--census",required=True,type=Path)
    ap.add_argument("--reuse-found",required=True,type=Path)
    ap.add_argument("--scanner",required=True,type=Path)
    ap.add_argument("--out",required=True,type=Path)
    a=ap.parse_args()
    assert sha(a.census)==D112_GZ_SHA
    assert sha(a.reuse_found)==D110_FOUND_SHA
    d=json.loads(gzip.decompress(a.census.read_bytes()))
    assert d["parent"]==PARENT and d["stats"]["open"]==len(d["opens"])==3841
    assert d["stats"]["score"]==1015
    codes=sorted({line.split()[1] for line in a.reuse_found.read_text().splitlines() if line.strip()})
    code_bytes=("\n".join(codes)+"\n").encode()
    assert len(codes)==441 and hashlib.sha256(code_bytes).hexdigest()==CODES_SHA
    a.out.mkdir(parents=True,exist_ok=True)
    tables=a.out/"tables.txt"; seeds=a.out/"seeds.txt"; found=a.out/"found.tsv"
    tables.write_text("\n".join(d["opens"])+"\n"); seeds.write_bytes(code_bytes)
    with found.open("w") as fo:
        subprocess.run([str(a.scanner),str(tables),str(seeds)],stdout=fo,check=True)
    rows=[line.split("\t") for line in found.read_text().splitlines() if line.strip()]
    assert len(rows)==len({r[0] for r in rows})==2345
    assert set(r[0] for r in rows)<=set(d["opens"])
    assert set(r[1] for r in rows)<=set(codes)
    assert sha(found)==OUTPUT_SHA
    by_d=Counter((len(r[1])-1)//2 for r in rows)
    report={
      "kind":"exact finite FAR candidate reuse; Lean source gate required per literal",
      "parent":PARENT,"bound":1015,"canonical_open":3841,
      "reuse_seed_count":441,"closed":2345,"remaining":1496,
      "winner_count":len({r[1] for r in rows}),
      "closed_by_d":dict(sorted(by_d.items())),
      "source_census_run":46122807180,
      "source_census_artifact":15254284649,
      "reuse_bank_run":46153748009,
      "reuse_bank_artifact":15266667082,
      "found_sha256":OUTPUT_SHA,
    }
    (a.out/"summary.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps(report,sort_keys=True))

if __name__=="__main__":
    main()
