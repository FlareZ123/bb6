"""Exact literal Raw36 direct-D1 scout using preserved DFA witnesses.

This script is discovery only: the canonical tree and all far/cycle leaves must
be independently source-checked before asserting any Cover.
"""
import base64, gzip, hashlib, json, os, subprocess, sys, tempfile
from pathlib import Path
from itertools import product

ROOT = Path(__file__).resolve().parent
R29 = ROOT.parent / "agent29-raw36"
R7 = ROOT.parent / "agent7-raw36-b1le"
TRANSFER = ROOT.parent / "agent7-raw36-transfer"
MOVES = [w+d+q for w,d,q in product("01","LR","ABCDEF")]

def scout(index: int, output: Path):
    assert index in [0,1,4,10,12,16,22], index
    output.mkdir(parents=True,exist_ok=True)
    spec=json.loads((R29/"candidate.json").read_text())
    assert spec["options"]["short"] == 160
    archive=gzip.decompress(base64.b64decode((TRANSFER/"fixture.tsv.gz.b64").read_text())).decode()
    codes=list(dict.fromkeys([*spec["codes"],"101230333","101023202",*(x.split()[1] for x in archive.splitlines())]))
    literal="1RB---_1RC---_0RD---_0LD"+MOVES[index]+"_------_------"
    cut=max(4,index%6+1)
    with tempfile.TemporaryDirectory() as tmp:
        wd=Path(tmp)
        (wd/"codes.txt").write_text("\n".join(codes)+"\n")
        subprocess.run(["g++","-std=c++17","-O3",str(R7/"scan_tree.cpp"),"-o",str(wd/"scan")],check=True)
        result=json.loads(subprocess.check_output([str(wd/"scan"),literal,str(cut),str(wd/"codes.txt"),str(wd/"tree.json")],text=True))
        assert result["parent"] == literal and result["cut"] == cut
        result["tree"] = json.loads((wd/"tree.json").read_text())
    keys=sorted(x.replace("_","") for x in result["opens"])
    assert len(keys)==len(set(keys))
    summary={"index":index,"move":MOVES[index],"parent":literal,"cut":cut,"stats":result["stats"],"mass":result["mass"],"seeds":len(codes),"open_digest":hashlib.sha256("\n".join(keys).encode()).hexdigest()}
    (output/f"direct{index:02d}.json.gz").write_bytes(gzip.compress(json.dumps(result,separators=(",",":")).encode(),mtime=0))
    (output/f"summary{index:02d}.json").write_text(json.dumps(summary,indent=2)+"\n")
    print(json.dumps(summary),flush=True)

if __name__=="__main__":
    scout(int(sys.argv[1]),Path(sys.argv[2]))
