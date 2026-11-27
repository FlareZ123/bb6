#!/usr/bin/env python3
"""Certify candidates only via original Lean checker; FAR discovery is untrusted.

Reuses Agent47's literal two-query canonical partition and Agent19's exact
enumerator/FAR search. Generates complete 24-branch Lean proof source if and
only if every open leaf receives a candidate FAR certificate.
"""
from __future__ import annotations
import argparse
import base64
import contextlib
import gzip
import io
import json
import re
import runpy
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
R47=ROOT/"im-results/agent47-raw41-cut"
R19=ROOT/"im-results/agent19-raw40-cut"
GEN=R47/"generate_two.py"

def run(args, **kw):
    return subprocess.run(args, check=True, text=True, **kw)

def gather_bank():
    bank=set()
    for f in sorted(R47.glob("**/far.txt")):
        for line in f.read_text().splitlines():
            a=line.split()
            if len(a)==2 and re.fullmatch(r"[01][0-9]+",a[1]) and len(a[1])%2:
                bank.add(a[1])
    bundled=R47/"survey-evidence.json.gz.b64"
    if bundled.exists():
        obj=json.loads(gzip.decompress(base64.b64decode(bundled.read_text())))
        for x in obj.values():
            for line in x.get("files",{}).get("far.txt","").splitlines():
                a=line.split()
                if len(a)==2 and re.fullmatch(r"[01][0-9]+",a[1]) and len(a[1])%2:
                    bank.add(a[1])
    return sorted(bank,key=lambda s:(len(s),s))

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--index",type=int,default=88)
    parser.add_argument("--dfa",type=int,default=5)
    parser.add_argument("--time",type=int,default=600)
    parser.add_argument("--out",type=Path,default=Path("/tmp/raw41-closure"))
    args=parser.parse_args()
    assert args.index>=0 and args.dfa in range(1,9)
    args.out.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="raw41-proof-") as temp:
        temp=Path(temp)
        with contextlib.chdir(temp):
            g=runpy.run_path(str(GEN))
        moves={g["move"](i):i for i in range(24)}
        reps=[]
        for first,second,table in g["residual"]:
            i,j=moves[first],moves[second]
            if i%6<=4 and j%6<=g["support"](g["refine"](g["T"],1,i)):
                reps.append(table)
        assert len(reps)==153
        assert args.index<len(reps)
        table=reps[args.index]
        run(["g++","-std=c++20","-O3",str(R19/"enumerate_canon.cpp"),"-o",str(temp/"enumerate")])
        run(["g++","-std=c++20","-O3",str(R19/"farbank.cpp"),"-o",str(temp/"farbank")])
        enumerator=run([str(temp/"enumerate"),table],cwd=temp,capture_output=True)
        score=re.search(r"maxscore=(\d+)",enumerator.stdout)
        assert score is not None,enumerator.stdout
        bound=max(16,int(score.group(1)))
        leaves=(temp/"open.txt").read_text().splitlines()
        bank=gather_bank()
        (temp/"bank.txt").write_text("\n".join(bank)+"\n")
        jobs="\n".join(f"{i} {s}" for i,s in enumerate(leaves))+"\n"
        found={}
        truncated=False
        if leaves:
            try:
                far=subprocess.run([str(temp/"farbank"),str(args.dfa),str(temp/"bank.txt")],
                    input=jobs,cwd=temp,capture_output=True,text=True,timeout=args.time)
                assert far.returncode==0,(far.returncode,far.stderr[-500:])
                for line in far.stdout.splitlines():
                    k,cert=line.split()
                    idx=int(k)
                    assert idx<len(leaves) and idx not in found
                    assert re.fullmatch(r"[01][0-9]+",cert) and len(cert)%2
                    found[idx]=cert
                (args.out/"far.stderr.txt").write_text(far.stderr)
            except subprocess.TimeoutExpired as e:
                truncated=True
                # Timeout cannot be promoted to a certificate. Preserve raw
                # output only when a complete certificate is present.
                raw=e.stdout or b""
                if isinstance(raw,bytes):raw=raw.decode(errors="replace")
                for line in raw.splitlines():
                    match=re.fullmatch(r"(\d+)\s+([01][0-9]+)",line.strip())
                    if match:
                        idx=int(match.group(1)); cert=match.group(2)
                        if idx<len(leaves) and len(cert)%2:
                            found[idx]=cert
        (args.out/"far.txt").write_text("".join(f"{i} {v}\n" for i,v in sorted(found.items())))
        missing=[(i,v) for i,v in enumerate(leaves) if i not in found]
        (args.out/"missing.txt").write_text("".join(f"{i} {v}\n" for i,v in missing))
        summary=dict(index=args.index,table=table,bound=bound,opens=len(leaves),
             far_certificates=len(found),remaining=len(missing),
             bank_size=len(bank),timeout=truncated,
             proof_status="FAR candidates only, pending Lean source check")
        (args.out/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")
        print(json.dumps(summary,indent=2),flush=True)
        if not missing:
            # Reuse original exact canonical tree and trusted source checker.
            source=args.out/"lean"
            source.mkdir(exist_ok=True)
            shutil.copy(temp/"tree.json",source/"tree.json")
            shutil.copy(temp/"open.txt",source/"open.txt")
            shutil.copy(args.out/"far.txt",source/"far.txt")
            mod=f"Raw41New{args.index:03d}"
            run(["python3",str(R47/"gen_children.py"),str(source),mod,str(bound),table,
                 "--standalone"],cwd=source)
            print(f"PROOF SOURCE READY: {mod}Closed.lean (NOT YET COMPILED)",flush=True)
if __name__=="__main__":
    main()
