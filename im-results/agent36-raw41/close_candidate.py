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

def patch_late_last_holes(t, late):
    """Replace selected original canonical open leaves by checked last-hole queries."""
    counter=[0]
    def rec(node):
        kind=node[0]
        if kind=="open":
            i=counter[0]; counter[0]+=1
            if i in late:
                return ["last",late[i][0],late[i][1]]
            return node
        if kind=="split":
            return node[:3]+[[rec(c) for c in node[3]]]
        return node
    out=rec(t)
    return out,counter[0]

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--index",type=int,default=88)
    parser.add_argument("--dfa",type=int,default=5)
    parser.add_argument("--time",type=int,default=600)
    parser.add_argument("--out",type=Path,default=Path("/tmp/raw41-closure"))
    parser.add_argument("--late",action="append",default=[],help="Original open-index:exact-step:read-slot; e.g. 2:1423:9")
    parser.add_argument("--far-override",action="append",default=[],help="Original open-index:reflectedDFAcode; verified by the existing FAR constructor")
    parser.add_argument("--min-bound",type=int,default=0)
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
        bound=max(16,int(score.group(1)),args.min_bound)
        late={}
        for item in args.late:
            if not item.strip():continue
            i,n,slot=map(int,item.split(":"))
            assert i not in late and i>=0 and n>=0 and slot in range(12)
            late[i]=(n,slot)
        leaves=(temp/"open.txt").read_text().splitlines()
        bank=gather_bank()
        (temp/"bank.txt").write_text("\n".join(bank)+"\n")
        jobs="\n".join(f"{i} {s.replace(chr(95), '')}" for i,s in enumerate(leaves))+"\n"
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
        # The SMT synthesis is untrusted; independently reconstruct each
        # externally discovered compact DFA using the original source FAR
        # fixed-point checker before including it in Lean source.
        overrides={}
        for item in args.far_override:
            if not item.strip():continue
            i,code=item.split(":")
            idx=int(i)
            assert 0<=idx<len(leaves) and idx not in overrides
            assert re.fullmatch(r"[01][0-9]+",code) and len(code)%2
            normalized=leaves[idx].replace("_","")
            vals=tuple(-1 if normalized[k]=="-" else
                int(normalized[k])*12+6*(normalized[k+1]=="R")+ord(normalized[k+2])-65
                for k in range(0,36,3))
            g["far"](code,vals)
            overrides[idx]=code
        for idx,code in overrides.items():
            if idx in found:
                assert found[idx]==code,(idx,found[idx],code)
            found[idx]=code
        (args.out/"far.txt").write_text("".join(f"{i} {v}\n" for i,v in sorted(found.items())))
        missing=[(i,v) for i,v in enumerate(leaves) if i not in found]
        (args.out/"missing.txt").write_text("".join(f"{i} {v}\n" for i,v in missing))
        assert set(late).issubset({i for i,_ in missing}),"late clause must name a genuinely unclosed leaf"
        remaining_after_late=[(i,v) for i,v in missing if i not in late]
        summary=dict(index=args.index,table=table,bound=bound,opens=len(leaves),
             far_certificates=len(found),remaining=len(missing),
             late_last_holes={str(i): {"step":n,"slot":sl} for i,(n,sl) in late.items()},
             external_far_overrides={str(i):v for i,v in overrides.items()},
             remaining_after_late=len(remaining_after_late),
             bank_size=len(bank),timeout=truncated,
             proof_status="FAR candidates only, pending Lean source check")
        (args.out/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")
        print(json.dumps(summary,indent=2),flush=True)
        if not remaining_after_late:
            # Reuse original exact canonical tree and trusted source checker.
            source=args.out/"lean"
            source.mkdir(exist_ok=True)
            tree=json.loads((temp/"tree.json").read_text())
            patched,count=patch_late_last_holes(tree,late)
            assert count==len(leaves),(count,len(leaves))
            (source/"tree.json").write_text(json.dumps(patched)+"\n")
            mapping={i:k for k,i in enumerate(j for j in range(len(leaves)) if j not in late)}
            (source/"open.txt").write_text("".join(v+"\n" for i,v in enumerate(leaves) if i not in late))
            (source/"far.txt").write_text("".join(f"{mapping[i]} {v}\n" for i,v in sorted(found.items())))
            mod=f"Raw41New{args.index:03d}"
            run(["python3",str(R47/"gen_children.py"),str(source.resolve()),mod,str(bound),table,
                 "--standalone"],cwd=source)
            print(f"PROOF SOURCE READY: {mod}Closed.lean (NOT YET COMPILED)",flush=True)
if __name__=="__main__":
    main()
