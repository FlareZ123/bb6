"""Discover candidate specs for the four remaining raw60 children; no proof claims."""
import hashlib
import json
from concurrent.futures import ProcessPoolExecutor
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT=Path(__file__).resolve().parent
sys.path[:0]=[str(ROOT.parent/"agent31-three-hole-tnf"),str(ROOT.parent/"agent10-tnf-multipump")]
import generate_sweeps as one
import multi

def run(args, **kw):
    return subprocess.run(args, check=True, text=True, capture_output=True, **kw)

def late_scan(item):
    i, line = item
    p = one.parse(line)
    q = h = 0
    tape = set()
    for t in range(1000000):
        state = 2*q + (h in tape)
        move = p[state]
        if move == "---":
            return i, (t, state)
        if move[0] == "1":
            tape.add(h)
        else:
            tape.discard(h)
        h += 1 if move[1] == "R" else -1
        q = ord(move[2]) - 65
    return i, None

def main(a):
    target=ROOT/("discover_"+a)
    target.mkdir(exist_ok=True)
    for tool,src,std in [
        ("enumerate","agent2-tnf-raw99/enumerate.cpp","c++17"),
        ("bank","agent11-raw107/bank.cpp","c++20"),
        ("ngram","agent1-ngram/ngram.cpp","c++17"),
    ]:
        run(["g++","-std="+std,"-O3",str(ROOT.parent/src),"-o",str(target/tool)])
    en=run([str(target/"enumerate"),f"1RB{a}_1RC---_0RD---_1LD1RE_---1RA_------"],cwd=target)
    print(en.stdout,flush=True)
    data=(target/"open.txt").read_bytes()
    opens=data.decode().splitlines()
    tree=json.loads((target/"tree.json").read_text())
    assert tree[0]=="split"
    stats=Counter()
    def walk(t):
        stats[t[0]]+=1
        if t[0]=="split":
            for k in t[3]:walk(k)
    walk(tree)
    bound=int(re.search(r"maxscore=(\d+)",en.stdout)[1])
    spec=dict(bound=max(1175,bound),query=tree[1:3],stats=dict(stats),sha=hashlib.sha256(data).hexdigest(),one=[],multi=[],ngram=[],unresolved={},late={})
    def inp(ids,strip=False):
        return "".join(f"{i} {opens[i].replace('_','') if strip else opens[i]}\n" for i in ids)
    far=run([str(target/"bank"),str(ROOT/"bank.txt")],input=inp(range(len(opens)),True))
    misses=[int(l.split()[0]) for l in far.stderr.splitlines() if l.strip()]
    print("FAR misses",len(misses),flush=True)
    residual=[]
    for i in misses:
        p=one.parse(opens[i])
        ev=one.concrete_events(p,2500)
        if one.candidate(p,ev):spec["one"].append(i)
        elif multi.candidate(p,ev):spec["multi"].append(i)
        else:residual.append(i)
    print("Pumps",len(spec["one"]),len(spec["multi"]),"residual",len(residual),flush=True)
    ng=run([str(target/"ngram"),"12"],input=inp(residual))
    spec["ngram"]=[int(l.split()[0]) for l in ng.stdout.splitlines() if l.strip()]
    miss=[int(l.split()[0]) for l in ng.stderr.splitlines() if l.strip()]
    print("Ngram",len(spec["ngram"]),"remaining",len(miss),flush=True)
    workers = min(2, __import__("os").cpu_count() or 1)
    print("Late simulation workers",workers,flush=True)
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for i, hit in pool.map(late_scan, [(i, opens[i]) for i in miss]):
            if hit and opens[i].count("---")==1:
                spec["late"][str(i)]=[*hit,opens[i]]
                spec["bound"]=max(spec["bound"],hit[0]+6)
            else:
                spec["unresolved"][str(i)]=opens[i]
    print("RAW60SPEC "+a+" "+json.dumps(spec,separators=(",",":")),flush=True)
    (target/"spec.json").write_text(json.dumps(spec,indent=2)+"\n")

if __name__=="__main__":
    for a in sys.argv[1:]:main(a)
