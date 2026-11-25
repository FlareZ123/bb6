"""Regenerate exact symbolic witness proposals for the raw60/0LF frontier.

The family list is fixed data. The existing multi-block proof emitter checks
each macro through universally quantified finite equations and induction.
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path[:0] = [str(ROOT.parent / "agent31-three-hole-tnf"),
                str(ROOT.parent / "agent10-tnf-multipump")]
import generate_sweeps as one
import multi

def census(frontier):
    work = ROOT / "generated_0LF"
    work.mkdir(exist_ok=True)
    subprocess.run(["g++", "-std=c++17", "-O3",
                    str(ROOT.parent / "agent2-tnf-raw99/enumerate.cpp"),
                    "-o", str(work / "enumerate")], check=True)
    subprocess.run([str(work / "enumerate"),
                    "1RB0LF_1RC---_0RD---_1LD1RE_---1RA_------"],
                   cwd=work, check=True)
    data = (work / "open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest() == frontier["sha"]
    return data.decode().splitlines()

def generate(frontier, opens):
    ns = "BB6.Agent1Raw60LFPumps"
    parts = ["import SweepPumping", "set_option maxRecDepth 100000",
             "set_option maxHeartbeats 0", "set_option linter.unusedVariables false",
             f"namespace {ns}", "open BB6Coverage BB6Coverage.Agent31Pump"]
    manual = {}
    for key, (t, sd, q, raw) in sorted(frontier["families"].items(), key=lambda x:int(x[0])):
        i = int(key)
        p = one.parse(opens[i])
        w = multi.clean(tuple(tuple(x) for x in raw))
        v = multi.clean(tuple(y for s,b in w for y in (((s,False),(s,True)) if b else ((s,False),))))
        st = multi.C(q,w if sd=="R" else (),w if sd=="L" else ())
        tg = multi.C(q,v if sd=="R" else (),v if sd=="L" else ())
        ans = multi.pump(p,st,tg)
        assert ans is not None, i
        proof, info = multi.generate(i,p,(t,st,tg,ans))
        parts.append(proof)
        manual[key] = ["Raw60LFPumps",f"{ns}.M{i}",opens[i]]
        print("0LF",i,info,flush=True)
    parts.append("end "+ns)
    (ROOT/"Raw60LFPumps.lean").write_text("\n\n".join(parts)+"\n",encoding="utf-8")
    return manual

def main():
    frontier = json.loads((ROOT/"0lf-frontier.json").read_text())
    opens = census(frontier)
    generate(frontier, opens)

if __name__=="__main__":
    main()
