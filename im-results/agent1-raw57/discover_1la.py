"""Native candidate discovery on the remaining 1LA leaves only."""
from pathlib import Path
import sys, json, hashlib, subprocess
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent/"agent31-three-hole-tnf"))
import generate_sweeps as one
sys.path.insert(0, str(ROOT.parent/"agent10-tnf-multipump"))
import multi
def main():
    far = json.loads((ROOT/"1la-far-frontier.json").read_text())
    ng = json.loads((ROOT/"1la-ngram-frontier.json").read_text())
    work = ROOT/"generated-1LA"
    work.mkdir(exist_ok=True)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent47-raw112-cut/enumerate_fast.cpp"),"-o",str(work/"enumerate")],check=True)
    subprocess.run([str(work/"enumerate"),far["parent"]],cwd=work,check=True)
    raw=(work/"open.txt").read_bytes()
    opens=raw.decode().splitlines()
    assert len(opens)==far["stats"]["open"]
    assert all(opens[i]==p for i,p in far["miss"])
    assert all(opens[i]==p for i,p in ng["miss"])
    spec={k:far[k] for k in ("bound","stats","bank","root")}
    spec.update(hash=hashlib.sha256(raw).hexdigest(),one=[],two=[],ngram=ng["ngram"])
    miss=[]
    for i,s in ng["miss"]:
        p=one.parse(s)
        ev=one.concrete_events(p,6000)
        a=one.candidate(p,ev)
        if a is not None:
            spec["one"].append(i)
        elif multi.candidate(p,ev) is not None:
            spec["two"].append(i)
        else:
            miss.append([i,s])
        print(i, "one" if i in spec["one"] else "two" if i in spec["two"] else "miss",flush=True)
    out={"spec":spec,"miss":miss}
    (work/"discovery.json").write_text(json.dumps(out,indent=2)+"\n")
    print("SPEC",json.dumps(spec,separators=(",",":")),flush=True)
    for i,s in miss:
        print("RESIDUAL",i,s,flush=True)
    print("COUNTS",len(spec["one"]),len(spec["two"]),len(miss),flush=True)
    if miss:
        raise SystemExit("Incomplete candidate partition")
if __name__=="__main__": main()
