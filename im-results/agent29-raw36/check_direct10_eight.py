#!/usr/bin/env python3
"""Check the new 16-cycle / 8-live D1=0RE original-source theorem.

The canonical census selects literal side-cycle witnesses; Lean checks each
witness, normal-machine covering of all 25 E0 outcomes, and the exact
weighted terminal bound. Full accepted B1 dependency closure is reconstructed
from pinned original-source proof objects first.
"""
import argparse,hashlib,json,os,re,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
sys.path.insert(0,str(HERE))
import compose_accepted as base
import emit_direct10_eight as emit
NS="BB6.Agent29Raw36D110Live8."
NAMES=["parent_root","parent_nohalt","parent_query","haltChild",
       "ordinaryExact","liveComplete","cycleCover",
       "parent_cover_from_live8","live_count"]
ALLOWED={"propext","Classical.choice","Quot.sound"}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--census",type=Path,required=True)
    ap.add_argument("--archives",type=Path,required=True)
    ap.add_argument("--work",type=Path,required=True)
    a=ap.parse_args()
    work=a.work.resolve()
    a.archives.resolve().mkdir(parents=True,exist_ok=True)
    subprocess.run([sys.executable,str(HERE/"compose_accepted.py"),
                    "--inputs",str(a.archives.resolve()),
                    "--work",str(work),"--download"],check=True)
    provenance=json.loads((work/"manifest.json").read_text())
    assert provenance["claim"]["theorem"]=="BB6.Agent29Raw36.parent_cover_from_nine"
    src=work/"Raw36D110Live8.lean"
    summary=work/"raw36-d110-live8-candidate.json"
    subprocess.run([sys.executable,str(HERE/"emit_direct10_eight.py"),
                    "--census",str(a.census.resolve()),
                    "--source",str(src),"--summary",str(summary)],check=True)
    env=dict(os.environ,LEAN_PATH=str(work))
    c=subprocess.run(["lean","-o",src.stem+".olean",src.name],
                     cwd=work,env=env,text=True,capture_output=True)
    (work/"raw36-d110-live8-source.log").write_text(c.stdout+"\n"+c.stderr)
    print(c.stdout,flush=True)
    if c.returncode:
        print(c.stderr,file=sys.stderr,flush=True)
        raise RuntimeError("Raw36 D1=0RE source Lean proof rejected")
    assert not re.search(r"sorryAx|native_decide",c.stdout+c.stderr)
    observed=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",c.stdout))
    assert set(observed)=={NS+n for n in NAMES},observed
    assert all(set(t.strip() for t in val.split(",") if t.strip())<=ALLOWED
               for val in observed.values()),observed
    receipt=json.loads(summary.read_text())
    assert receipt["cycle_indices"]==[0,1,2,3,6,7,8,9,10,14,15,18,19,20,21,22]
    assert receipt["live_indices"]==[4,5,11,12,13,16,17,23]
    receipt.update({
      "status":"original-source accepted D1=0RE 16-cycle / eight-cover parent",
      "source_revision":subprocess.check_output(["git","rev-parse","HEAD"],
                                            cwd=REPO,text=True).strip(),
      "accepted_nine_parent":provenance["claim"],
      "theorem":NS+"parent_cover_from_live8",
      "root_olean_sha256":base.file_sha(work/(src.stem+".olean")),
      "axioms":observed,
    })
    (work/"raw36-d110-live8-accepted.json").write_text(
       json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print("PASS: exact original-source 16 Raw36 D1=0RE cycle Covers, "
          "8 explicit next-child hypotheses",flush=True)

if __name__=="__main__":main()
