#!/usr/bin/env python3
"""Original-source consume two complete E0 branches of Raw36 D1=0RE.

One common generator pass names every FAR/stack producer exactly once,
avoiding identity collisions between E0=0LE's 13 candidates and E0=1LB's
40 candidates, the latter including the NEW 'r',6,9,5,1318 proof.
All producer modules are checked by Lean; no candidate result is trusted.
"""
import argparse,base64,hashlib,json,lzma,os,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
sys.path.insert(0,str(HERE))
import compose_accepted as base
from compose_direct10_child04 import read_parent_banks,run_lean,check_axioms
from emit_direct10_eight import MOVES
LITERAL="1RB---_1RC1LC_0RD1RF_0LD0RE_1LB1RA_1RE0LF"
def main():
    a=argparse.ArgumentParser(description=__doc__)
    for name in ("census","far","structured","archives","work"):
       a.add_argument("--"+name,required=True,type=Path)
    p=a.parse_args()
    work=p.work.resolve()
    staging=work.with_name(work.name+"-inputs")
    staging.mkdir(parents=True,exist_ok=False)
    p.archives.resolve().mkdir(parents=True,exist_ok=True)
    census,fixture,child04=read_parent_banks(p)
    keys=sorted(t.replace("_","") for t in census["opens"])
    hard=LITERAL.replace("_","")
    assert len(hard)==36 and hard in keys and hard[24:27]=="1LB"
    j=keys.index(hard)
    assert fixture["data"][j] is None
    fixture["data"][j]=["r",6,9,5,1318]
    assert len(child04)==13
    # All 40 canonical OPEN tables beneath E0=1LB now have proposed
    # FAR/stack certificates; kernel checking is the decisive part.
    keys13={t.replace("_","") for t in census["opens"] if
           t.replace("_","")[24:27]=="1LB"}
    assert len(keys13)==40
    assert all(fixture["data"][keys.index(k)] is not None for k in keys13)
    assert len(keys13-{hard})==39
    src=staging/"direct10-census.json"
    src.write_text(json.dumps(census,separators=(",",":"))+"\n")
    fixture_file=staging/"direct10-two-children.xz.b64"
    fixture_file.write_text(base64.b64encode(lzma.compress(
      json.dumps(fixture,separators=(",",":")).encode())).decode()+"\n")
    subprocess.run([sys.executable,str(HERE/"compose_accepted.py"),
       "--inputs",str(p.archives.resolve()),"--work",str(work),"--download"],
       check=True)
    predecessor=json.loads((work/"manifest.json").read_text())
    assert predecessor["claim"]["theorem"]=="BB6.Agent29Raw36.parent_cover_from_nine"
    generator=HERE/"generate_direct10_multi.py"
    subprocess.run([sys.executable,str(generator),str(src),str(work),
       str(fixture_file),"300","10","4,13"],check=True)
    run_lean(work,"Raw36D110Base")
    for name in sorted(x.stem for x in work.glob("Raw36D110Automata*.lean")):
        run_lean(work,name)
    for name in sorted(x.stem for x in work.glob("Raw36D110Sweep*.lean")):
        run_lean(work,name)
    for kid in ("04","13"):
        r=run_lean(work,"Raw36D110Kid"+kid)
        check_axioms(r,["BB6.Agent29Raw36D110.kid"+kid+"_bound"])
    # First-level 16 side-cycle Cover source already accepted independently.
    subprocess.run([sys.executable,str(HERE/"emit_direct10_eight.py"),
       "--census",str(p.census.resolve()),
       "--source",str(work/"Raw36D110Live8.lean"),
       "--summary",str(work/"direct10-source-16cycles.json")],check=True)
    r=run_lean(work,"Raw36D110Live8")
    ns8="BB6.Agent29Raw36D110Live8."
    check_axioms(r,[ns8+x for x in ("parent_root","parent_nohalt",
        "parent_query","haltChild","ordinaryExact","liveComplete",
        "cycleCover","parent_cover_from_live8","live_count")])
    names=[
      ("Raw36D110Live7AfterE0LE","BB6.Agent29Raw36D110Live7.",(
        "child04_identity","child04_cover","live8_from_live7",
        "parent_cover_from_live7","live7_count")),
      ("Raw36D110Live6AfterE0LE1LB","BB6.Agent29Raw36D110Live6.",(
        "child13_identity","child13_cover","live7_from_live6",
        "parent_cover_from_live6","live6_count")),
    ]
    profiles={}
    for name,ns,required in names:
        file=HERE/(name+".lean")
        (work/file.name).write_bytes(file.read_bytes())
        compiled=run_lean(work,name)
        profiles.update(check_axioms(compiled,[ns+x for x in required]))
    last=work/(names[-1][0]+".olean")
    receipt={
      "status":"original-source accepted D110 E0=0LE and E0=1LB complete six-hole Covers",
      "source_revision":subprocess.check_output(["git","rev-parse","HEAD"],
                                     cwd=REPO,text=True).strip(),
      "parent":"1RB---_1RC---_0RD---_0LD0RE_------_------",
      "B":2004,
      "E0_children_closed":["0LE","1LB"],
      "E0_ordinary_cycle_children_closed":16,
      "remaining_E0_cover_count":6,
      "remaining_E0_moves":["0LF","0RF","1LA","1LE","1LF","1RF"],
      "whole_E0_0LE_child_proof":"BB6.Agent29Raw36D110Live7.child04_cover",
      "whole_E0_1LB_child_proof":"BB6.Agent29Raw36D110Live6.child13_cover",
      "parent_theorem":"BB6.Agent29Raw36D110Live6.parent_cover_from_live6",
      "one_new_machine":LITERAL,"new_machine_certificate":["r",6,9,5,1318],
      "candidate_0LE":{"original_open":13,"far":12,"structured":1},
      "candidate_1LB":{"original_open":40,"far":16,"structured":23,"new_r":1},
      "predecessor_source":predecessor["claim"],
      "root_olean_sha256":base.file_sha(last),
      "source_sha256":base.file_sha(HERE/(names[-1][0]+".lean")),
      "axioms":profiles,
    }
    (work/"raw36-d110-e0le-and-1lb-accepted.json").write_text(
      json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print("PASS: all 53 literal OPEN descendants in two branches Lean checked;"
          " 16 cycle + 2 whole E0 children closed, 6 conditional E0 Covers left",flush=True)
if __name__=="__main__":main()
