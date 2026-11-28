#!/usr/bin/env python3
"""Original-source consume selected complete E0 branches of Raw36 D1=0RE.

One common generator pass names every FAR/stack producer exactly once,
avoiding identity collisions between the E0=0LE, E0=1LB and optional
E0=0LF candidate families. Every generated witness is rechecked by Lean.
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
    a.add_argument("--zeroLF-search",type=Path)
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
    assert len(child04)==13
    # Authenticate the exact E0=1LB open set against the archived census.
    # Counts may change when the exact source census is regenerated; the
    # invariant is that the targeted hard literal is the sole missing
    # candidate and every other key has a replayable FAR/stack witness.
    keys13={t.replace("_","") for t in census["opens"] if
           t.replace("_","")[24:27]=="1LB"}
    assert hard in keys13
    fixture["data"][j]=["r",6,9,5,1318]
    candidate_rows=[fixture["data"][keys.index(k)] for k in sorted(keys13)]
    assert all(v is not None for v in candidate_rows)
    assert len(keys13-{hard})==len(keys13)-1
    far13=sum(1 for v in candidate_rows if v[0]=="f")
    structured13=len(candidate_rows)-far13
    zeroLF_results=[]
    zeroLF_keys=set()
    if p.zeroLF_search is not None:
        report=json.loads(p.zeroLF_search.read_text())
        assert report["kind"]=="untrusted candidate search, NOT formal Cover"
        assert report["target"]=="Raw36 D1=0RE E0=0LF"
        expected_zeroLF={
          "1RB0LE_1RC1RA_0RD0RB_0LD0RE_0LF0LD_1LA---",
          "1RB0LE_1RC1RA_0RD0RB_0LD0RE_0LF0RD_1LA---",
          "1RB0RB_1RC0RF_0RD0RA_0LD0RE_0LF---_1LB1LE",
          "1RB0RC_1RC0RF_0RD0RA_0LD0RE_0LF---_1LB1LE",
          "1RB1LF_1RC0RF_0RD1RA_0LD0RE_0LF---_1LA0LA",
        }
        assert len(report["results"])==5
        assert {x["table"] for x in report["results"]}==expected_zeroLF
        zeroLF_keys={t for t in keys if t[24:27]=="0LF"}
        assert zeroLF_keys=={t.replace("_","") for t in expected_zeroLF}
        for item in report["results"]:
            table=item["table"].replace("_","")
            assert table in zeroLF_keys
            assert isinstance(item["params"],list) and item["params"]
            assert item["params"][0] in ("r","m","p")
            assert isinstance(item["reachable"],int) and item["reachable"]>0
            idx=keys.index(table)
            assert fixture["data"][idx] is None
            fixture["data"][idx]=item["params"]+[item["reachable"]]
            zeroLF_results.append({"table":item["table"],"certificate":
                                   item["params"]+[item["reachable"]]})
        assert all(fixture["data"][keys.index(t)] is not None for t in zeroLF_keys)
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
    selected_children="4,5,13" if p.zeroLF_search is not None else "4,13"
    subprocess.run([sys.executable,str(generator),str(src),str(work),
       str(fixture_file),"300","10",selected_children],check=True)
    run_lean(work,"Raw36D110Base")
    for name in sorted(x.stem for x in work.glob("Raw36D110Automata*.lean")):
        run_lean(work,name)
    for name in sorted(x.stem for x in work.glob("Raw36D110Sweep*.lean")):
        run_lean(work,name)
    for kid in (("04","05","13") if p.zeroLF_search is not None else ("04","13")):
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
    if p.zeroLF_search is not None:
        names.append(("Raw36D110Live5AfterE0LE1LB0LF","BB6.Agent29Raw36D110Live5.",(
            "child05_identity","child05_cover","live6_from_live5",
            "parent_cover_from_live5","live5_count")))
    profiles={}
    for name,ns,required in names:
        file=HERE/(name+".lean")
        (work/file.name).write_bytes(file.read_bytes())
        compiled=run_lean(work,name)
        profiles.update(check_axioms(compiled,[ns+x for x in required]))
    last=work/(names[-1][0]+".olean")
    include_zeroLF=p.zeroLF_search is not None
    closed=["0LE","1LB"]+(["0LF"] if include_zeroLF else [])
    remaining=(["0RF","1LA","1LE","1LF","1RF"] if include_zeroLF else
               ["0LF","0RF","1LA","1LE","1LF","1RF"])
    parent_theorem=("BB6.Agent29Raw36D110Live5.parent_cover_from_live5" if include_zeroLF
                    else "BB6.Agent29Raw36D110Live6.parent_cover_from_live6")
    receipt={
      "status":"original-source accepted D110 whole-child Covers with "
               +str(len(remaining))+" live E0 obligations",
      "source_revision":subprocess.check_output(["git","rev-parse","HEAD"],
                                     cwd=REPO,text=True).strip(),
      "parent":"1RB---_1RC---_0RD---_0LD0RE_------_------",
      "B":2004,
      "E0_children_closed":closed,
      "E0_ordinary_cycle_children_closed":16,
      "remaining_E0_cover_count":len(remaining),
      "remaining_E0_moves":remaining,
      "whole_E0_0LE_child_proof":"BB6.Agent29Raw36D110Live7.child04_cover",
      "whole_E0_1LB_child_proof":"BB6.Agent29Raw36D110Live6.child13_cover",
      "whole_E0_0LF_child_proof":("BB6.Agent29Raw36D110Live5.child05_cover" if include_zeroLF else None),
      "parent_theorem":parent_theorem,
      "one_new_machine":LITERAL,"new_machine_certificate":["r",6,9,5,1318],
      "candidate_0LE":{"original_open":13,"far":12,"structured":1},
      "candidate_1LB":{"original_open":len(keys13),"far":far13,"structured":structured13,"new_r":1},
      "candidate_0LF":({"original_open":len(zeroLF_keys),"new_nonhalting":len(zeroLF_results),
                        "certificates":zeroLF_results} if include_zeroLF else None),
      "predecessor_source":predecessor["claim"],
      "root_olean_sha256":base.file_sha(last),
      "source_sha256":base.file_sha(HERE/(names[-1][0]+".lean")),
      "axioms":profiles,
    }
    outname=("raw36-d110-e0le-1lb-0lf-accepted.json" if include_zeroLF
             else "raw36-d110-e0le-and-1lb-accepted.json")
    (work/outname).write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print("PASS: all "+str(len(child04)+len(keys13)+len(zeroLF_keys))+" literal OPEN descendants in selected E0 branches Lean checked; "
          +str(len(closed))+" whole E0 children closed, "+str(len(remaining))+" conditional E0 Covers left",flush=True)
if __name__=="__main__":main()
