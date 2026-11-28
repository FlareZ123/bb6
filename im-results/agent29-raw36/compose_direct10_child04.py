#!/usr/bin/env python3
"""Kernel-check complete Raw36 D1=0RE / E0=0LE branch after 12 FAR + 1 stack.

The exact archived 2638-table census and independent FAR + structured
candidate banks select certificates. Their truth is *not trusted*; all
selected witnesses and the full source parent Cover must recompile in
Lean 4.36.0-rc2 on the authenticated accepted Raw36 dependency closure.
"""
import argparse,base64,gzip,hashlib,json,lzma,os,re,subprocess,sys
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
sys.path.insert(0,str(HERE))
import compose_accepted as base
NS="BB6.Agent29Raw36D110Live7."
PARENT="1RB---_1RC---_0RD---_0LD0RE_------_------"
REQUIRED=["child04_identity","child04_cover","live8_from_live7",
          "parent_cover_from_live7","live7_count"]
ALLOWED={"propext","Classical.choice","Quot.sound"}
def normalized(t):
    raw=t.replace("_","")
    assert len(raw)==36,t
    return raw
def hash_lines(xs):
    return hashlib.sha256("\n".join(sorted(xs)).encode()).hexdigest()
def read_parent_banks(a):
    census=json.loads(gzip.decompress(a.census.read_bytes()))
    assert census["parent"]==PARENT and census["stats"]["open"]==2638
    assert census["stats"]["score"]==2004 and census["cut"]==5
    assert census["tree"][0]=="split" and census["tree"][2]==8
    keys=sorted(normalized(t) for t in census["opens"])
    assert len(keys)==len(set(keys))==2638
    orig={normalized(k) for k in census["opens"]}
    far={}
    for line in a.far.read_text().splitlines():
        if not line.strip():continue
        k,v=line.split()
        k=normalized(k)
        assert k in orig and k not in far
        far[k]=["f",v]
    assert len(far)==1705
    struct={}
    for k,v in json.loads(a.structured.read_text()):
        k=normalized(k)
        assert k in orig and k not in struct and k not in far
        assert isinstance(v,list) and v and v[0] in ("r","m","p"),(k,v)
        struct[k]=v
    assert len(struct)==809
    missing=orig-set(far)-set(struct)
    assert len(missing)==124
    target={k for k in orig if k[24:27]=="0LE"}
    assert len(target)==13 and not (target&missing)
    assert len(target&set(far))==12 and len(target&set(struct))==1
    data=[far.get(k,struct.get(k)) for k in keys]
    fixture={"digest":hash_lines(keys),"data":data,"bound":2004}
    return census,fixture,target

def run_lean(work,name):
    env=dict(os.environ,LEAN_PATH=str(work))
    source=work/(name+".lean")
    assert source.is_file(),source
    r=subprocess.run(["lean","-o",name+".olean",name+".lean"],
                     cwd=work,env=env,text=True,capture_output=True)
    with (work/"direct10-source-build.log").open("a") as f:
        f.write("### "+name+"\n"+r.stdout+r.stderr+"\n")
    print("COMPILE",name,"returncode",r.returncode,flush=True)
    if r.stdout:print(r.stdout[-11000:],flush=True)
    if r.returncode:
        print(r.stderr[-13000:],file=sys.stderr,flush=True)
        raise RuntimeError("source Lean rejected "+name)
    assert "sorryAx" not in r.stdout+r.stderr
    return r.stdout

def check_axioms(stdout,needed):
    observed=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",stdout))
    observed.update({n:"" for n in re.findall(
       r"'([^']+)' does not depend on any axioms",stdout)})
    assert set(observed)==set(needed),observed
    assert all(set(x.strip() for x in v.split(",") if x.strip())<=ALLOWED
               for v in observed.values()),observed
    assert "sorryAx" not in stdout and "native_decide" not in stdout
    return observed

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ("census","far","structured","archives","work"):
        p.add_argument("--"+name,required=True,type=Path)
    a=p.parse_args()
    work=a.work.resolve()
    stage=work.with_name(work.name+"-inputs")
    stage.mkdir(parents=True,exist_ok=False)
    a.archives.resolve().mkdir(parents=True,exist_ok=True)
    census,fixture,target=read_parent_banks(a)
    fixture_file=stage/"direct10-accepted-candidate-bank.xz.b64"
    fixture_file.write_text(base64.b64encode(lzma.compress(
        json.dumps(fixture,separators=(",",":")).encode())).decode()+"\n")
    sourcefile=stage/"direct10-original-census.json"
    sourcefile.write_text(json.dumps(census,separators=(",",":"))+"\n")
    # At this point the 13 target-table witnesses are *candidates*.
    # Reconstruct the original trusted predecessor and recheck each proof.
    subprocess.run([sys.executable,str(HERE/"compose_accepted.py"),
       "--inputs",str(a.archives.resolve()),
       "--work",str(work),"--download"],check=True)
    predecessor=json.loads((work/"manifest.json").read_text())
    assert predecessor["claim"]["theorem"]=="BB6.Agent29Raw36.parent_cover_from_nine"
    srcgen=REPO/"im-results/agent7-raw36-direct/generate_direct.py"
    subprocess.run([sys.executable,str(srcgen),str(sourcefile),str(work),
                   str(fixture_file),"300","10","4"],check=True)
    # All generated source objects are recompiled under unchanged imports.
    run_lean(work,"Raw36D110Base")
    for name in sorted(x.stem for x in work.glob("Raw36D110Automata*.lean")):
        run_lean(work,name)
    for name in sorted(x.stem for x in work.glob("Raw36D110Sweep*.lean")):
        run_lean(work,name)
    kid=run_lean(work,"Raw36D110Kid04")
    check_axioms(kid,["BB6.Agent29Raw36D110.kid04_bound"])
    # Re-run the parent 16-side-cycle source kernel proof in the same
    # environment, even if it passed in a separate workflow execution.
    emit=HERE/"emit_direct10_eight.py"
    subprocess.run([sys.executable,str(emit),"--census",str(a.census.resolve()),
       "--source",str(work/"Raw36D110Live8.lean"),
       "--summary",str(work/"direct10-live8-source.json")],check=True)
    live8=run_lean(work,"Raw36D110Live8")
    check_axioms(live8,["BB6.Agent29Raw36D110Live8."+x for x in (
        "parent_root","parent_nohalt","parent_query","haltChild",
        "ordinaryExact","liveComplete","cycleCover",
        "parent_cover_from_live8","live_count")])
    consumer=HERE/"Raw36D110Live7AfterE0LE.lean"
    (work/consumer.name).write_bytes(consumer.read_bytes())
    accepted=run_lean(work,consumer.stem)
    profile=check_axioms(accepted,[NS+x for x in REQUIRED])
    report={
      "status":"original-source accepted full E0=0LE six-hole Cover and D1=0RE seven-live interface",
      "source_revision":subprocess.check_output(["git","rev-parse","HEAD"],cwd=REPO,text=True).strip(),
      "parent":PARENT,"threshold":2004,"selected_E0":"0LE",
      "target_open_literals":13,"FAR_witnesses":12,"structured_witnesses":1,
      "remaining_e0_actions":["0LF","0RF","1LA","1LB","1LE","1LF","1RF"],
      "remaining_e0_cover_count":7,
      "raw_evidence_sha256":hashlib.sha256(a.census.read_bytes()).hexdigest(),
      "target_literal_sha256":hash_lines(target),
      "consumer_theorem":NS+"parent_cover_from_live7",
      "whole_child_theorem":NS+"child04_cover",
      "parent_provenance":predecessor["claim"],
      "source_sha256":base.file_sha(consumer),
      "root_olean_sha256":base.file_sha(work/(consumer.stem+".olean")),
      "axioms":profile,
    }
    (work/"raw36-d110-e0le-accepted.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print("PASS: all 13 D1=0RE E0=0LE literal leaves kernel-checked; "
          "8->7 live E0 Cover obligations",flush=True)

if __name__=="__main__":main()
