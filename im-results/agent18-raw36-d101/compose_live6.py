#!/usr/bin/env python3
"""Consume an accepted Raw36 D1=0LB Cover into the accepted D102+D114 live-seven chain."""
import argparse,hashlib,json,os,re,subprocess,sys,zipfile
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
ALLOWED={"propext","Classical.choice","Quot.sound"}
NS="BB6.Agent18Raw36."
NAMES=["d101_same_source","d101_cover_at",
       "parent_cover_from_live6_after01_02_14","after01_02_14_count"]

def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()

def file_sha(p):
    with Path(p).open("rb") as f:
        return hashlib.file_digest(f,"sha256").hexdigest()

def artifact_for_run(run_id):
    raw=subprocess.check_output([
        "gh","api",f"repos/FlareZ123/bb6/actions/runs/{run_id}/artifacts?per_page=100"
    ],text=True)
    xs=json.loads(raw)["artifacts"]
    xs=[a for a in xs if a["name"]=="raw36-direct01-original-cover450" and not a["expired"]]
    assert len(xs)==1,("expected one live D101 artifact",run_id,
                      [(a["id"],a["name"],a["expired"]) for a in xs])
    return xs[0]

def absorb_d101(run_id,archives,work):
    art=artifact_for_run(run_id)
    arc=archives/"raw36-direct01-original-cover450.zip"
    with arc.open("wb") as f:
        subprocess.run(["gh","api",f"repos/FlareZ123/bb6/actions/artifacts/{art['id']}/zip"],
                       stdout=f,check=True)
    with zipfile.ZipFile(arc) as z:
        doc=json.loads(z.read("manifest.json"))
        assert doc["schema_version"]==1
        assert int(doc["workflow"]["run_id"])==run_id
        assert doc["artifact_name"]=="raw36-direct01-original-cover450"
        assert doc["claim"]["theorem"]=="BB6.Agent29Raw36D101.cover"
        assert doc["claim"]["weighted_bound"]==450
        assert doc["claim"]["parent_table"]=="1RB---_1RC---_0RD---_0LD0LB_------_------"
        assert not doc["claim"]["conditional"]
        entries={x["module"]:x for x in doc["modules"]}
        assert "Raw36D101" in entries
        assert any(x["module"]=="Raw36D101" for x in doc["roots"])
        for name,ent in entries.items():
            for ext,key in ((".lean","source_sha256"),(".olean","olean_sha256")):
                rel=str(Path(*name.split(".")).with_suffix(ext))
                data=z.read(rel)
                assert sha_bytes(data)==ent[key],(name,ext,"archive digest")
                dst=work/rel
                if dst.exists():
                    assert file_sha(dst)==ent[key],(name,ext,"identity collision")
                else:
                    dst.parent.mkdir(parents=True,exist_ok=True)
                    dst.write_bytes(data)
        return {
            "run_id":run_id,
            "artifact_id":art["id"],
            "artifact_name":art["name"],
            "archive_sha256":file_sha(arc),
            "root_identity":entries["Raw36D101"]["module_identity_sha256"],
            "proof_source_revision":doc["proof_source_revision"],
        }

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--d101-run",required=True,type=int)
    ap.add_argument("--inputs",required=True,type=Path)
    ap.add_argument("--work",required=True,type=Path)
    a=ap.parse_args()
    archives=a.inputs.resolve(); archives.mkdir(parents=True,exist_ok=True)
    work=a.work.resolve()

    subprocess.run([sys.executable,str(HERE.parent/"agent29-raw36"/"compose_dual_direct.py"),
                    "--inputs",str(archives),"--work",str(work)],check=True)

    d101=absorb_d101(a.d101_run,archives,work)
    src=HERE.parent/"agent18-raw36-d101"/"Raw36ParentLive6D101.lean"
    target=work/src.name
    target.write_bytes(src.read_bytes())

    env=dict(os.environ,LEAN_PATH=str(work))
    r=subprocess.run(["lean","-o",src.stem+".olean",src.name],
                     cwd=work,env=env,text=True,capture_output=True)
    (work/"d101-live6-source.log").write_text(r.stdout+"\n"+r.stderr)
    print(r.stdout,flush=True)
    if r.returncode:
        print(r.stderr,file=sys.stderr,flush=True)
        raise RuntimeError("Lean live-six source compilation failed: "+str(r.returncode))
    assert not re.search(r"sorryAx|native_decide",r.stdout+r.stderr)
    observed=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",r.stdout))
    assert set(observed)=={NS+n for n in NAMES},observed
    assert all(set(x.strip() for x in v.split(",") if x.strip())<=ALLOWED
               for v in observed.values()),observed

    prior=json.loads((work/"raw36-live7-after-d102-d114.json").read_text())
    receipt={
      "status":"source-checked Raw36 D101 consumption after accepted D102+D114",
      "source_revision":subprocess.check_output(["git","rev-parse","HEAD"],
                                               cwd=REPO,text=True).strip(),
      "d101":d101,
      "prior_live7":prior,
      "source_sha256":file_sha(src),
      "root_olean_sha256":file_sha(work/(src.stem+".olean")),
      "remaining_cover_count":6,
      "remaining_d1":["0LA","1LA","0LE","0RE","1LE","1RE"],
      "theorem":NS+"parent_cover_from_live6_after01_02_14",
      "axioms":observed,
    }
    (work/"raw36-live6-after-d101.json").write_text(
        json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print("PASS: accepted Raw36 direct D101 consumed; live direct premises 7 -> 6",flush=True)

if __name__=="__main__":
    main()
