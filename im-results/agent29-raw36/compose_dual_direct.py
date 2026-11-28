#!/usr/bin/env python3
"""Source-kernel consume accepted D102 and D114 without blocked D101.

Authenticates original producer manifests and exact overlap identities; no
coercion of distinct kernel declarations and no new mathematical axioms.
"""
import argparse,hashlib,json,os,re,subprocess,sys,zipfile
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
sys.path.insert(0,str(HERE))
import compose_accepted as base
ALLOWED={"propext","Classical.choice","Quot.sound"}
NS="BB6.Agent29Raw36."
NAMES=["d102_same_source","d114_same_source","d102_cover_at",
       "d114_cover_at","parent_cover_from_live7_after02And14",
       "remaining_count","removed_02","removed_14"]
PINS=[
 {"index":"02","run":46135318026,"revision":"432ae5f017782402e77b656aa42f27afd442c6fb",
  "id":15261371812,"artifact":"raw36-d1-02-proof-split16",
  "sha":"11943f96af0282a4e32f44b444ea88e2355915cd0f3bcf52f1f266378d1a187d",
  "root":"Raw36D102","bound":172,"theorem":"BB6.Agent29Raw36D102.cover",
  "table":"1RB---_1RC---_0RD---_0LD0LC_------_------"},
 {"index":"14","run":46136452862,"revision":"48ec4171ab08b4b21ddcdebd328f0061730e23f6",
  "id":15262524140,"artifact":"raw36-d1-14-proof-recovery",
  "sha":"5b88e3a6dae7c7c6c004952b99db95490dfc7f9538c8210c5ea06dc3186a5602",
  "root":"Raw36D114","bound":366,"theorem":"BB6.Agent29Raw36D114.cover",
  "table":"1RB---_1RC---_0RD---_0LD1LC_------_------"},
]

def absorb(pin,archives,work,members,meta):
    arc=archives/(pin["artifact"]+".zip")
    if not arc.is_file():
        with arc.open("wb") as f:
            subprocess.run(["gh","api",f"repos/FlareZ123/bb6/actions/artifacts/{pin['id']}/zip"],
                           stdout=f,check=True)
    assert base.file_sha(arc)==pin["sha"],pin["index"]
    with zipfile.ZipFile(arc) as z:
        doc=json.loads(z.read("manifest.json"))
        assert doc["schema_version"]==1
        assert doc["proof_source_revision"]==doc["workflow"]["workflow_head_sha"]==pin["revision"]
        assert int(doc["workflow"]["run_id"])==pin["run"]
        assert doc["lean_version"]==meta["lean_version"]
        assert doc["lean_binary"]["sha256"]==meta["lean_binary"]["sha256"]
        assert doc["artifact_name"]==pin["artifact"]
        assert doc["claim"]["theorem"]==pin["theorem"]
        assert doc["claim"]["weighted_bound"]==pin["bound"]
        assert doc["claim"]["parent_table"]==pin["table"]
        assert not doc["claim"]["conditional"]
        entries={x["module"]:x for x in doc["modules"]}
        assert len(entries)==doc["module_count"]
        assert any(x["module"]==pin["root"] for x in doc["roots"])
        assert pin["root"] in entries
        collisions=[]
        for name,ent in entries.items():
            if name in members and ent["module_identity_sha256"]!=members[name]["module_identity_sha256"]:
                collisions.append((name,members[name]["module_identity_sha256"],ent["module_identity_sha256"]))
        if collisions:
            (work/(pin["index"]+"-collisions.json")).write_text(
                json.dumps({"producer":pin["artifact"],"conflicts":collisions},indent=2)+"\n")
            raise AssertionError("incompatible imported module declarations: "+repr(collisions[:8]))
        for name,ent in entries.items():
            assert all(dep in entries or dep in members for dep in ent["project_imports"]),(name,ent["project_imports"])
            if name in members:continue
            for ext,key in ((".lean","source_sha256"),(".olean","olean_sha256")):
                f=str(Path(*name.split(".")).with_suffix(ext))
                b=z.read(f)
                assert base.sha(b)==ent[key],(pin["artifact"],f)
                target=work/f
                assert not target.exists(),target
                target.parent.mkdir(parents=True,exist_ok=True)
                target.write_bytes(b)
            members[name]=ent
        print("PASS: accepted",pin["artifact"],"root",pin["root"],
              "dependency modules",len(entries),flush=True)
        return {"run":pin["run"],"artifact_id":pin["id"],"archive_sha256":pin["sha"],
                "root":pin["root"],"root_identity":entries[pin["root"]]["module_identity_sha256"]}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inputs",required=True,type=Path)
    ap.add_argument("--work",required=True,type=Path)
    a=ap.parse_args()
    archives=a.inputs.resolve()
    archives.mkdir(parents=True,exist_ok=True)
    work=a.work.resolve()
    subprocess.run([sys.executable,str(HERE/"compose_accepted.py"),
                    "--inputs",str(archives),"--work",str(work),"--download"],check=True)
    base_meta=json.loads((work/"manifest.json").read_text())
    assert base_meta["claim"]["theorem"]=="BB6.Agent29Raw36.parent_cover_from_nine"
    assert base_meta["claim"]["conditional"]
    members={m["module"]:m for m in base_meta["modules"]}
    attestations=[absorb(p,archives,work,members,base_meta) for p in PINS]
    src=HERE/"Raw36ParentLive7D102D114.lean"
    (work/src.name).write_bytes(src.read_bytes())
    env=dict(os.environ,LEAN_PATH=str(work))
    r=subprocess.run(["lean","-o",src.stem+".olean",src.name],cwd=work,
                     env=env,text=True,capture_output=True)
    (work/"dual-source.log").write_text(r.stdout+"\n"+r.stderr)
    print(r.stdout,flush=True)
    if r.returncode:
        print(r.stderr,file=sys.stderr,flush=True)
        raise RuntimeError("Lean source compilation failed: "+str(r.returncode))
    assert not re.search(r"sorryAx|native_decide",r.stdout+r.stderr)
    observed=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",r.stdout))
    assert set(observed)=={NS+n for n in NAMES},observed
    assert all(set(x.strip() for x in v.split(",") if x.strip())<=ALLOWED
               for v in observed.values()),observed
    receipt={
      "status":"source-checked Raw36 D102+D114 independent nine-to-seven reduction",
      "source_revision":subprocess.check_output(["git","rev-parse","HEAD"],
                                 cwd=REPO,text=True).strip(),
      "accepted_parents":attestations,
      "source_sha256":base.file_sha(src),
      "root_olean_sha256":base.file_sha(work/(src.stem+".olean")),
      "remaining_cover_count":7,
      "remaining_d1":["0LA","1LA","0LB","0LE","0RE","1LE","1RE"],
      "theorem":NS+"parent_cover_from_live7_after02And14",
      "axioms":observed,
    }
    (work/"raw36-live7-after-d102-d114.json").write_text(
       json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print("PASS: original-source accepted 9->7 Raw36 D1 parents",flush=True)

if __name__=="__main__":main()
