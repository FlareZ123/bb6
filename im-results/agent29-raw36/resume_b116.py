"""Resume the exact Raw36 B1=1LE source closure from its timed-out proof artifact.

The source run 46097780398 compiled every dependency and child 00--22 before the
150-minute cutoff. Its artifact retained the exact source/object closure plus
Kid23 and the final root sources. This script verifies that archive, compiles only
those two missing modules with the pinned Lean binary, and emits a complete
identity manifest suitable for the normal accepted-object composer.
"""
import argparse, hashlib, json, os, re, subprocess, zipfile
from pathlib import Path

PARTIAL_SHA256 = "3c33df85c78cd8cdfdaa500e0214506102bbf28e4ccbcf26e294ddf5f254e8f1"
PARTIAL_ARTIFACT = 15248908350
PARTIAL_RUN = 46097780398
PARTIAL_REVISION = "9d3e9d52a6c1e6ee04a67604fdd7f1acb29fda56"
LEAN_SHA256 = "db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def file_sha(path):
    with Path(path).open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()

def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()

def sha(data):
    return hashlib.sha256(data).hexdigest()

def module_path(work, name, suffix):
    return work / Path(*name.split(".")).with_suffix(suffix)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--partial-zip", type=Path, required=True)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--lean", default="lean")
    args=ap.parse_args()
    assert file_sha(args.partial_zip) == PARTIAL_SHA256
    args.work.mkdir(parents=True, exist_ok=False)
    with zipfile.ZipFile(args.partial_zip) as z:
        for info in z.infolist():
            p=Path(info.filename)
            assert not p.is_absolute() and ".." not in p.parts
        z.extractall(args.work)
    assert not (args.work/"Raw36B116Kid23.olean").exists()
    assert not (args.work/"Raw36B116.olean").exists()

    version=subprocess.check_output([args.lean,"--version"],text=True).strip()
    compiler=Path(subprocess.check_output([args.lean,"--print-prefix"],text=True).strip())/"bin/lean"
    assert file_sha(compiler) == LEAN_SHA256
    env=dict(os.environ, LEAN_PATH=str(args.work))
    logs=[]
    for name in ("Raw36B116Kid23","Raw36B116"):
        proc=subprocess.run([args.lean,"-o",name+".olean",name+".lean"],
            cwd=args.work,env=env,text=True,capture_output=True)
        out=proc.stdout+proc.stderr
        print(out,end="",flush=True)
        logs.append(out)
        if proc.returncode:
            raise SystemExit(proc.returncode)
    joined="".join(logs)
    ax=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",joined)
    found={name.rsplit(".",1)[-1] for name,_ in ax}
    assert {"kid23_bound","bound","cover"} <= found, found
    assert all({x.strip() for x in vals.split(",") if x.strip()} <= AXIOMS for _,vals in ax)

    members={}
    visiting=set()
    def visit(name):
        if name in members: return
        assert name not in visiting
        visiting.add(name)
        src=module_path(args.work,name,".lean")
        obj=module_path(args.work,name,".olean")
        assert src.is_file() and obj.is_file(), (name,src,obj)
        imports=re.findall(r"^import ([A-Za-z0-9_.]+)$",src.read_text(),re.M)
        project=[]
        for dep in imports:
            if module_path(args.work,dep,".lean").is_file():
                visit(dep); project.append(dep)
        deps=[{"module":d,"identity":members[d]["module_identity_sha256"]} for d in sorted(project)]
        imp=sha(canonical(deps))
        entry={
          "module":name,
          "source_path":"resumed-partial/"+str(src.relative_to(args.work)),
          "source_kind":"verified-partial-artifact",
          "source_sha256":file_sha(src),
          "project_imports":project,
          "olean_path":str(obj.relative_to(args.work)),
          "olean_sha256":file_sha(obj),
          "import_closure_sha256":imp,
        }
        payload={k:entry[k] for k in ("module","source_sha256","project_imports","olean_sha256")}
        payload["import_closure_sha256"]=imp
        entry["module_identity_sha256"]=sha(canonical(payload))
        members[name]=entry
        visiting.remove(name)
    visit("Raw36B116")

    rev=os.environ.get("GITHUB_SHA")
    run=os.environ.get("GITHUB_RUN_ID")
    assert rev and run
    root=members["Raw36B116"]
    manifest={
      "schema_version":1,
      "label":"raw36-b1-16-resumed",
      "artifact_name":"raw36-b1-16-resumed-proof",
      "proof_source_revision":rev,
      "source_revisions":sorted({rev,PARTIAL_REVISION}),
      "workflow":{"run_id":run,"workflow_head_sha":rev},
      "lean_version":version,
      "lean_binary":{"path":str(compiler),"sha256":file_sha(compiler)},
      "claim":{"theorem":"BB6.Agent29Raw36B116.cover","weighted_bound":387,
               "parent_table":"1RB---_1RC1LE_0RD---_0LD1LB_------_------",
               "conditional":False},
      "roots":[{k:root[k] for k in ("module","source_path","source_sha256")}],
      "module_count":len(members),
      "modules":[members[k] for k in sorted(members)],
      "provenance_inputs":[
        {"artifact_id":PARTIAL_ARTIFACT,"run_id":PARTIAL_RUN,
         "revision":PARTIAL_REVISION,"sha256":PARTIAL_SHA256}
      ],
      "precompiled_core":None,
    }
    (args.work/"manifest.json").write_text(json.dumps(manifest,indent=2,sort_keys=True)+"\n")
    print("resumed closure modules:",len(members),flush=True)

if __name__=="__main__":
    main()
