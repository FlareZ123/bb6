"""Build a source/object identity manifest for an already kernel-compiled Lean root closure."""
import argparse, hashlib, json, os, re, subprocess
from pathlib import Path

LEAN_SHA256="db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00"

def file_sha(p):
    with Path(p).open("rb") as f: return hashlib.file_digest(f,"sha256").hexdigest()
def sha(b): return hashlib.sha256(b).hexdigest()
def canonical(x): return json.dumps(x,sort_keys=True,separators=(",",":")).encode()
def path_for(work,name,suffix): return work/Path(*name.split(".")).with_suffix(suffix)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work",type=Path,required=True)
    ap.add_argument("--root",required=True)
    ap.add_argument("--label",required=True)
    ap.add_argument("--artifact-name",required=True)
    ap.add_argument("--theorem",required=True)
    ap.add_argument("--bound",type=int,required=True)
    ap.add_argument("--parent-table",required=True)
    ap.add_argument("--provenance",action="append",default=[])
    ap.add_argument("--lean",default="lean")
    a=ap.parse_args()
    version=subprocess.check_output([a.lean,"--version"],text=True).strip()
    compiler=Path(subprocess.check_output([a.lean,"--print-prefix"],text=True).strip())/"bin/lean"
    assert file_sha(compiler)==LEAN_SHA256
    members={}; visiting=set()
    def visit(name):
        if name in members:return
        assert name not in visiting,name
        visiting.add(name)
        src=path_for(a.work,name,".lean"); obj=path_for(a.work,name,".olean")
        assert src.is_file() and obj.is_file(),(name,src,obj)
        imports=re.findall(r"^import ([A-Za-z0-9_.]+)$",src.read_text(),re.M)
        project=[]
        for dep in imports:
            if path_for(a.work,dep,".lean").is_file():
                visit(dep); project.append(dep)
        deps=[{"module":d,"identity":members[d]["module_identity_sha256"]} for d in sorted(project)]
        imp=sha(canonical(deps))
        entry={"module":name,"source_path":"artifact/"+str(src.relative_to(a.work)),
               "source_kind":"exact-source-closure","source_sha256":file_sha(src),
               "project_imports":project,"olean_path":str(obj.relative_to(a.work)),
               "olean_sha256":file_sha(obj),"import_closure_sha256":imp}
        payload={k:entry[k] for k in ("module","source_sha256","project_imports","olean_sha256")}
        payload["import_closure_sha256"]=imp
        entry["module_identity_sha256"]=sha(canonical(payload))
        members[name]=entry; visiting.remove(name)
    visit(a.root)
    rev=os.environ.get("GITHUB_SHA"); run=os.environ.get("GITHUB_RUN_ID")
    assert rev and run
    root=members[a.root]
    out={"schema_version":1,"label":a.label,"artifact_name":a.artifact_name,
         "proof_source_revision":rev,"source_revisions":[rev],
         "workflow":{"run_id":run,"workflow_head_sha":rev},
         "lean_version":version,"lean_binary":{"path":str(compiler),"sha256":file_sha(compiler)},
         "claim":{"theorem":a.theorem,"weighted_bound":a.bound,"parent_table":a.parent_table,"conditional":False},
         "roots":[{k:root[k] for k in ("module","source_path","source_sha256")}],
         "module_count":len(members),"modules":[members[k] for k in sorted(members)],
         "provenance_inputs":[{"description":p} for p in a.provenance],"precompiled_core":None}
    (a.work/"manifest.json").write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print("manifest closure modules:",len(members),flush=True)
if __name__=="__main__": main()
