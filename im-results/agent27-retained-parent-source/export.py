#!/usr/bin/env python3
"""Export exact generated source of the retained Raw106 cylinder for local Lean compilation.
The export is not a certificate; the original audit terms must all kernel-check.
"""
import json
from pathlib import Path
import shutil
import subprocess
import sys

REPO=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(REPO/'tools'))
from lean_compile_closure import module_index, resolve_source, parse_imports, sha256_file, git_revision, display_source

def run(*args):
    subprocess.run([str(x) for x in args],cwd=REPO,check=True)

def export(raw,out):
    if raw not in {"67","79","106"}:
        raise ValueError("Unsupported retained parent")
    py=sys.executable
    root=REPO/'im-results/agent10-tnf-multipump'
    run(py,REPO/'im-results/agent13-coverage/unpack.py')
    run(py,root/'generate.py',raw)
    run(py,root/'chunk_checks.py',root,'Raw'+raw,'--limit','96')
    source=root/f'Raw{raw}Data.lean'
    index=module_index()
    entries={}
    def visit(module,path=None):
        if module in entries:
            return
        path=path or resolve_source(module,index)
        deps=parse_imports(path)
        dst=out/(module.replace('.','/')+'.lean')
        dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(path,dst)
        entries[module]={'module':module,'source_path':display_source(path),
                         'bundle_path':str(dst.relative_to(out)),
                         'source_sha256':sha256_file(path),'project_imports':deps}
        for dep in deps:visit(dep)
    out.mkdir(parents=True,exist_ok=False)
    visit(source.stem,source)
    manifest={'schema_version':1,'kind':'source-only',
        'proof_source_revision':git_revision(REPO),'root':source.stem,
        'modules':list(entries.values())}
    (out/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print('exported',len(entries),'source modules, root',source.stem,flush=True)

if __name__=='__main__':
    export(sys.argv[1],Path(sys.argv[2]))
