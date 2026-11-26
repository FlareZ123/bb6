#!/usr/bin/env python3
"""Export exact generated source closures for local Lean work without Git access.

This is a source-only artifact, never an accepted proof. Its module hashes,
revision, dependency graph and root identify what must be checked locally.
"""
import json
from pathlib import Path
import shutil
import sys

ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[1]
sys.path.insert(0,str(REPO/'tools'))
from lean_compile_closure import module_index, resolve_source, parse_imports, sha256_file, git_revision, display_source
from shard_plan import run


def export(child, out):
    if child not in {'LE','LF','RF','LE1','LF1'}:
        raise ValueError('unsupported Raw58 child')
    py=sys.executable
    run(py,REPO/'im-results/agent13-coverage/unpack.py')
    run(py,REPO/'im-results/agent31-three-hole-tnf/generate_sweeps.py')
    run(py,REPO/'im-results/agent31-three-hole-tnf/generate_four_hole.py')
    run(py,ROOT/'generate_more.py',child)
    run(py,REPO/'im-results/agent10-tnf-multipump/chunk_checks.py',ROOT,'Raw58'+child,'--limit','180')
    root=ROOT/f'Raw58{child}Data.lean'
    index=module_index()
    entries={}
    def visit(module,source=None):
        if module in entries:
            return
        source=source or resolve_source(module,index)
        deps=parse_imports(source)
        dest=out/(module.replace('.','/')+'.lean')
        dest.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(source,dest)
        entries[module]={'module':module,'source_path':display_source(source),
                         'bundle_path':str(dest.relative_to(out)),
                         'source_sha256':sha256_file(source),'project_imports':deps}
        for dep in deps:
            visit(dep)
    out.mkdir(parents=True,exist_ok=False)
    visit(root.stem,root)
    manifest={'schema_version':1,'kind':'source-only','proof_source_revision':git_revision(REPO),
              'root':root.stem,'modules':list(entries.values())}
    (out/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print('exported',len(entries),'source modules, root',root.stem,flush=True)


if __name__=='__main__':
    export(sys.argv[1],Path(sys.argv[2]))
