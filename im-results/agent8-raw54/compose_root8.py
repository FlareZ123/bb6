#!/usr/bin/env python3
"""Merge eight source-accepted Raw54 E1 child proof closures, retaining explicit residuals."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(REPO / 'tools'))
import lean_compile_closure as lc

EXPECTED = {
    '0LE': ('46089155933', 'BB6.Agent8Raw54.e1_complete', 39447,
            '1RB---_1RC---_0RD---_1LD0LE_---0LE_------'),
    '0RA': ('46078961045', 'BB6.Agent8Raw54.E1RA.complete_cover', 27669,
            '1RB---_1RC---_0RD---_1LD0LE_---0RA_------'),
    '0RB': ('46087618052', 'BB6.Agent8Raw54.E1RB.complete_cover', 12634,
            '1RB---_1RC---_0RD---_1LD0LE_---0RB_------'),
    '0RC': ('46088429391', 'BB6.Agent8Raw54.E1RC.complete_cover', 623,
            '1RB---_1RC---_0RD---_1LD0LE_---0RC_------'),
    '0RE': ('45960006400', 'BB6.Agent8Raw54.E1RE.complete_cover', 4076,
            '1RB---_1RC---_0RD---_1LD0LE_---0RE_------'),
    '0RF': ('45960012324', 'BB6.Agent8Raw54.E1RF.complete_cover', 840,
            '1RB---_1RC---_0RD---_1LD0LE_---0RF_------'),
    '1RC': ('46122232071', 'BB6.Agent8Raw54.E1OneRC.complete_cover', 1847,
            '1RB---_1RC---_0RD---_1LD0LE_---1RC_------'),
    '1RE': ('46103257412', 'BB6.Agent8Raw54.E1OneRE.complete_cover', 8212,
            '1RB---_1RC---_0RD---_1LD0LE_---1RE_------'),
}

sha = lc.sha256_file

def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()

def child_file(d, rel):
    p = Path(rel)
    if p.is_absolute() or '..' in p.parts:
        raise ValueError(f'unsafe artifact path: {rel}')
    return d / p

def merge(inputs, out):
    out.mkdir(parents=True, exist_ok=False)
    entries, revisions, base = {}, set(), None
    for label, (run, theorem, bound, parent) in EXPECTED.items():
        paths = list((inputs / label).rglob('manifest.json'))
        assert len(paths) == 1, (label, paths)
        path = paths[0]
        m = json.loads(path.read_text())
        assert m['schema_version'] == 1
        assert m['workflow']['run_id'] == run
        assert m['claim']['theorem'] == theorem
        assert m['claim']['weighted_bound'] == bound
        if bound is not None:
            assert m['claim']['parent_table'] == parent
        if base is None:
            base = m
        else:
            assert m['lean_version'] == base['lean_version']
            assert m['lean_binary']['sha256'] == base['lean_binary']['sha256']
        revisions.update(m['source_revisions'])
        revisions.add(m['proof_source_revision'])
        for e in m['modules']:
            module = e['module']
            rel = module.replace('.', '/')
            src = child_file(path.parent, rel + '.lean')
            obj = child_file(path.parent, e['olean_path'])
            assert sha(src) == e['source_sha256'], module
            assert sha(obj) == e['olean_sha256'], module
            assert lc.parse_imports(src) == e['project_imports'], module
            if module in entries:
                assert entries[module]['module_identity_sha256'] == e['module_identity_sha256'], module
                continue
            entries[module] = e
            for a, b in [(src, child_file(out, rel + '.lean')), (obj, child_file(out, e['olean_path']))]:
                b.parent.mkdir(parents=True, exist_ok=True)
                os.link(a, b)
        print(label, 'accepted modules in union:', len(entries), flush=True)
    for module, e in entries.items():
        deps = [{'module': d, 'identity': entries[d]['module_identity_sha256']}
                for d in sorted(e['project_imports'])]
        assert digest(deps) == e['import_closure_sha256'], module
        identity = {k: e[k] for k in ('module', 'source_sha256', 'project_imports', 'olean_sha256', 'import_closure_sha256')}
        assert digest(identity) == e['module_identity_sha256'], module
    m = dict(base, modules=list(entries.values()), module_count=len(entries),
             source_revisions=sorted(revisions), label='Raw54 eight accepted E1 child union',
             roots=[], claim={'theorem': None, 'parent_table': None, 'weighted_bound': None})
    (out / 'manifest.json').write_text(json.dumps(m, indent=2, sort_keys=True) + '\n')


def main():
    p = argparse.ArgumentParser()
    p.add_argument('inputs', type=Path)
    p.add_argument('merged', type=Path)
    p.add_argument('work', type=Path)
    p.add_argument('--jobs', type=int, default=2)
    args = p.parse_args()
    inputs, merged, work = (v.resolve() for v in (args.inputs, args.merged, args.work))
    merge(inputs, merged)
    for src in merged.rglob('*.lean'):
        module = '.'.join(src.relative_to(merged).with_suffix('').parts)
        lc.OVERRIDES[module] = str(src)
    lc.compile_closure(
        roots=[HERE / 'Raw54RootEightClosed.lean'], workdir=work,
        jobs=args.jobs, lean='lean', extra_source_roots=[merged],
        manifest_path=work / 'manifest.json',
        label='Raw54 eight accepted E1 children, twelve explicit residual premises',
        provenance_inputs=[HERE / 'compose_root8.py',
                           HERE / 'Raw54RootEightCut.lean',
                           HERE / 'Raw54RootEightClosed.lean'],
        theorem='BB6.Agent8Raw54.root_eight_complete_of_twelve',
        parent_table=None, weighted_bound=None,
        artifact_name='raw54-root-eight-conditional-certified',
        precompiled_manifest_path=merged / 'manifest.json',
        precompiled_dir=merged,
    )

if __name__ == '__main__':
    main()
