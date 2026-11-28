#!/usr/bin/env python3
"""Reuse pinned, identity-compatible E1=0LE child objects; rebuild only 1RB."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(REPO / 'tools'))
import lean_compile_closure as lc

EXPECTED = {
    '0LF': ('45900516624', 'BB6.Agent8Raw54.ZeroLF.cover', 1055),
    '0RA': ('45930495327', 'BB6.Agent8Raw54.RA.cover', 363),
    '0RB': ('45902903420', 'BB6.Agent8Raw54.ZeroRB.cover', 390),
    '0RF': ('45901424082', 'BB6.Agent8Raw54.ZeroRF.cover', 402),
    '1LA': ('45914537986', 'BB6.Agent8Raw54.LA.cover', 545),
    '1LB': ('45930495327', 'BB6.Agent8Raw54.complete_cover', 7014),
    '1LF': ('45914537986', 'BB6.Agent8Raw54.LF.complete_cover', 7014),
    '1RA': ('46077702370', 'BB6.Agent8Raw54.OneRA.cover', 39447),
    # RF predates parent-table and bound manifest fields.
    '1RF': ('45869885988', 'BB6.Agent8Raw54.RF.exact_threshold', None),
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
    for label, (run, theorem, bound) in EXPECTED.items():
        paths = list((inputs / label).rglob('manifest.json'))
        assert len(paths) == 1, (label, paths)
        path = paths[0]
        m = json.loads(path.read_text())
        assert m['schema_version'] == 1
        assert m['workflow']['run_id'] == run
        assert m['claim']['theorem'] == theorem
        assert m['claim']['weighted_bound'] == bound
        if bound is not None:
            assert m['claim']['parent_table'] == f'1RB---_1RC---_0RD---_1LD0LE_{label}0LE_------'
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
             source_revisions=sorted(revisions), label='Raw54 E1=0LE accepted child union',
             roots=[], claim={'theorem': None, 'parent_table': None, 'weighted_bound': None})
    (out / 'manifest.json').write_text(json.dumps(m, indent=2, sort_keys=True) + '\n')

def prepare_rb(inputs, out):
    paths = list((inputs / '1RB').rglob('source-export.json'))
    assert len(paths) == 1, paths
    p = paths[0]
    m = json.loads(p.read_text())
    assert m['revision'] == 'bdd87f2fa9569fd70ce09d18358e53367757f07f'
    assert len(m['modules']) == 1045
    out.mkdir(parents=True, exist_ok=False)
    for module, e in m['modules'].items():
        src = child_file(p.parent, e['file'])
        assert sha(src) == e['sha256'], module
        assert lc.parse_imports(src) == e['dependencies'], module
        dst = child_file(out, e['file'])
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, dst)
    subprocess.run([sys.executable, str(HERE / 'shard_rb.py'), '--directory', str(out), '--threshold', '50'], check=True)
    # Identical sparse-row fusion to generate_ra.py:fuse_sparse.
    for data in sorted(out.glob('Raw54RBSparse*Data.lean')):
        mod = data.stem.removesuffix('Data')
        parts = [data, *(out / f'{mod}Row{j:02}.lean' for j in range(12)), out / f'{mod}.lean']
        source = parts[0].read_text()
        for path in parts[1:]:
            source += ''.join(line for line in path.read_text().splitlines(keepends=True) if not line.startswith('import '))
        parts[-1].write_text(source)
        for path in parts[:-1]:
            path.unlink()

def main():
    p = argparse.ArgumentParser()
    p.add_argument('inputs', type=Path)
    p.add_argument('merged', type=Path)
    p.add_argument('work', type=Path)
    p.add_argument('--jobs', type=int, default=2)
    args = p.parse_args()
    inputs, merged, work = (v.resolve() for v in (args.inputs, args.merged, args.work))
    merge(inputs, merged)
    rb = merged.parent / (merged.name + '-rb-source')
    prepare_rb(inputs, rb)
    for src in rb.rglob('*.lean'):
        rel = src.relative_to(rb)
        dst = merged / rel
        if dst.exists():
            assert sha(src) == sha(dst), rel
        else:
            dst.parent.mkdir(parents=True, exist_ok=True)
            os.link(src, dst)
    # Pinned source takes precedence over later same-name repository copies.
    for src in merged.rglob('*.lean'):
        module = '.'.join(src.relative_to(merged).with_suffix('').parts)
        lc.OVERRIDES[module] = str(src)
    lc.compile_closure(
        roots=[HERE / 'Raw54E1LEComplete.lean'], workdir=work,
        jobs=args.jobs, lean='lean', extra_source_roots=[merged],
        manifest_path=work / 'manifest.json', label='Raw54 E1=0LE composed exact threshold',
        provenance_inputs=[HERE / 'compose_e1le.py', HERE / 'shard_rb.py'],
        theorem='BB6.Agent8Raw54.e1_complete',
        parent_table='1RB---_1RC---_0RD---_1LD0LE_---0LE_------',
        weighted_bound=39447, artifact_name='raw54-e1le-complete-certified',
        precompiled_manifest_path=merged / 'manifest.json', precompiled_dir=merged,
    )

if __name__ == '__main__':
    main()
