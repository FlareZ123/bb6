"""Compile independent leaf modules, then join the exact generated Lean DAG."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def digest(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def graph(source):
    files = {p.stem: p for p in source.glob('*.lean')}
    imports = {k: {m for line in p.read_text().splitlines()
                   if line.startswith('import ') for m in line.split()[1:]}
               for k, p in files.items()}
    deps = {k: v & files.keys() for k, v in imports.items()}
    return files, imports, deps


def partition(files, deps, groups):
    bins = [[] for _ in range(groups)]
    costs = [0] * groups
    for name in sorted((k for k in files if not deps[k]),
                       key=lambda k: (-files[k].stat().st_size, k)):
        g = min(range(groups), key=lambda i: (costs[i], i))
        bins[g].append(name)
        costs[g] += files[name].stat().st_size
    return bins, costs


def compile_one(name, files, base, out):
    src = files[name]
    target = out / (name + '.olean')
    log = out / (name + '.log')
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, (out, base))))
    print('compile', name, flush=True)
    with log.open('w') as f:
        result = subprocess.run(['lean', '-j1', '-o', str(target), src.name],
                                cwd=src.parent, env=env, stdout=f, stderr=subprocess.STDOUT)
    s = log.read_text()
    if result.returncode or re.search(r'sorryAx|native_decide', s):
        print(s[-12000:], flush=True)
        raise RuntimeError(f'Lean check failed: {name}')
    reports = [line for line in s.splitlines() if 'depends on axioms:' in line or 'does not depend on any axioms' in line]
    if not reports:
        raise RuntimeError(f'No axiom report: {name}')
    print('\n'.join(reports), flush=True)
    return {'source': digest(src), 'olean': digest(target), 'axioms': reports}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('mode', choices=['plan', 'leaf', 'join'])
    p.add_argument('source', type=Path)
    p.add_argument('base', type=Path)
    p.add_argument('out', type=Path)
    p.add_argument('--groups', type=int, default=8)
    p.add_argument('--group', type=int, default=0)
    a = p.parse_args()
    a.source, a.base, a.out = (x.resolve() for x in (a.source, a.base, a.out))
    files, imports, deps = graph(a.source)
    assert files and a.groups > 0
    for external in set().union(*imports.values()) - files.keys():
        assert (a.base / (external.replace('.', '/') + '.olean')).is_file(), external
    bins, costs = partition(files, deps, a.groups)
    if a.mode == 'plan':
        print(json.dumps({'modules': len(files), 'leaves': [len(b) for b in bins], 'bytes': costs}, indent=2))
        return
    a.out.mkdir(parents=True, exist_ok=True)
    if a.mode == 'leaf':
        assert 0 <= a.group < a.groups
        receipt = {}
        for name in bins[a.group]:
            receipt[name] = compile_one(name, files, a.base, a.out)
            (a.out / f'receipt-{a.group}.json').write_text(json.dumps(receipt, indent=2)+'\n')
        if not receipt:
            (a.out / f'receipt-{a.group}.json').write_text('{}\n')
        return
    done = set()
    receipt = {}
    for g, names in enumerate(bins):
        obj = json.loads((a.out / f'receipt-{g}.json').read_text())
        assert set(obj) == set(names), f'incomplete leaf shard {g}'
        for name, item in obj.items():
            assert item['source'] == digest(files[name]), name
            assert item['olean'] == digest(a.out / (name+'.olean')), name
            assert item['axioms'] and not re.search(r'sorryAx|native_decide', '\n'.join(item['axioms'])), name
            done.add(name)
            receipt[name] = item
    while done != files.keys():
        ready = sorted(k for k in files.keys()-done if deps[k] <= done)
        assert ready, 'cycle or missing dependency'
        for name in ready:
            receipt[name] = compile_one(name, files, a.base, a.out)
            done.add(name)
            (a.out / 'join-receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    assert len(receipt) == len(files)
    print('compiled exact parent DAG', len(done), flush=True)


if __name__ == '__main__':
    main()
