#!/usr/bin/env python3
"""Relocate the affected import cone of an accepted Lean proof, one module at a time.

The caller must authenticate the producer closure and pinned base before invoking.
No changed object is imported until its selected declarations have passed kernel replay.
"""
import argparse
import concurrent.futures
import hashlib
import heapq
import json
import os
from pathlib import Path
import shutil
import subprocess


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def write_lines(path, lines):
    path.write_text(''.join(str(x) + '\n' for x in lines))


def relocate(*, producer_files, base, work, root_module, root_names, prefix,
             tool, comparator=None, plan_only=False, jobs=1, checkpoint_every=1):
    """Return the root module and staged closure, leaving base untouched."""
    if jobs < 1:
        raise ValueError('jobs must be >= 1')
    if checkpoint_every < 1:
        raise ValueError('checkpoint_every must be >= 1')
    work = work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    base = base.resolve()
    output = work / 'objects'
    output.mkdir()
    logs = work / 'logs'
    logs.mkdir()
    sysroot = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
    env = dict(os.environ, LEAN_SYSROOT=str(sysroot), LEAN_PATH=os.pathsep.join(map(str, [output, base])))
    files = {}
    for p in map(Path, producer_files):
        p = p.resolve()
        assert p.suffix == '.olean' and p.is_file()
        m = p.stem
        if m in files:
            assert sha(p) == sha(files[m]), f'different duplicate producer module {m}'
        else:
            files[m] = p
    assert root_module in files
    index_path = work / 'producer-objects.txt'
    write_lines(index_path, [files[m] for m in sorted(files)])
    raw_index = subprocess.check_output([str(tool), 'index', str(index_path)], env=env, text=True)
    (work / 'module-index.jsonl').write_text(raw_index)
    index = {Path(x['path']).stem: x for x in map(json.loads, raw_index.splitlines())}
    assert set(index) == set(files)
    # Restrict to the actual root's transitive import closure.
    reachable = set()
    order = []
    visiting = set()
    def visit(m):
        if m in reachable:
            return
        if m not in index:
            assert (sysroot / 'lib' / 'lean' / (m.replace('.', '/') + '.olean')).is_file(), f'missing {m}'
            return
        assert m not in visiting, f'cyclic import {m}'
        visiting.add(m)
        for dep in index[m]['imports']:
            visit(dep)
        visiting.remove(m)
        reachable.add(m)
        order.append(m)
    visit(root_module)
    # Mark only conflicting modules and their transitive import consumers.
    affected = set()
    collisions = []
    for m in order:
        p = files[m]
        q = base / p.name
        if q.is_file() and sha(p) != sha(q):
            equal = False
            if comparator is not None:
                proc = subprocess.run(['lean', '--run', str(comparator), str(q), str(p)],
                                      env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                equal = proc.returncode == 0
                (logs / (m + '-compare.log')).write_text(proc.stdout)
            collisions.append({'module': m, 'producer': sha(p), 'base': sha(q), 'kernel_equal': equal})
            if not equal:
                affected.add(m)
        if any(dep in affected for dep in index[m]['imports']):
            affected.add(m)
    if root_module not in affected:
        raise ValueError('root is already import-compatible; use the normal strict linker')
    affected_files = work / 'affected-objects.txt'
    write_lines(affected_files, [files[m] for m in order if m in affected])
    roots = work / 'roots.txt'
    write_lines(roots, root_names)
    relocation = work / 'relocation.txt'
    plan_log = subprocess.check_output([str(tool), 'plan', str(affected_files), str(roots), str(relocation)], env=env, text=True)
    (logs / 'plan.log').write_text(plan_log)
    names = set(relocation.read_text().splitlines())
    assert set(root_names) <= names
    mapping = {m: f'{prefix}Module{i:04d}' for i, m in enumerate(order) if m in affected}
    report = {'root_module': root_module, 'staged_root': mapping[root_module], 'prefix': prefix,
              'root_names': {n: prefix + '.' + n for n in root_names},
              'source_modules': len(order), 'affected_modules': len(affected),
              'selected_declarations': len(names), 'collisions': collisions,
              'stages': [], 'complete': False}
    report_path = work / 'report.json'
    def checkpoint():
        report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    checkpoint()
    if plan_only:
        return report, output, names
    # Unaffected modules cannot import an affected module: affectedness is
    # propagated to every transitive consumer above. Materialize them first so
    # independent affected branches can be replayed concurrently.
    for m in order:
        if m in affected:
            continue
        p = files[m]
        if not (base / p.name).is_file():
            shutil.copy2(p, output / p.name)

    affected_order = [m for m in order if m in affected]
    rank = {m: i for i, m in enumerate(order)}

    def replay_one(m):
        p = files[m]
        staged = mapping[m]
        deps_path = work / (staged + '.imports.txt')
        # Duplicate Init headers are harmless, but preserve order while deduplicating.
        deps = list(dict.fromkeys(mapping.get(x, x) for x in index[m]['imports']))
        write_lines(deps_path, deps)
        object_path = work / (staged + '.objects.txt')
        write_lines(object_path, [p])
        dest = output / (staged + '.olean')
        log_path = logs / (staged + '.log')
        with log_path.open('w') as log:
            subprocess.run([str(tool), str(deps_path), str(relocation), str(object_path),
                            staged, prefix, str(dest)], env=env, stdout=log,
                           stderr=subprocess.STDOUT, check=True)
        log_text = log_path.read_text()
        assert dest.is_file() and 'PASS: saved' in log_text, f'no successful replay {m}'
        record = {'source_module': m, 'stage_module': staged,
                  'source_olean_sha256': sha(p), 'stage_olean_sha256': sha(dest),
                  'log': log_text}
        return record, log_text.strip().splitlines()[-1]

    completed = 0
    def record_stage(record, final_line):
        nonlocal completed
        report['stages'].append(record)
        completed += 1
        if completed % checkpoint_every == 0:
            checkpoint()
        print(record['source_module'], final_line, flush=True)

    if jobs == 1:
        for m in affected_order:
            record_stage(*replay_one(m))
    else:
        # Schedule the affected import DAG. A stage becomes runnable exactly
        # when all of its affected imports have produced their relocated olean.
        pending = {m: {d for d in index[m]['imports'] if d in affected}
                   for m in affected_order}
        children = {m: [] for m in affected_order}
        for m, deps in pending.items():
            for d in deps:
                children[d].append(m)
        ready = [(rank[m], m) for m in affected_order if not pending[m]]
        heapq.heapify(ready)
        active = {}
        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
            while ready or active:
                while ready and len(active) < jobs:
                    _, m = heapq.heappop(ready)
                    active[pool.submit(replay_one, m)] = m
                if not active:
                    raise RuntimeError('affected import DAG stalled')
                done, _ = concurrent.futures.wait(
                    active, return_when=concurrent.futures.FIRST_COMPLETED)
                for future in sorted(done, key=lambda f: rank[active[f]]):
                    m = active.pop(future)
                    record_stage(*future.result())
                    for child in children[m]:
                        pending[child].remove(m)
                        if not pending[child]:
                            heapq.heappush(ready, (rank[child], child))
        assert completed == len(affected_order)

    # Completion-order logging is useful while running; the persisted report is
    # deterministic in original topological order.
    report['stages'].sort(key=lambda x: rank[x['source_module']])
    checkpoint()
    report['complete'] = True
    checkpoint()
    return report, output, names


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--producer-objects', type=Path, required=True)
    p.add_argument('--base', type=Path, required=True)
    p.add_argument('--work', type=Path, required=True)
    p.add_argument('--root-module', required=True)
    p.add_argument('--root-name', action='append', required=True)
    p.add_argument('--prefix', required=True)
    p.add_argument('--tool', type=Path, required=True)
    p.add_argument('--comparator', type=Path)
    p.add_argument('--plan-only', action='store_true')
    p.add_argument('--jobs', type=int, default=1)
    p.add_argument('--checkpoint-every', type=int, default=1)
    a = p.parse_args()
    report, _, _ = relocate(producer_files=a.producer_objects.read_text().splitlines(), base=a.base,
        work=a.work, root_module=a.root_module, root_names=a.root_name, prefix=a.prefix,
        tool=a.tool.resolve(), comparator=a.comparator, plan_only=a.plan_only,
        jobs=a.jobs, checkpoint_every=a.checkpoint_every)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
