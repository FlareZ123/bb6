#!/usr/bin/env python3
"""Source-rebuild a checked Raw59 artifact with its modern width-two API isolated."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

RENAME = {name: 'Raw59Modern' + name for name in (
    'BlockMacro2', 'BlockFAR2', 'MaskBlockFAR2', 'RangeCheck2',
    'OffsetBlockFAR2', 'BlockFARBridge2',
)}
OLD_NAMESPACE = 'BB6BlockFAR2'
NEW_NAMESPACE = 'BB6Raw59ModernBlockFAR2'
STANDARD = ('Lean', 'Init', 'Std', 'Batteries', 'Mathlib')
IMPORT = re.compile(r'^(\s*(?:(?:public|meta)\s+)*import\s+)(.+?)\s*$', re.M)
RENAME_IMPORT = re.compile(r'^([ \t]*(?:(?:public|meta)[ \t]+)*import[ \t]+)([^\r\n]+)', re.M)
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path: Path) -> str:
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def digest(value: object) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def standard(name: str) -> bool:
    return any(name == x or name.startswith(x + '.') for x in STANDARD)


def imports(text: str) -> list[str]:
    return [x for m in IMPORT.finditer(text) for x in m.group(2).split() if not standard(x)]


def rename_source(text: str) -> str:
    text = re.sub(r'\b' + OLD_NAMESPACE + r'\b', NEW_NAMESPACE, text)
    return RENAME_IMPORT.sub(lambda m: m.group(1) + re.sub(r'\b[A-Za-z0-9_]+\b', lambda t: RENAME.get(t.group(0), t.group(0)), m.group(2)), text)


def topological(entries: dict) -> list[str]:
    order: list[str] = []
    active: set[str] = set()
    done: set[str] = set()

    def visit(name: str) -> None:
        if name in done:
            return
        if name in active:
            raise ValueError(f'cyclic imports at {name}')
        if name not in entries:
            raise ValueError(f'missing project import {name}')
        active.add(name)
        for dep in entries[name]['project_imports']:
            visit(dep)
        active.remove(name)
        done.add(name)
        order.append(name)

    for name in sorted(entries):
        visit(name)
    return order


def identities(entries: dict, order: list[str]) -> None:
    for name in order:
        entry = entries[name]
        dependencies = [{'module': dep, 'identity': entries[dep]['module_identity_sha256']}
                        for dep in sorted(entry['project_imports'])]
        entry['import_closure_sha256'] = digest(dependencies)
        entry['module_identity_sha256'] = digest({key: entry[key] for key in (
            'module', 'source_sha256', 'project_imports', 'olean_sha256', 'import_closure_sha256',
        )})


def check_axioms(log: str, required: list[str]) -> dict[str, list[str]]:
    profiles = {name: set(axioms.split(', ')) if axioms else set()
                for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)}
    profiles.update({name: set() for name in re.findall(r"'([^']+)' does not depend on any axioms", log)})
    for name in required:
        if name not in profiles:
            raise ValueError(f'missing axiom profile {name}')
    for name, axioms in profiles.items():
        if axioms - ALLOWED_AXIOMS:
            raise ValueError(f'unapproved axioms for {name}: {sorted(axioms - ALLOWED_AXIOMS)}')
    return {name: sorted(axioms) for name, axioms in profiles.items()}


def run(source: Path, output: Path, lean: str, jobs: int, claims: list[str], plan_only: bool, kernel_replay: bool = False) -> dict:
    manifest_path = source / 'manifest.json'
    manifest = json.loads(manifest_path.read_text())
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    compiler = Path(subprocess.check_output([lean, '--print-prefix'], text=True).strip()) / 'bin/lean'
    if manifest['schema_version'] != 1 or manifest['lean_version'] != version or manifest['lean_binary']['sha256'] != sha(compiler):
        raise ValueError('source manifest/compiler mismatch')
    original = {e['module']: e for e in manifest['modules']}
    if len(original) != len(manifest['modules']) or len(original) != manifest['module_count']:
        raise ValueError('duplicate or inconsistent module manifest')
    if any(not re.fullmatch(r'[A-Za-z0-9_]+', name) for name in original):
        raise ValueError('expected flat, simple project module names')
    if set(original) & set(RENAME.values()):
        raise ValueError('isolation output module names already exist in producer')
    order = topological(original)
    identity_copy = {name: dict(e) for name, e in original.items()}
    identities(identity_copy, order)
    transformed: dict[str, str] = {}
    affected: set[str] = set()
    direct: set[str] = set()
    for name in order:
        entry = original[name]
        src = source / (name + '.lean')
        obj = source / (name + '.olean')
        if entry['olean_path'] != name + '.olean' or sha(src) != entry['source_sha256'] or sha(obj) != entry['olean_sha256']:
            raise ValueError(f'producer source or object hash mismatch: {name}')
        for key in ('import_closure_sha256', 'module_identity_sha256'):
            if entry[key] != identity_copy[name][key]:
                raise ValueError(f'producer identity mismatch: {name} {key}')
        text = src.read_text()
        if imports(text) != entry['project_imports']:
            raise ValueError(f'producer import manifest mismatch: {name}')
        new_text = rename_source(text)
        transformed[name] = new_text
        if name in RENAME or new_text != text:
            direct.add(name)
        if name in direct or any(dep in affected for dep in entry['project_imports']):
            affected.add(name)
    if 'BlockMacro2' in original:
        text = (source / 'BlockMacro2.lean').read_text()
        if 'import BlockMacro' not in text or 'export BB6BlockFAR' not in text:
            raise ValueError('not the modern Raw59 width-two primitive implementation')
    names = [RENAME.get(name, name) for name in order]
    replay = affected - direct if kernel_replay else set()
    replay_names = {RENAME.get(name, name) for name in replay}
    report = {'producer_manifest_sha256': sha(manifest_path),
              'producer_source_revision': manifest['proof_source_revision'],
              'producer_claim': manifest['claim'],
              'lean_version': version, 'compiler_sha256': sha(compiler),
              'namespace_rename': {OLD_NAMESPACE: NEW_NAMESPACE},
              'module_renames': {k: v for k, v in RENAME.items() if k in original},
              'recompiled_modules': [RENAME.get(name, name) for name in order if name in affected - replay],
              'kernel_replayed_modules': sorted(replay_names),
              'reused_count': len(order) - len(affected), 'module_count': len(order)}
    print(f"{len(order)} checked producer modules; {len(affected)} affected; {len(order)-len(affected)} reusable", flush=True)
    if plan_only:
        print(json.dumps(report, indent=2, sort_keys=True))
        return report
    output.mkdir(parents=True, exist_ok=False)
    logs = output / 'logs'
    logs.mkdir()
    result_entries: dict[str, dict] = {}
    for old_name, name in zip(order, names):
        src = output / (name + '.lean')
        original_entry = original[old_name]
        if old_name in affected - replay:
            src.write_text(transformed[old_name])
        else:
            shutil.copyfile(source / (old_name + '.lean'), src)
            shutil.copyfile(source / (old_name + '.olean'), output / (name + '.olean'))
        deps = imports(src.read_text())
        expected_deps = [RENAME.get(dep, dep) for dep in original_entry['project_imports']]
        if deps != expected_deps or set(deps) & RENAME.keys():
            raise ValueError(f'bad isolated import graph for {name}')
        result_entries[name] = {'module': name, 'source_path': name + '.lean',
                                'source_kind': ('artifact-kernel-replayed' if old_name in replay else
                                                'artifact-namespace-transform' if old_name in affected else 'artifact-reused'),
                                'source_sha256': sha(src), 'project_imports': deps,
                                'olean_path': name + '.olean',
                                'producer_module': old_name,
                                'producer_module_identity_sha256': original_entry['module_identity_sha256']}
    env = dict(os.environ, LEAN_PATH=str(output.resolve()))

    def compile_one(name: str) -> tuple[str, float]:
        start = time.monotonic()
        log_path = logs / (name + '.log')
        with log_path.open('w') as log:
            p = subprocess.run([lean, '-o', name + '.olean', name + '.lean'], cwd=output, env=env,
                               stdout=log, stderr=subprocess.STDOUT)
        log = log_path.read_text()
        if p.returncode or re.search(r'sorryAx|native_decide', log):
            raise RuntimeError(f'compile failed: {name}\n{log[-12000:]}')
        check_axioms(log, [])
        seconds = time.monotonic() - start
        print(f'compiled {name}: {seconds:.2f}s', flush=True)
        return name, seconds

    done = {RENAME.get(name, name) for name in order if name not in affected}
    pending = set(names) - done
    timing = {}
    while pending:
        ready = sorted(name for name in pending if set(result_entries[name]['project_imports']) <= done)
        if not ready:
            raise ValueError('no remaining import layer')
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            timing.update(pool.map(compile_one, [name for name in ready if name not in replay_names]))
        # Group by the source import list; Lean independently checks the actual
        # serialized import descriptors before replaying each declaration.
        groups: dict[tuple[str, ...], list[str]] = {}
        for name in ready:
            if name in replay_names:
                key = tuple(m.group(0).strip() for m in IMPORT.finditer((output / (name + '.lean')).read_text()))
                groups.setdefault(key, []).append(name)
        for group in groups.values():
            log_path = logs / (group[0] + '.replay.log')
            start = time.monotonic()
            cmd = [lean, '--run', str(Path(__file__).resolve().with_name('ReplayUnchanged.lean')),
                   *[name + '.olean' for name in group]]
            with log_path.open('w') as log:
                p = subprocess.run(cmd, cwd=output, env=env, stdout=log, stderr=subprocess.STDOUT)
            log = log_path.read_text()
            if p.returncode or any(f'PASS {name}.olean: checked by Lean kernel' not in log for name in group):
                raise RuntimeError(f'kernel replay failed: {group}\n{log[-12000:]}')
            print(log, end='', flush=True)
            print(f'kernel-replayed {len(group)} modules: {time.monotonic()-start:.2f}s', flush=True)
        done.update(ready)
        pending.difference_update(ready)
    for name, entry in result_entries.items():
        entry['olean_sha256'] = sha(output / entry['olean_path'])
        old_name = entry['producer_module']
        if (old_name not in affected or old_name in replay) and entry['olean_sha256'] != original[old_name]['olean_sha256']:
            raise ValueError(f'reused object changed: {name}')
    identities(result_entries, names)
    roots = [RENAME.get(r['module'], r['module']) for r in manifest['roots']]
    required = list(dict.fromkeys([x for x in [manifest['claim'].get('theorem'), *claims] if x]))
    audit = output / 'IsolationAudit.lean'
    audit.write_text(''.join(f'import {root}\n' for root in roots) + ''.join(f'#print axioms {claim}\n' for claim in required))
    audit_result = subprocess.run([lean, audit.name], cwd=output, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (output / 'audit.log').write_text(audit_result.stdout)
    print(audit_result.stdout, end='', flush=True)
    audit_result.check_returncode()
    profiles = check_axioms(audit_result.stdout, required)
    report['compile_seconds'] = timing
    report['axiom_profiles'] = profiles
    report['roots'] = roots
    report['modules'] = [result_entries[name] for name in sorted(result_entries)]
    (output / 'isolation-report.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print('KERNEL-REPLAY ISOLATION PASSED' if kernel_replay else 'SOURCE-REBUILT ISOLATION PASSED', flush=True)
    return report


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source', type=Path, help='extracted accepted artifact with flat .lean, .olean and manifest.json')
    ap.add_argument('output', type=Path)
    ap.add_argument('--lean', default='lean')
    ap.add_argument('--jobs', type=int, default=1)
    ap.add_argument('--claim', action='append', default=[])
    ap.add_argument('--plan-only', action='store_true')
    ap.add_argument('--kernel-replay', action='store_true', help='kernel-check unchanged source/object pairs in the changed reverse cone instead of re-elaborating')
    args = ap.parse_args()
    run(args.source.resolve(), args.output.resolve(), args.lean, args.jobs, args.claim, args.plan_only, args.kernel_replay)


if __name__ == '__main__':
    main()
