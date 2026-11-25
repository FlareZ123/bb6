#!/usr/bin/env python3
"""Merge raw109 same-revision audited shards without silent object collisions.

Restore generated sources in the checkout, leaving tracked inputs untouched.
The existing strict closure compiler then revalidates all module identities and
checks the unconditional parent theorem against this union.
"""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

GROUPS = {
    'cut': {'Raw109Cut'},
    'lc-re-lb': {'Raw109B0LCData', 'Raw109B1REData', 'Raw109B1LBData'},
    'rf': {'Raw109B0RFData', 'Raw109B1RFData'},
    'lc-la': {'Raw109B1LCData', 'Raw109B0LAData'},
    'la-rc': {'Raw109B1LAData', 'Raw109B0RCData'},
    'lf1': {'Raw109B1LFData'},
    'lf0': {'Raw109B0LFData'},
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def inside(root, relative):
    path = (root / relative).resolve()
    require(path.is_relative_to(root), f'path escapes {root}: {relative}')
    return path


def merge(repo, downloads, output, groups=None, artifact_prefix='raw109-shard'):
    groups = GROUPS if groups is None else groups
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
    tracked = set(subprocess.check_output(['git', 'ls-files', '-z'], cwd=repo).decode().split('\0'))
    output.mkdir(parents=True, exist_ok=False)
    entries = {}
    inputs = {}
    manifests = []
    template = None
    for group, roots in groups.items():
        artifact_name = f'{artifact_prefix}-{group}'
        shard = downloads / artifact_name
        manifest = json.loads((shard / 'manifest.json').read_text())
        require(manifest['schema_version'] == 1, f'{group}: bad schema')
        require(manifest['proof_source_revision'] == revision, f'{group}: revision mismatch')
        require(manifest['artifact_name'] == artifact_name, f'{group}: wrong artifact name')
        require({item['module'] for item in manifest['roots']} == roots, f'{group}: unexpected roots')
        if template is None:
            template = manifest
        require(manifest['lean_version'] == template['lean_version'], f'{group}: Lean version mismatch')
        require(manifest['lean_binary']['sha256'] == template['lean_binary']['sha256'], f'{group}: compiler hash mismatch')
        modules = {item['module']: item for item in manifest['modules']}
        require(len(modules) == len(manifest['modules']) == manifest['module_count'], f'{group}: duplicate/missing modules')
        require(roots <= modules.keys(), f'{group}: missing root object')
        for name, item in modules.items():
            require(set(item['project_imports']) <= modules.keys(), f'{group}: {name} has absent dependencies')
            relative = name.replace('.', '/')
            require(item['olean_path'] == relative + '.olean', f'{group}: {name} has unexpected object path')
            source = inside(shard, relative + '.lean')
            obj = inside(shard, item['olean_path'])
            require(digest(source) == item['source_sha256'], f'{group}: {name} source hash mismatch')
            require(digest(obj) == item['olean_sha256'], f'{group}: {name} object hash mismatch')
            if name in entries:
                require(entries[name] == item, f'{group}: conflicting shared module {name}')
            else:
                entries[name] = item
                dest = inside(output, item['olean_path'])
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(obj, dest)
                src = inside(repo, item['source_path'])
                if src.exists() or item['source_path'] in tracked:
                    require(src.is_file() and digest(src) == item['source_sha256'], f'{group}: checkout source mismatch for {name}')
                else:
                    require(item['source_kind'] == 'generated-or-untracked', f'{group}: cannot restore {name}')
                    src.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(source, src)
        for item in manifest['provenance_inputs']:
            path = item['path']
            require(digest(inside(repo, path)) == item['sha256'], f'{group}: input mismatch {path}')
            require(path not in inputs or inputs[path] == item, f'{group}: conflicting input {path}')
            inputs[path] = item
        manifests.append(manifest)
    merged = dict(template, label=f'{artifact_prefix}-union', artifact_name=f'{artifact_prefix}-union',
                  roots=[item for m in manifests for item in m['roots']],
                  modules=[entries[k] for k in sorted(entries)], module_count=len(entries),
                  provenance_inputs=[inputs[k] for k in sorted(inputs)],
                  shard_workflows=[m['workflow'] for m in manifests])
    (output / 'manifest.json').write_text(json.dumps(merged, indent=2, sort_keys=True) + '\n')
    print(f'Validated {len(manifests)} shards; {len(entries)} unique modules at {revision}')


if __name__ == '__main__':
    if len(sys.argv) not in (3, 4):
        raise SystemExit('usage: merge_shards.py DOWNLOADS OUTPUT [CONFIG.json]')
    groups = GROUPS
    artifact_prefix = 'raw109-shard'
    if len(sys.argv) == 4:
        config = json.loads(Path(sys.argv[3]).read_text())
        artifact_prefix = config['artifact_prefix']
        groups = {name: set(modules) for name, modules in config['groups'].items()}
    merge(
        Path.cwd().resolve(),
        Path(sys.argv[1]).resolve(),
        Path(sys.argv[2]).resolve(),
        groups,
        artifact_prefix,
    )
