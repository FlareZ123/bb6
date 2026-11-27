"""Split an independent generated *Small.lean module into exact root blocks.

Preserves every declaration verbatim, and replaces the original module with
an import-only facade. This is a source transformation, not a proof oracle.
Run on uncompiled generated sources; Lean checks each resulting module.
"""
import re
import sys
from pathlib import Path


def split(path: Path) -> list[Path]:
    text = path.read_text()
    m = re.fullmatch(r'(.*Root)((?:_\d\d)*)Small', path.stem)
    if m is None:
        raise ValueError(f'not a generated Small module: {path}')
    if not re.search(r'^abbrev pRoot', text, re.M):
        return []  # already an import-only facade
    prefix = 'pRoot' + m.group(2)
    matches = list(re.finditer(r'^abbrev ' + prefix + r'_\d\d :=', text, re.M))
    end = re.search(r'^end BB6\.Agent32Raw42[^\n]+\.Closed\s*\Z', text, re.M)
    if not matches or end is None:
        raise ValueError(f'unrecognized generated source: {path}')
    header = text[:matches[0].start()]
    if re.search(r'^(?:def|abbrev|theorem) ', header, re.M):
        raise ValueError(f'nontrivial header in {path}')
    blocks = []
    for i, match in enumerate(matches):
        limit = matches[i+1].start() if i+1 < len(matches) else end.start()
        block = text[match.start():limit]
        tag = match.group(0).split(' :=')[0].split('_')[-1]
        target = path.with_name(f'{path.stem}_{tag}.lean')
        blocks.append((target, header + block + end.group(0) + '\n'))
    # Exact source reproduction and unique names are checked before any write.
    assert len({p for p,_ in blocks}) == len(blocks)
    for p,s in blocks:
        if p.exists() and p.read_text() != s:
            raise ValueError(f'conflicting split output: {p}')
    for p,s in blocks:
        p.write_text(s)
    path.write_text(''.join(f'import {p.stem}\n' for p,_ in blocks))
    return [p for p,_ in blocks]

if __name__ == '__main__':
    for path in map(Path, sys.argv[1:]):
        print(path, len(split(path)))
