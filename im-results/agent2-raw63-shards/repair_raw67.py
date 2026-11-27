#!/usr/bin/env python3
"""Recover only failed Raw67Kid11; keep the five authenticated successful shards."""
import argparse
import json
import re
from itertools import product
from pathlib import Path
import subprocess
import zipfile
from shard import compile_roots, merge, schedule, digest

REPO = "FlareZ123/bb6"
RUN = 46032521543
PINS = {
    "generated": (15214857546, "613847244de5b4b47b8c65ab76aac0414ac6c4f7901777d975ac9bdc9f007529"),
    "core": (15214762707, "0680c19f9894890b16e74750bac6c64038c2f0ac1218294221443d59e028f89f"),
    "shard-1": (15214644110, "cbb172cd1ef9f812a9015a24ce82a6ed9fbba6cee3daafa5b3e8cfd3109634bb"),
    "shard-2": (15215441634, "3a573e00af7bc10826badbdcc1fe1b736e0c1b7bc3ae86543a0d763594e110af"),
    "shard-3": (15214718608, "01789aab429ff48bc65dd5f460ea60a67f837a6423b4bcbfd744cf1830c68e6a"),
    "shard-4": (15214753303, "0fea0268fd29f7dfe888337c96f440ecc8e275784da0943cf17e0dc601ac1207"),
    "shard-5": (15214822932, "d2acf5b8db17f4fea26799c85193f6b06dd2092d7a9cd98ba418ab795b6adb0f"),
}
MOVES = [f'⟨{str(bool(w)).lower()},{str(bool(r)).lower()},{q}⟩'
         for w,r,q in product(range(2),range(2),range(6))]


def fetch(key, dest):
    aid, expected = PINS[key]
    metadata = json.loads(subprocess.check_output(
        ["gh", "api", f"repos/{REPO}/actions/artifacts/{aid}"], text=True))
    assert metadata["workflow_run"]["id"] == RUN
    assert metadata["name"] == "raw67-prefix-" + key
    assert not metadata["expired"] and metadata["digest"] == "sha256:" + expected
    dest.mkdir(parents=True, exist_ok=False)
    archive = dest / "download.zip"
    with archive.open("wb") as f:
        subprocess.run(["gh", "api", f"repos/{REPO}/actions/artifacts/{aid}/zip"], stdout=f, check=True)
    assert digest(archive) == expected
    with zipfile.ZipFile(archive) as z:
        z.extractall(dest)
    archive.unlink()


def split_children(text):
    m = re.fullmatch(r'\.split (\d+) (\(\d+,(?:true|false)\)) \(byMove \[\s*(.*)\]\)', text, re.S)
    assert m, text[:200]
    body = m[3]
    stack, kids, start = [], [], 0
    close = {')':'(', ']':'[', '⟩':'⟨'}
    for i, c in enumerate(body):
        if c in '([⟨':
            stack.append(c)
        elif c in close:
            assert stack.pop() == close[c]
        elif c == ',' and not stack:
            kids.append(body[start:i].strip())
            start = i+1
    assert not stack
    kids.append(body[start:].strip())
    assert len(kids) == 24
    return m[1], m[2], kids


def factor(generated):
    s = schedule(generated)
    assert s['branch']=='67' and s['groups'][0]==['Raw67Kid11']
    path = generated / 'Raw67Kid11.lean'
    header, rest = path.read_text().split('def kid11 : Audit := ',1)
    tree, check = rest.split('\ntheorem check11 : ',1)
    m = re.match(r'zipCheck 808 (\(child67 ⟨false,true,5⟩\)) kid11 = true := by', check)
    assert m
    parent = m[1]
    n, slot, kids = split_children(tree)
    names = []
    for i,(kid,mv) in enumerate(zip(kids,MOVES)):
        module, name, proof = f'Raw67Kid11P{i:02}',f'kid11P{i:02}',f'check11P{i:02}'
        child = f'(refine {parent} {slot} (some {mv}))'
        body = f'def {name} : Audit := {kid}\ntheorem {proof} : zipCheck 808 {child} {name} = true := by\n  rw [← BB6.Agent48PrefixAudit.prefixCheck_eq]\n  decide\n'
        (generated/(module+'.lean')).write_text(header+body+'\nend BB6.Agent10Raw67\n')
        names.append((module,name,proof))
    imports = ''.join(f'import {mod}\n' for mod,_,_ in names)
    body = f'def branches11 : Move → Audit := byMove [{",".join(k for _,k,_ in names)}]\n'
    body += f'theorem branches11_checked (mv : Move) : zipCheck 808 (refine {parent} {slot} (some mv)) (branches11 mv) = true := by\n  rcases mv with ⟨w,r,q⟩\n  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl\n  all_goals cases w <;> cases r\n'
    body += '\n'.join(f'  · exact {names[12*w+6*r+q][2]}' for q,w,r in product(range(6),range(2),range(2)))+'\n'
    body += f'def kid11 : Audit := .split {n} {slot} branches11\n'
    body += f'theorem check11 : zipCheck 808 {parent} kid11 = true := by\n  change (zipQueryOK 808 {parent} {n} {slot} && allMoves (fun mv => zipCheck 808 (refine {parent} {slot} (some mv)) (branches11 mv))) = true\n  simp only [Bool.and_eq_true]\n  exact ⟨by decide, allMoves_of _ branches11_checked⟩\n'
    path.write_text(imports+header+body+'\nend BB6.Agent10Raw67\n')
    groups = [[] for _ in range(6)]
    loads = [0]*6
    for module,_,_ in sorted(names,key=lambda row: -(generated/(row[0]+'.lean')).stat().st_size):
        size = (generated/(module+'.lean')).stat().st_size
        i = min(range(6),key=loads.__getitem__)
        groups[i].append(module)
        loads[i] += size
    s['groups'] = s['groups'][1:] + groups
    s['sources'] = {p.name:digest(p) for p in sorted(generated.glob('*.lean'))}
    (generated/'schedule.json').write_text(json.dumps(s,indent=2)+'\n')
    print(f'Factored unchanged Raw67Kid11 into 24 subtree checks; shard source loads {loads}',flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action',choices=('prepare','shard','assemble'))
    ap.add_argument('--generated',required=True,type=Path)
    ap.add_argument('--core',type=Path)
    ap.add_argument('--work',type=Path)
    ap.add_argument('--inputs',type=Path)
    ap.add_argument('--merged',type=Path)
    ap.add_argument('--shard',type=int)
    a=ap.parse_args()
    if a.action=='prepare':
        fetch('generated',a.generated)
        factor(a.generated)
        fetch('core',a.core)
    elif a.action=='shard':
        s=schedule(a.generated)
        compile_roots([a.generated/(r+'.lean') for r in s['groups'][5+a.shard]],
                      a.generated,a.core,a.work,'67')
    else:
        for i in range(5):
            fetch(f'shard-{i+1}',a.inputs/f'raw67-repair-shard-{i}')
        merge(a.inputs,a.merged,a.generated,prefix='raw67-repair')
        compile_roots([a.generated/'Raw67ParentCover.lean'],a.generated,a.merged,a.work,'67',final=True)

if __name__=='__main__':
    main()
