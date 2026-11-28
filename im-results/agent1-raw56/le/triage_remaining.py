#!/usr/bin/env python3
"""Exact per-E0 inventory map for the nine unresolved Raw56 E1=0LE siblings.

Replays the pinned canonical root open list; the counts are triage data, not
certificates. Only source-accepted Lean Covers can remove a parent.
"""
import base64, collections, gzip, hashlib, itertools, json, subprocess, tempfile
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CUT = ROOT / 'im-results/agent7-raw49/cut.cpp'
P = '1RB---_1RC---_0RD---_1LD1LE_---0LE_------'
OPEN_SHA = 'aba63f28439c707c3343fd4ff53f66717d5924b88b1aa8012947f6039e0da7ef'
INV_SHA = '869a651cebab0b5eda351eb783438e7040237b3412747f3ac6265629b840da6f'
def delta_set(groups):
    return {i for _,ds in groups for i in itertools.accumulate(ds)}
def main():
    src=gzip.decompress(base64.b64decode((HERE/'inventory-79.json.gz.b64').read_text()))
    assert hashlib.sha256(src).hexdigest()==INV_SHA
    inv=json.loads(src)
    with tempfile.TemporaryDirectory(prefix='raw56-le-triage-') as d:
        d=Path(d)
        exe=d/'cut'
        subprocess.run(['g++','-std=c++20','-O3',str(CUT),'-o',str(exe)],check=True)
        subprocess.run([str(exe),P,'1000','32','7',str(d/'global-le')],check=True,stdout=subprocess.DEVNULL)
        body=(d/'global-le.open').read_bytes()
        assert hashlib.sha256(body).hexdigest()==OPEN_SHA
        rows=body.decode().splitlines()
    assert len(rows)==26493
    fields={
        'extraFAR': delta_set(inv['fmore']),
        'finiteDFA': delta_set(inv['abs']),
        'late': {r[0] for r in inv['late']},
        'remaining': set(inv['remaining']),
    }
    if inv.get('sat'):
        fields['sat']={r[0] if isinstance(r,list) else r for r in inv['sat']}
    used=set()
    for key,ids in fields.items():
        assert not used.intersection(ids),(key,used.intersection(ids))
        used.update(ids)
    fields['baseFAR5']=set(range(len(rows)))-used
    bytype={i:kind for kind,ids in fields.items() for i in ids}
    assert len(bytype)==len(rows)
    groups=collections.defaultdict(lambda:collections.Counter())
    hard=collections.defaultdict(list)
    late=collections.defaultdict(list)
    for i,tab in enumerate(rows):
        e0=tab.split('_')[4][:3]
        assert len(e0)==3,(i,tab)
        groups[e0][bytype[i]]+=1
        if i in fields['remaining']:hard[e0].append((i,tab))
    for r in inv['late']:
        e0=rows[r[0]].split('_')[4][:3]
        late[e0].append((r[0],r[2],r[1]))
    keys=sorted(groups)
    print('E0 | total | baseFAR5 | extraFAR | finiteDFA | late | unproved')
    for key in keys:
        row=groups[key]
        print(f"{key} | {sum(row.values())} | {row['baseFAR5']} | {row['extraFAR']} | {row['finiteDFA']} | {row['late']} | {row['remaining']}")
    print('TOTAL',collections.Counter({k:len(v) for k,v in fields.items()}))
    for key in keys:
        if hard[key] or late[key]:
            print('DETAIL',key,'hard',hard[key],'late',late[key])
    print('CANDIDATE_COMPLETE_BY_INVENTORY',[k for k in keys if not hard[k]])
if __name__=='__main__':main()
