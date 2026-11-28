#!/usr/bin/env python3
"""Original-source candidate emitter for five literal Raw36 D1=0LA modular-stack quotients.

Discovery/replay is untrusted. Every exported NeverHalts assertion must be
accepted by the independent TwoSidedAutomata Lean source and axiom audit.
"""
import gzip,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def main(census,out):
    data=json.loads(gzip.decompress(Path(census).read_bytes()))
    assert data['parent']=='1RB---_1RC---_0RD---_0LD0LA_------_------'
    keys=sorted(t.replace('_','') for t in data['opens'])
    assert len(keys)==2255
    assert hashlib.sha256('\n'.join(keys).encode()).hexdigest()=='d3cff2c1257272d8af4c8087906589d4623f41dcd8cd3de98e2ae7f71d8d8ff0'
    variant=sys.argv[3] if len(sys.argv)>3 else 'five'
    assert variant in ('five','six','ten')
    fixture=ROOT/('d100-new-phase-ten.json' if variant=='ten' else 'd100-new-modular-extra.json' if variant=='six' else 'd100-new-modular.json')
    rows=json.loads(fixture.read_text())
    assert len(rows)==(10 if variant=='ten' else 6 if variant=='six' else 5) and len({t for t,v in rows})==len(rows)
    norm=sorted(t.replace('_','') for t,v in rows)
    assert all(t in keys for t in norm)
    digest=('4fc1a66ec41ec1e6725bd12d9346315c2580839eee291eb87a931344ecda3ecc' if variant=='ten' else '80f04cbbd0e04cefaa660374a207d750e5064669ea74d8525012f0427ab5cc4c' if variant=='six' else 'b89e5b016f42c2e5fd81e50339b29b2bf0c125f4592c6e2c7e13fffe196eaac3')
    assert hashlib.sha256('\n'.join(sorted(t for t,v in rows)).encode()).hexdigest()==digest
    if variant in ('six','ten'):
        older=['d100-new-modular.json']+(['d100-new-modular-extra.json'] if variant=='ten' else [])
        for f in older:
            old={t.replace('_','') for t,v in json.loads((ROOT/f).read_text())}
            assert old.isdisjoint(norm)
    pumps={t.replace('_','') for t in (ROOT/'d100-new-pumps.txt').read_text().splitlines()}
    assert pumps.isdisjoint(norm)
    assert all((v[0] in ('m','r') and len(v)==5) or (v[0]=='p' and len(v)==7) for t,v in rows)
    sys.path.insert(0,str(ROOT.parent/'agent7-raw36-b1le'))
    from stack_candidates import generate
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    stem='Raw36D100Phase' if variant=='ten' else 'Raw36D100Extra' if variant=='six' else 'Raw36D100Mod'
    namespace='BB6.Agent7Raw36D100Phase' if variant=='ten' else 'BB6.Agent7Raw36D100ModularExtra' if variant=='six' else 'BB6.Agent7Raw36D100Modular'
    mapping=generate([(t.replace('_',''),v) for t,v in rows],out,stem=stem,ns=namespace)
    assert len(mapping)==len(rows)
    theorems=[mapping[t.replace('_','')][1]+'.never' for t,v in rows]
    assert all(mapping[t.replace('_','')][0]==stem+'Automata00' for t,v in rows)
    (out/'theorems.txt').write_text('\n'.join(theorems)+'\n')
    (out/'source-index.json').write_text(json.dumps(dict(census_digest='d3cff2c1257272d8af4c8087906589d4623f41dcd8cd3de98e2ae7f71d8d8ff0',tables=rows,theorems=theorems),indent=2)+'\n')
    print('strict five-key source emission',len(mapping),theorems,flush=True)
if __name__=='__main__':
    main(sys.argv[1],sys.argv[2])
