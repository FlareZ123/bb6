#!/usr/bin/env python3
"""Close identified residual leaves of the pinned raw122 audit by literal table."""
from pathlib import Path
import sys, re, json
from raw122_patch import PARENT,MOVES,leaf
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parent/'agent47-raw114-cut'),str(HERE.parent/'agent31-three-hole-tnf')]
import multi_sweep as ms
import generate_sweeps as gs
COUNTER='BB6Coverage.Agent43Raw122Counter'
SELECT={12:{8957,8958,10076,10443},23:{28406,28530,29181,29184}}
COUNTERS={
 '1RB1LB_1RC0LE_0RD1RC_1LD1RE_0RB0LF_---1LA':0,
 '1RB1LB_1RC0LE_0RD1RD_1LD1RE_0RB0LF_---1LA':1,
}
def plan_proof(p):
    row=p['row']; idx=p['id']
    def w(x):return ms.Word.of(*(ms.Rep(a['rep']) if isinstance(a,dict) else a for a in x))
    st=ms.Config(p['q'],w(p['left']),w(p['right']))
    dst=ms.Config(st.q,st.l.inc(),st.r.inc())
    table=gs.parse(row)
    res=ms.execute(table,st,dst,limit=20000)
    assert res is not None,(idx,row)
    proof,info=ms.generate(idx,table,(p['entry'],st,dst,res))
    module=f'Raw122Planned{idx}'
    source='import SweepPumping\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false\nnamespace BB6Coverage.Agent31Pump\nopen BB6Coverage\n'+proof+'\nend BB6Coverage.Agent31Pump\n'
    return module,source,f'.proven BB6Coverage.Agent31Pump.M{idx}.table BB6Coverage.Agent31Pump.M{idx}.never',info
def patch(root,branch,kid):
    f=root/f'Raw122Kid{branch:02}_{kid:02}.lean'
    head,body=f.read_text().split(' : PartialAudit := ',1)
    expr,tail=body.split('\ntheorem',1)
    lines=iter(expr.strip().splitlines())
    parent=list(gs.parse(PARENT));parent[11]=MOVES[branch]
    src=(root/f'Raw122Branch{branch:02}.lean').read_text()
    m=re.search(r'def branch\d+ : PartialAudit := \.split \d+ \((\d+),(true|false)\)',src)
    assert m
    slot=2*int(m[1])+(m[2]=='true')
    assert parent[slot]=='---'
    parent[slot]=MOVES[kid]
    plans={p['row']:p for p in json.loads((HERE/'long-plans.json').read_text()) if p['id'] in SELECT[branch]}
    seen=set(); imports=set()
    def read(p,partial=True,first=None):
        s=next(lines).strip() if first is None else first
        if partial and s.startswith('.closed ('):
            return read(p,False,s[len('.closed ('):])
        m=re.match(r'\.split (\d+) \((\d+),(true|false)\) \(by(Partial)?Move \[',s)
        if m:
            n,q,b,part=m.groups();assert partial==bool(part)
            sl=2*int(q)+(b=='true');assert p[sl]=='---'
            kids=[]
            for a in MOVES:
                c=p.copy();c[sl]=a;kids.append(read(c,partial))
            return f'.split {n} ({q},{b}) (byMove [\n'+',\n'.join(kids)+'])'
        row=gs.show(p)
        if partial:
            assert s.startswith('.unresolved'),s
            assert row not in seen,row
            seen.add(row)
            if branch==12 and row in COUNTERS:
                v=COUNTERS[row];imports.add('Raw122Counter')
                (root/'Raw122Counter.lean').write_bytes((HERE/'Raw122Counter.lean').read_bytes())
                return f'.proven ({COUNTER}.table {str(bool(v)).lower()}) {COUNTER}.never{v}'
            assert row in plans,(branch,kid,row)
            module,source,proof,info=plan_proof(plans[row])
            (root/(module+'.lean')).write_text(source)
            imports.add(module);print('plan',plans[row]['id'],info,flush=True)
            return proof
        assert re.match(r'\.(?:last|cycle|far|proven) ',s),s
        return leaf(s)
    result=read(parent)
    assert next(lines,None) is None
    f.write_text(''.join(f'import {m}\n' for m in sorted(imports))+head+' : PartialAudit := .closed ('+result+')\ntheorem'+tail)
    print('patched',branch,kid,sorted(seen),flush=True)
if __name__=='__main__':
    patch(Path(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]))
