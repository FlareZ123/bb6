"""Patch exact unresolved leaves in pinned Raw122 generated audit 15043765926.
Only leaves matching full literal tables are replaced. Unmatched leaves remain
unresolved. Closed splits are consolidated into ordinary Audit nodes.
"""
from itertools import product
from pathlib import Path
import re,json,sys
from generate import rows,generate
HERE=Path(__file__).resolve().parent
MOVES=[''.join(x) for x in product('01','LR','ABCDEF')]
P='1RB---1RC---0RD---1LD1RE---0LF------'
PARENT=[P[i:i+3] for i in range(0,36,3)]

def patch(root,branch,kid):
    f=root/f'Raw122Kid{branch:02}_{kid:02}.lean'
    s=f.read_text()
    if '.unresolved' not in s:return False
    selected={m:i for i,sh, m,*_ in rows() if sh==f.stem}
    direct_dir=HERE.parent/'agent43-raw122-cut'
    direct={a['table'].replace('_',''):a for a in json.loads((direct_dir/'direct_certificates.json').read_text()) if a['id'] not in (28,29,32)}
    sys.path.insert(0,str(direct_dir))
    import direct_cert
    h=re.search(r'def kid\d+_\d+ : PartialAudit := (.*?)\ntheorem',s,re.S);assert h
    body=h[1];i=0;imports=set();ids=set();dids=set();remaining=[]
    t=PARENT.copy();t[11]=MOVES[branch]
    slot=re.search(r'partialCheck 7014 \(refine \(child ⟨[^⟩]+⟩\) \((\d+),(true|false)\)',s)
    assert slot
    t[2*int(slot[1])+(slot[2]=='true')]=MOVES[kid]
    def ws():
        nonlocal i
        while i<len(body) and body[i].isspace():i+=1
    def expect(x):
        nonlocal i
        ws();assert body.startswith(x,i),(x,body[i:i+100]);i+=len(x)
    def read():
        nonlocal i
        ws()
        if body.startswith('.closed',i):
            i+=7;ws();assert body[i]=='(';a=i+1;n=1;i+=1
            while n:
                c=body[i];i+=1;n+=(c=='(')-(c==')')
            return True,body[a:i-1]
        if body.startswith('.unresolved',i):
            i+=11;m=''.join(t)
            if m in selected:
                j=selected[m];ids.add(j);imports.add(f'Agent29Raw122Indexed{j:03}')
                ns=f'BB6Coverage.Agent29Raw122Indexed.M{j:03}'
                return True,f'.proven {ns}.table {ns}.never'
            if m in direct:
                a=direct[m];j=a['id'];dids.add(j);imports.add(f'Raw122Direct{j}')
                ns=f'BB6Coverage.Agent31Pump.Raw122DirectGrowth.M{j}'
                return True,f'.proven {ns}.table {ns}.never'
            remaining.append(m);return False,'.unresolved'
        z=re.match(r'\.split\s+(\d+)\s+\((\d+),(true|false)\)\s+\(byPartialMove\s*\[',body[i:])
        assert z,body[i:i+100]
        i+=z.end();sl=2*int(z[2])+(z[3]=='true');assert t[sl]=='---'
        kids=[]
        for j,mv in enumerate(MOVES):
            if j:expect(',')
            t[sl]=mv;kids.append(read());t[sl]='---'
        expect(']');expect(')')
        closed=all(x[0] for x in kids)
        parts=[a if closed or not c else f'.closed ({a})' for c,a in kids]
        return closed,f'.split {z[1]} ({z[2]},{z[3]}) (by{"Move" if closed else "PartialMove"} [\n'+',\n'.join(parts)+'])'
    closed,out=read();ws();assert i==len(body)
    assert ids==set(selected.values()),(f,ids,selected)
    if not ids and not dids:return False
    generate(root,ids)
    for a in direct.values():
        if a['id'] in dids:direct_cert.generate(a,root)
    if ids:
        for rel in ['agent16-raw118/BiDFA.lean','agent16-raw118/TreeBiDFA.lean','agent1-bidfa-sat/IndexedBiDFA.lean']:
            src=HERE.parent/rel
            (root/src.name).write_bytes(src.read_bytes())
    expr=f'.closed ({out})' if closed else out
    f.write_text(''.join(f'import {m}\n' for m in sorted(imports))+s[:h.start(1)]+expr+s[h.end(1):])
    print(f.stem,'run-aware',sorted(ids),'direct',sorted(dids),'remaining',len(remaining),flush=True)
    return True

if __name__=='__main__':
    patch(Path(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]))
