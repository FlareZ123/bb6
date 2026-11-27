"""Replay fixed Raw47 recurrence recipes and emit Lean proofs.

Run: python generate_pumps.py > Raw47Pumps.lean
Requires the existing Agent48 autopump/emitproof modules.
"""
import json
from pathlib import Path
import re
import sys
import tempfile
here = Path(__file__).resolve().parent
sys.path.insert(0,str(here.parent / 'agent48-raw139-f1-oneLA'))
from autopump import *
from emitproof import emit

def word(s):
    return normalize([G(x[1:-1]) if x.startswith('(') else x for x in re.findall(r'\([01]+\)|[01]+',s)])

def parse(t):
    t=t.replace('_','')
    return [24 if t[i]=='-' else 4*(ord(t[i+2])-65)+2*int(t[i])+(t[i+1]=='R') for i in range(0,36,3)]

rows=[line.split()[2] for line in (here/'hard30.txt').read_text().splitlines()]
print('import SweepPumping\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent50Raw47Pumps\nopen BB6Coverage BB6Coverage.Agent31Pump')
with tempfile.TemporaryDirectory() as tmp:
    for line in (here/'pump-recipes.txt').read_text().splitlines():
        i,t,q,l,r,recipe=line.split()
        i,t,q=map(int,[i,t,q])
        p=parse(rows[i]); c=(q,word(l),word(r)); a=c; ops=[]
        assert evaluate(trace(p,t)[t],0)==evaluate(c,0)
        for token in recipe.split(','):
            if token.isdigit():
                for _ in range(int(token)):
                    b=step(p,a); assert b is not None
                    ops.append(('step',a,b)); a=b
            else:
                side=token[0]; prefix,cost=map(int,token[1:].split(':'))
                matches=[(b,op) for b,op in pump(p,a,side) if len(op[3])==prefix and op[6]==cost]
                assert len(matches)==1,(i,token,matches)
                b,op=matches[0]; ops.append(('pump',a,b,op)); a=b
        target=targetnext(c)
        assert a[0]==q and canonical(a[1])==canonical(target[1]) and canonical(a[2])==canonical(target[2])
        path=Path(tmp)/f'pump-{i}.json'
        path.write_text(json.dumps(dict(table=p,result=(t,c,(ops,a))),default=js))
        s=emit(path)
        table=['def ctr : PartialMachine := fun s => match s.1.val,s.2 with']
        for k,v in enumerate(p):
            if v!=24:
                table.append(f'  | {k//2},{str(bool(k%2)).lower()} => some (some ⟨{str(bool(v&2)).lower()},{str(bool(v&1)).lower()},{v//4}⟩)')
        table.append('  | _,_ => none')
        s=re.sub(r'^def ctr : PartialMachine := .*$',lambda _: '\n'.join(table),s,count=1,flags=re.M)
        cost=re.search(r'theorem growth \(n : Nat\) : run0 ctr \((\d+)\*n\+(\d+)\)',s)
        a,b=cost.groups()
        s=s.replace(f'#print axioms growth\nend H{i}',f'theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=\n  never_of_growth ctr family {t} (fun n => {a}*n+{b}) entry (fun k => by omega) growth m hm\n#print axioms never\nend H{i}')
        print(s)
print('end BB6.Agent50Raw47Pumps')
