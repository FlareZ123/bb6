"""Compose any bank of accepted Raw47 D3 FAR, graph or pump parent modules.
Every packed key is checked against its actual Lean table, and the kernel checks
the residual count. No witness discovery or positional roster assumption.
"""
from pathlib import Path
import hashlib, json, re, sys
here=Path(__file__).resolve().parent
p=Path(sys.argv[1]).resolve()
raw=(here/'raw47-depth3.open').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d'
rows=raw.decode().splitlines()
names={}
for path in p.glob('Raw47D3*.lean'):
    m=re.fullmatch(r'Raw47D3(FAR|G|P)(\d+)',path.stem)
    if not m: continue
    i=int(m.group(2)); assert 0<=i<len(rows) and i not in names,i
    names[i]=path.stem
def key(i):
    s=rows[i].replace('_','')
    return sum((25 if s[j:j+3]=='---' else 4*(ord(s[j+2])-65)+2*int(s[j])+(s[j+1]=='R'))*26**(j//3) for j in range(0,36,3))
ids=sorted(names,key=key); keys=list(map(key,ids)); assert len(set(keys))==len(ids) and ids
N=len(ids)
if len(sys.argv)>2: assert N==int(sys.argv[2]),N
def tree(ks):
    if not ks:return '.empty'
    if len(ks)==1:return f'(.leaf {ks[0]})'
    j=len(ks)//2
    return f'(.branch {ks[j]} {tree(ks[:j])} {tree(ks[j:])})'
imports=[names[i] for i in ids]
entries=[]
for i,m in zip(ids,imports):
    n='BB6.Agent50.'+m
    entries.append(f'  ⟨{n}.p, '+(f'{n}.all_quotient' if m.startswith(('Raw47D3FAR','Raw47D3G')) else f'quotientSafe {n}.root {n}.bound')+'⟩')
body=(here/'Raw47AcceptedFast.template').read_text().replace('@@ENTRIES@@',',\n'.join(entries)).replace('@@TREE@@',tree(keys)).replace('@@N@@',str(N)).replace('@@REMAIN@@',str(len(rows)-N))
name=f'Raw47Accepted{N}'
(p/(name+'.lean')).write_text('\n'.join('import '+x for x in ['Raw47Depth3Cut','FastKey']+imports)+'\n'+body)
(p/'accepted-roster.json').write_text(json.dumps({
    'theorem': f'BB6.Agent50{name}.local_sound',
    'weighted_bound': 10006,
    'roster_sha256': hashlib.sha256(raw).hexdigest(),
    'closed_count': N,
    'remaining_count': len(rows)-N,
    'closed': [{'id': i, 'table': rows[i], 'module': names[i]} for i in sorted(names)],
    'remaining': [{'id': i, 'table': row} for i,row in enumerate(rows) if i not in names],
}, indent=2)+'\n')
print(name)
