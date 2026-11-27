"""Generate the authenticated primary seed, or check the exact truncated endpoint."""
import hashlib
import sys
from pathlib import Path
from verify_tertiary import action, guard, unpack
from cross_zero import seed
from boundary import drain

sys.set_int_max_str_digits(0)

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def prepare():
    assert digest('prefix-state.txt')=='f5e445d70cf1b2fc1982201911c6557b6c2b9fd5a1b9ee082e21be31758f2f87'
    w,K,odd=seed()
    while odd<65700:
        w,k,o=action(w);K+=k;odd+=o
    w,k,_=drain(w)
    assert hashlib.sha256(('\n'.join(f'{p} {n}' for p,n in w)+'\n').encode()).hexdigest()=='a74ba0026d9a3d59b37216703669dd8d7c59f552c63cd5fa3c7efd38de75fab2'
    a,b,cs,*_=unpack(w)
    assert guard(*unpack(w))==2**8214-1 and len(cs)==3
    Path('seed-primary.txt').write_text(f'{a} {b}\n'+''.join(f'{p} {q}\n' for p,q in reversed(cs)))
    assert digest('seed-primary.txt')=='2d0c2fe4885749c07cf91f2e1651d10cddc0d61834b9282d0c9a391abc273ffa'

def check():
    assert digest('primary-prefix-input.txt')=='4837e4673a9c08df779f852717c8de14829077fa47c82947ee7d18e5d6c026ba'
    assert digest('primary-prefix-output.txt')=='6f65e53de761617f6521cb49fb4e220207f95be4ba81ce9848184f7fb5f74dae'
    rs=[tuple(map(int,l.split())) for l in Path('primary-prefix-output.txt').read_text().splitlines()]
    assert rs[0]==(0,0)
    rows=rs[1:];assert len(rows)==198 and rows[-1][0]==0
    s=2**8214-1;t=2*s+1
    a=[];h=0;carry=0;prev=3
    for p,q in rows:
        cap=2*h+1
        if q>cap:
            a.append((q-cap,prev+h+1+carry));h+=h+1;carry=0
        else:
            assert q%2==1
            v=(q+1)//2;h+=v;carry+=prev+v
        prev=p-1
    assert len(a)==198
    z=[(a[i+1][1]-(2*(1<<i)-1) if i+1<len(a) else 0,p-1+(1<<i)) for i,(p,q) in enumerate(a)]
    assert z==[(p,q-(1<<i)) for i,(p,q) in enumerate(rows)] # P unchanged, Q decreases by B
    assert all(p>=2*(1<<i)*t+3 for i,(p,q) in enumerate(z[:-1]))
    assert all(q>=(1<<i)+2 for i,(p,q) in enumerate(z))
    print('Exact known far rows after zero:',len(z),'known P:',len(z)-1)
    print('First ten floor P/(2BT):',[p//(2*(1<<i)*t) for i,(p,q) in enumerate(z[:10])])
    print('Nondivisible known P:',sum(bool(p%(2<<i)) for i,(p,q) in enumerate(z[:-1])))

if __name__=='__main__':
    if sys.argv[1:] == ['prepare']: prepare()
    elif sys.argv[1:] == ['check']: check()
    else: raise SystemExit('usage: primary_events.py prepare|check')
