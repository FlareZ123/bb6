"""Reconstruct exact affine-growth witnesses on the corrected Raw36 OPEN roster."""
from pathlib import Path
import hashlib,json,sys
from concurrent.futures import ProcessPoolExecutor
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE.parent/'agent46-raw13-cut'))
from autoword import infer
from emitGrowthBank import emit_growth

def decode(s):
    assert len(s)==12
    out=[]
    for c in s:
        n=ord(c)-65
        assert 0<=n<=24
        out.append('---' if n==24 else str(n//12)+('R' if n%12>=6 else 'L')+chr(65+n%6))
    return ''.join(out)

def word(w):
    return [w.pre,w.block,word(w.post)] if w.block else w.pre

def one(t):
    r=infer(t,budget=float('inf'))
    assert r and r[0]!='hole',t
    entry,f,(inc,path,(a,b)),_=r
    ops=[]
    for _,_,o in path:
        if o is None:
            if ops and isinstance(ops[-1],int):ops[-1]+=1
            else:ops.append(1)
        else:
            dr,lp,rp,I,O,k,L,R=o
            if dr=='L':lp,rp,L,R=rp,lp,R,L
            ops.append([dr,lp,rp,I,O,word(L),word(R),k])
    return dict(table=t,entry=entry,family=[f.q,word(f.l),word(f.r)],inc=inc,ops=ops,a=a,b=b)

if __name__=='__main__':
    tables=sorted(map(decode,(BASE/'sweep_tables.txt').read_text().split()))
    assert len(tables)==len(set(tables))==161
    with ProcessPoolExecutor(max_workers=4) as pool:
        bank=list(pool.map(one,tables))
    payload=json.dumps(bank,sort_keys=True,separators=(',',':'))
    assert hashlib.sha256(payload.encode()).hexdigest()=='a831464ee07644ab283ca4e5ca2045fb86aefe9749347d1c339b2bece5518015'
    (BASE/'raw36-sweep.json').write_text(payload+'\n')
    if len(sys.argv)>1:
        out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
        for i in range(0,len(bank),8):
            n=f'Raw36Sweep{i//8:02}'
            emit_growth(bank[i:i+8],out/(n+'.lean'),n)
    print(len(bank),'exact growth fixtures')
