"""Reproduce candidate counts, FAR bank and symbolic proof-term proposals."""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, subprocess, sys

ROOT = Path(__file__).resolve().parent
SPECS = {
    117: ('1RD', 'e575d2af8ea45e6016d9dfbab632388f361cd1410eff06b51f4029476bdee3f6',
          5570, 7903, 143850, 32350, 5530),
    112: ('1LC', '61773d08354491c09508929b83a5090b564b7808e7dabf6b045d353c9ea2bf01',
          13289, 25004, 446232, 115572, 12896),
}
ONE = [26,28,171,619,827,828,829,830,832,1022,1025,1028,1108,1848,1990,2182,2185,2435,2677,2681,2701,2779,3442,3633,3634,3828,3880,3921,4080,4625]
HARD = [397,4215,4216]
LATE = 2707
TWO = {
    2003: (30, 2, [('0',False),('00',True),('100',False),('1',True),('01001',False)], [('000',False),('00',True),('1001',False),('1',True),('01001',False)], True),
    2013: (1, 1, [('0',False),('011',True),('1011',True),('1',False)], [('0011',False),('011',True),('1011',False),('1011',True),('1',False)], True),
    2703: (31, 2, [('01',False),('011',True),('111',False),('011',True),('011',False)], [('01011',False),('011',True),('111011',False),('011',True),('011',False)], True),
    2914: (1, 1, [('0',False),('1011',True),('1',False),('01',True)], [('01011',False),('1011',True),('101',False),('01',True)], True),
    1747: (17, 1, [('101010',False),('10'*8,True)], [('101010'+'10'*8,False),('10'*8,True)], False),
    3890: (124, 5, [('0000000000001001',False),('0001000000101',True)], [('00000000000010010001000000101',False),('0001000000101',True)], False),
}

def sweeps(opens, folder):
    sys.path.insert(0, str(ROOT.parent/'agent31-three-hole-tnf'))
    import generate_sweeps as one
    sys.path.insert(0, str(ROOT.parent/'agent10-tnf-multipump'))
    import multi
    # Reuse the same discovery, with enough symbolic phases to replay the local candidates.
    old_pump = one.pump
    one.pump = lambda p,st,tg,*a: old_pump(p,st,tg,1200)
    parts = ['import SweepPumping','set_option maxRecDepth 100000','set_option maxHeartbeats 0',
             'namespace BB6.Agent8Raw117Sweeps','open BB6Coverage BB6Coverage.Agent31Pump']
    for i in ONE:
        p=one.parse(opens[i]); ans=one.candidate(p,one.concrete_events(p,10000))
        assert ans is not None, i
        code,info=one.generate(i,p,ans);parts.append(code);print(i,info)
    for i,(entry,q,s,t,left) in TWO.items():
        p=one.parse(opens[i]); s,t=multi.clean(tuple(s)),multi.clean(tuple(t))
        st=multi.C(q,s if left else (),() if left else s)
        tg=multi.C(q,t if left else (),() if left else t)
        ans=multi.pump(p,st,tg,3000);assert ans is not None,i
        code,info=multi.generate(i,p,(entry,st,tg,ans));parts.append(code);print(i,info)
    parts.append('end BB6.Agent8Raw117Sweeps')
    (folder/'Raw117Sweeps.lean').write_text('\n\n'.join(parts)+'\n')

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('raw',type=int,choices=SPECS)
    ap.add_argument('--sweeps',action='store_true')
    a=ap.parse_args()
    raw=a.raw; divergence,digest,nopen,nsplit,ncycle,nlast,nfar=SPECS[raw]
    folder=ROOT/f'raw{raw}';folder.mkdir(exist_ok=True)
    parent=f'1RB---_1RC---_0RD---_1LD1RE_---{divergence}_------'
    for name,src in [('enumerate',ROOT.parent/'agent2-tnf-raw99/enumerate.cpp'),
                     ('bank',ROOT.parent/'agent8-tnf-six/bank.cpp')]:
        subprocess.run(['g++','-std=c++17','-O3',str(src),'-o',name],cwd=folder,check=True)
    subprocess.run([str(folder/'enumerate'),parent],cwd=folder,check=True)
    data=(folder/'open.txt').read_bytes();assert hashlib.sha256(data).hexdigest()==digest
    opens=data.decode().splitlines();assert len(opens)==len(set(opens))==nopen
    count=Counter()
    def visit(t):
        count[t[0]]+=1
        if t[0]=='split':
            for k in t[3]:visit(k)
    visit(json.loads((folder/'tree.json').read_text()))
    assert count==Counter(split=nsplit,cycle=ncycle,last=nlast,open=nopen)
    hits=subprocess.check_output([str(folder/'bank'),str(ROOT/f'bank{raw}.txt'),str(folder/'open.txt')],text=True)
    (folder/'hits.txt').write_text(hits)
    covered={int(line.split(':')[0]) for line in hits.splitlines()}
    assert len(covered)==nfar
    remaining=set(range(nopen))-covered
    if raw==117:
        assert remaining==set(ONE)|set(TWO)|set(HARD)|{LATE}
        remaining-=set(ONE)|set(TWO)|{LATE}
        if a.sweeps:sweeps(opens,folder)
    for i in sorted(remaining):print(i,opens[i])
    print('candidate FAR',len(covered),'remaining',len(remaining))

if __name__=='__main__':main()
