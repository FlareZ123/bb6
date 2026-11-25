"""Reproduce raw112 checkpoint: exact ID partition and candidate proof terms.
All classifications remain pending source Lean audit.
Run discover.py 112 first; this script extends its FAR bank.
"""
from pathlib import Path
import subprocess, sys, hashlib, inspect
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent31-three-hole-tnf'))
import generate_sweeps as one
sys.path.insert(0,str(ROOT.parent/'agent10-tnf-multipump'))
import multi
ONE=[35,45,46,47,53,54,55,57,58,60,64,78,81,98,100,101,102,104,105,106,134,213,215,317,320,377,403,404,424,437,438,439,488,495,496,497,498,508,531,532,590,661,943,1078,1307,1341,1818,1848,1854,1890,1891,1892,1932,1965,1989,2033,2077,2078,2230,2233,2234,2236,2237,2238,2257,2386,2387,2392,2452,2455,2463,2520,2521,2522,2604,2606,2625,2694,2798,2804,2820,2884,2942,2943,2945,2961,2966,2967,2968,2970,2971,2972,3048,3049,3050,3062,3156,3158,3188,3190,3191,3192,3193,3195,3196,3198,3225,3250,3275,3354,3406,3486,3502,3530,3599,3613,3614,3615,3616,3617,3622,3685,3686,3697,3813,3951,3997,4002,4003,4007,4029,4141,4145,4340,4360,4477,4736,4737,4799,4804,4805,4806,4807,4808,4876,5033,5271,5542,5591,5602,5613,5614,5731,5958,5988,5989,5990,5992,6085,6086,6115,6160,6162,6186,6215,6466,6755,6835,6950,6993,6995,6996,7029,7491,7492,7493,7494,7495,7496,7497,7498,7499,7501,7502,7503,7557,7615,7646,7651,7683,9214,9406,9478,9479,9686,9744,9929,9991,10485,10759,10881,10900,10902,10907,11161,12421,12460,12479,12493,12494,12496,12498,12499,12867,12912]
TWO=[216,643,647,2125,2232,3011,3113,3118,3201,3332,4047,4137,4734,5041,5484,5621,6120,6128,9242,11305,12500,12589,12608]
LATE={429:(1211,10),423:(2062,10),425:(2327,10),9399:(2527,8),426:(4135,10),479:(91502,1)}
REMAIN=[44,56,59,378,421,422,427,428,430,440,441,442,443,1314,1319,1320,1321,2124,3287,3288,3289,3290,4710,6043,7885,10494,10554,10590,10953,11008,12495,12597,12918,12919]

def read_events(text):
    for block in text.split('end\n'):
        if not block.strip():continue
        rows=block.splitlines();i,s=rows[0].split();ev=[]
        for row in rows[1:]:
            t,d,q,h,l,r=row.split()
            ev.append((int(t),d,one.C(int(q),int(h),0,one.W('' if l=='-' else l),one.W('' if r=='-' else r))))
        yield int(i),s,ev

def widen():
    # Reuse upstream candidate algorithms with widened search bounds.
    # The output is accepted only by the generated universal Lean proof.
    src=inspect.getsource(one.candidate)
    src=src.replace('ev[:60]','ev[:100]').replace('i+12','i+20').replace('diff<=16','diff<=24').replace('j+12','j+20').replace('pump(p,start,target)','pump(p,start,target,1200)')
    exec(src,one.__dict__)
    src=inspect.getsource(multi.candidates)
    src=src.replace('ev[:55]','ev[:85]').replace('i+14','i+20').replace('diff<=16','diff<=24').replace('j+14','j+20')
    exec(src,multi.__dict__)

def main():
    folder=ROOT/'raw112';raw=(folder/'open.txt').read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='61773d08354491c09508929b83a5090b564b7808e7dabf6b045d353c9ea2bf01'
    opens=raw.decode().splitlines()
    covered={int(l.split(':')[0]) for l in (folder/'hits.txt').read_text().splitlines()}
    hits=subprocess.check_output([str(folder/'bank'),str(ROOT/'bank112extra.txt'),str(folder/'open.txt')],text=True)
    ext={int(l.split(':')[0]) for l in hits.splitlines()}
    assert len(ext-covered)==115
    covered|=ext
    assert len(covered)==13011
    assert set(range(len(opens)))-covered==set(ONE)|set(TWO)|set(LATE)|set(REMAIN)
    # Transparent independent simulation verifies each first-query time.
    for i,(t,s) in LATE.items():
        p=one.parse(opens[i]);assert p.count('---')==1
        q=h=0;ones=set()
        for _ in range(t):
            a=p[2*q+int(h in ones)]
            assert a!='---'
            if a[0]=='1':ones.add(h)
            else:ones.discard(h)
            h+=1 if a[1]=='R' else -1
            q=ord(a[2])-65
        assert 2*q+int(h in ones)==s and p[s]=='---'
    if '--sweeps' in sys.argv:
        subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'events.cpp'),'-o',str(folder/'events')],check=True)
        rows=''.join(f'{i} {opens[i]}\n' for i in sorted(ONE+TWO))
        events=subprocess.check_output([str(folder/'events'),'1000000','140'],input=rows,text=True)
        widen()
        parts=['import SweepPumping','set_option maxRecDepth 100000','set_option maxHeartbeats 0',
               'namespace BB6.Agent8Raw112Sweeps','open BB6Coverage BB6Coverage.Agent31Pump']
        for i,s,ev in read_events(events):
            p=one.parse(s)
            if i in ONE:
                ans=one.candidate(p,ev);assert ans is not None,i
                code,info=one.generate(i,p,ans)
            else:
                ans=multi.candidate(p,ev);assert ans is not None,i
                code,info=multi.generate(i,p,ans)
            parts.append(code);print(i,info)
        parts.append('end BB6.Agent8Raw112Sweeps')
        (folder/'Raw112Sweeps.lean').write_text('\n\n'.join(parts)+'\n')
    print('FAR',len(covered),'symbolic',len(ONE)+len(TWO),'late',len(LATE),'remaining',len(REMAIN))
    for i in REMAIN:print(i,opens[i])

if __name__=='__main__':main()
