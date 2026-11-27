"""Continue exact F421 principal macros from the computed secondary-zero frontier."""
from boundary import make, tailmake, cells, drain, carry, single, scan
import sys
sys.set_int_max_str_digits(0)

def seed():
    with open('prefix-state.txt') as f:
        n=int(f.readline()); K=int(f.readline())
        a,b,m=map(int,f.readline().split())
        cs=[(*map(int,line.split()),False) for line in f]
    assert n==32750 and len(cs)==m
    sc=[(32776,851959,0),(16387,557051,1),(860160,737276,1),
        (659454,778236,1),(2048,241660,0),(62463,219134,1),
        (63998,89087,1),(48382,101116,1),(1662,12415,1),
        (1854,27260,1),(926,8508,1),(847,8620,1),(1958,3527,1),
        (1106,2529,1),(41,2621,1)]
    S=sum(e<<i for i,(_,_,e) in enumerate(sc)); assert S==n
    news=[]
    for i,(z,r,e) in enumerate(sc):
        A=S>>i; t=(A+1)//2; s=A-t
        news.append((z+t,r-s,False))
    U=[('01',1),('10',159),('00',1),('10',355),('11',1),('00',1),
       ('10',112),('11',1),('00',1),('01',1)]
    return make(a,b,cs,tailmake(1703916-n,262124-n,news,U)),K,190+2*n

def short(w):
    return ' '.join({'10':'P','01':'Q','00':'Z','11':'H'}[p]+
                    (str(n) if n<10**7 else f'[{n.bit_length()}b]') for p,n in w)

if __name__=='__main__':
    w,K,od=seed(); end=od+(int(sys.argv[1]) if len(sys.argv)>1 else 20); actions=0
    while od<end:
        a,b,cs,tail=cells(w); V=sum(e<<i for i,(_,_,e) in enumerate(cs))
        if V:
            d=drain(w)
            if d is not None:
                w,k,c=d; K+=k; actions+=1; continue
            v,k,c=carry(w,V)
            if k:
                w=v; K+=k; actions+=1; continue
        L,term=scan(w)
        try:
            w,c,odd,t=single(w)
        except RuntimeError as exc:
            print('F1',od,'Kbits',K.bit_length(),exc.args); raise
        K+=1; od+=odd; actions+=1
        if odd:
            aa,bb,cc,tt=cells(w)
            print('odd',od,'term',term,'cells',len(cc),'a bits',aa.bit_length(),
                  'runs',len(w),'tail',short(tt[:10]),'last',short(tt[-12:]),flush=True)
    print('end',od,'Kbits',K.bit_length(),'actions',actions)
