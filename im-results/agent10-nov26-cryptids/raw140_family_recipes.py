"""Exact affine recipes for the remaining related Raw140 siblings.

All paths proposed by concrete traces are symbolically replayed by the shared
raw14086_local checker. The Lean emitter checks every local exit again.
"""
import json, sys
from pathlib import Path
import raw14086_local as r
i=int(sys.argv[1])
a,f={28:(21,0),81:(23,17),39:(21,6),77:(23,1),88:(23,19)}[i]
r.TAB=(7,a,11,12,15,1,6,18,4,17,f,24)
r.E=r.exits(r.TAB)
S=dict(r.S)
if i==81:
    for n in ['cSeed','b62','b6221','b6405','a542','a1121','a1155','c315','c3242']:
        S.pop(n)
    for n,g in [('b62542',r.A('3^p+31 2','')),('a5215',r.A('3^p+30 2','2')),('c35221',r.B('5^p+34',''))]:
        S[n]=(S[n][0],g)
elif i in (39,77,88):
    inc=10 if i==88 else 12
    keep={'oddPump','oddLow','oddStart','oddInit','evenLow','aSeed','bSeed','seedCounter','cOddStart','cOddFinish','cOddPump','cInit','bFour'}
    S={k:v for k,v in S.items() if k in keep}
    S.update({
      'aPump':(r.A('3^p+24 2','1 1 5 1 1 5 Y'),r.A(f'3^p+{24+inc} 2','Y')),
      'bPump':(r.B('5^p+24','6 4 4 6 4 4 Y'),r.B(f'5^p+{24+inc}','Y')),
      'cPump':(r.A('3^p+24 2','2 3 2 2 3 2 2 Y'),r.A(f'3^p+{24+inc} 2','2 Y')),
    })
    # Ordered by bank type, odd rank 1/3/5, remainder 0/1.
    ends = {
      'a':[('B0',7),('A0',12),('A0',6),('B0',13),('B0',11),('A2',15)],
      'b':[('A0',4),('A2',9),('D',1),('B0',13),('B0',7),('A2',11)],
      'c':[('B0',7),('A0',12),('A0',8),('A2',13),('D',3),('A0',14)],
    } if i!=88 else {
      'a':[('B0',5),('A0',10),('A2',13),('B0',11),('B0',9),('D',7)],
      'b':[('A0',2),('A2',7),('D',-1),('B0',11),('A0',14),('A2',9)],
      'c':[('B0',5),('A0',10),('A0',6),('A2',11),('B0',17),('A0',12)],
    }
    tails={'a':['152','5215','11511'],'b':['64','6421','62542'],'c':['32','325','35221']}
    trips={'a':'115','b':'644','c':'322'}
    def cfg(tag,p,right=''):
        if tag=='A0':return r.A(f'3^p+{p} 2',right)
        if tag=='A2':return r.A(f'3^p+{p} 2','2')
        if tag=='B0':return r.B(f'5^p+{p}',right)
        if tag=='D':return r.D(f'6^p+{p} 4','4^8 6 2')
        raise ValueError(tag)
    terminals={}
    for b in 'abc':
        for j,tail in enumerate(tails[b]):
            for rem in range(2):
                name=f'{b}{2*j+1}{rem}'
                tag,delta=ends[b][2*j+rem]
                offset=25 if i==88 and name=='b30' else 24
                right=' '.join(('2' if b=='c' else '')+trips[b]*rem+tail)
                start=cfg('B0' if b=='b' else 'A0',offset,right)
                goal=cfg(tag,offset+delta)
                S[name]=(start,goal)
                terminals[name]={'start':start,'end':goal}
    Path(__file__).with_name(f'raw140-{i}-paired-terminals.json').write_text(json.dumps(terminals,separators=(',',':')))
print(json.dumps({n:dict(start=s,end=t,path=r.recipe(s,t)) for n,(s,t) in S.items()},separators=(',',':')))
