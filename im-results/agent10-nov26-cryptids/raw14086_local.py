"""Exact affine local-rule certificate generator for Raw140 sibling 86.

No third-party dependencies. Run with Python 3; writes raw14086-recipes.json
beside this file. Two concrete traces propose paths; symbolic replay proves
their validity at every nonnegative parameter, with opaque contexts.
"""
import json
from pathlib import Path

TAB=(7,23,11,12,15,1,6,18,4,17,11,24)
def exits(tab):
 E={}
 for Q in range(6):
  for D in range(2):
   for B in range(8):
    p=0 if D else 2;r=Q;b=B;k=0
    while 0<=p<3 and k<145:
     c=tab[2*r+((b>>p)&1)]
     if c==24: break
     b=(b&~(1<<p))|(((c>>1)&1)<<p);r=c>>2;p+=1 if c&1 else -1;k+=1
    if p<0 or p>=3:E[Q,D,str(B)]=(r,int(p>=3),str(b),k)
 return E
E=exits(TAB)
def step(st):
 q,d,L,R=st;S=R if d else L;b=S[0] if S else '0';z=E[q,d,b];n=1
 if z[:2]==(q,d) and S:n=len(S)-len(S.lstrip(b))
 if d:R=R[n:]
 else:L=L[n:]
 r,D,c,k=z
 if D:
  if L or c!='0':L=c*n+L
 else:
  if R or c!='0':R=c*n+R
 return (r,D,L,R),n*k,'ABCDEF'[q]+('R' if d else 'L')+b+('^'+str(n) if n!=1 else '')

A=lambda l,r:(0,1,l,r)
B=lambda l,r:(1,1,l,r)
D=lambda l,r:(3,0,l,r)
ER=lambda l,r:(4,1,l,r)
BL=lambda l,r:(1,0,l,r)
P='3^p+24 2';Q='5^p+24'
S={
 'aPump':(A(P,'1 1 5 Y'),A('3^p+29 2','Y')),
 'bPump':(B(Q,'6 4 4 Y'),B('5^p+29','Y')),
 'cPump':(A(P,'2 3 2 2 Y'),A('3^p+29 2','2 Y')),
 'oddPump':(A('3^p+3 2','0 1 1 Y'),A('3^p+7 2','0 Y')),
 'oddLow':(A(P,'0 1 5 Y'),A('3^p+29 2','Y')),
 'oddStart':(ER('2','1 1 1 Y'),A('3 3 3 2','0 1 Y')),
 'oddInit':(ER('3^p+24','1 Y'),ER('2','1^p+24 5 Y')),
 'evenLow':(A(P,'0 5 Y'),ER('1 3^p+25 2','Y')),
 'aSeed':(A(P,'2'),D('6^p+20 4','4^8 6 2')),
 'cSeed':(A(P,'2 3 1'),D('6^p+22 4','4^8 6 2')),
 'bSeed':(B(Q,''),ER('1 3^3 5^p+20','1 5 2')),
 'seedCounter':(A('3^7 X',''),ER('2 7 X','3 2^7 3 1')),
 'cOddStart':(A(P,'2 2 3 2 2 Y'),ER('2 6^p+26 4','3 2 2 Y')),
 'cOddFinish':(BL('6^p+26 4','2^4 3 2 2 Y'),A('3^p+31 2','2^3 Y')),
 'cOddPump':(A('3^p+2 2','2 2 2 Y'),A('3^p+6 2','2 Y')),
 'cInit':(BL('','2 2 Y'),A('3 3 2','2 Y')),
 'bFour':(B(Q,'4 4 Y'),B('5^p+28','Y')),
}
for s,tag,inc in [('62','B',2),('64','A2',2),('6221','A',3),('6421','B',6),('6405','B',6),('62542','A2',4)]:
 S['b'+s]=(B(Q,' '.join(s)),B(f'5^p+{24+inc}','') if tag=='B' else A(f'3^p+{24+inc} 2','2' if tag=='A2' else ''))
for s,tag,inc in [('542','A2',2),('152','A',5),('1121','A',5),('5215','B',6),('1155','A',6),('11511','B',9)]:
 S['a'+s]=(A(P,' '.join(s)),B(f'5^p+{24+inc}','') if tag=='B' else A(f'3^p+{24+inc} 2','2' if tag=='A2' else ''))
for s,tag,inc in [('32','A',5),('315','B',6),('325','A2',6),('3242','A2',6),('35221','A',7)]:
 S['c'+s]=(A(P,'2 '+' '.join(s)),B(f'5^p+{24+inc}','') if tag=='B' else A(f'3^p+{24+inc} 2','2' if tag=='A2' else ''))

def count(x):
 if x is None:return 0,1
 if x.startswith('p'):return 1,int(x[2:] or 0)
 return 0,int(x)
def push(st,b,c):
 if not st and b=='0':return
 if st and st[0][0]==b:st[0]=(b,(st[0][1][0]+c[0],st[0][1][1]+c[1]))
 else:st.insert(0,(b,c))
def parse(s):
 st=[]
 for tok in reversed(s.split()):
  if tok in ('X','Y'):st.insert(0,(tok,(0,1)))
  else:
   w=tok.split('^');push(st,w[0],count(w[1] if len(w)>1 else None))
 return st
def concrete(s,p):return ''.join(b*(a*p+c) for b,(a,c) in parse(s))
def inst(st,p):
 q,d,l,r=st;return q,d,concrete(l,p),concrete(r,p)
def find(s,t,p):
 st=inst(s,p);goal=inst(t,p);out=[]
 for _ in range(2000):
  if st==goal:return out
  st,k,tok=step(st);x=tok.split('^');out.append((x[0],int(x[1]) if len(x)>1 else 1))
 raise ValueError('no target')
def verify(s,t,seq):
 q,d,l,r=s;L,R=parse(l),parse(r)
 for tok,c in seq:
  assert q=='ABCDEF'.index(tok[0]) and d==(tok[1]=='R')
  b=tok[2];r,D,v,k=E[q,d,b];T=R if d else L
  if c!=(0,1):assert (r,D)==(q,d),'non-sweep'
  if not T:assert b=='0' and c==(0,1)
  else:
   x,z=T.pop(0);assert x==b,(tok,T,x)
   rem=(z[0]-c[0],z[1]-c[1]);assert min(rem)>=0,(tok,c,z)
   if rem!=(0,0):T.insert(0,(x,rem))
  push(L if D else R,v,c);q,d=r,D
 assert (q,d,L,R)==(t[0],t[1],parse(t[2]),parse(t[3])),(s,t,q,d,L,R)
def recipe(s,t):
 a,b=find(s,t,0),find(s,t,1);assert len(a)==len(b)
 seq=[]
 for (x,m),(y,n) in zip(a,b):
  assert x==y and n-m in (0,1);seq.append((x,(n-m,m)))
 verify(s,t,seq);return seq
if __name__=='__main__':
 out={}
 for name,(s,t) in S.items():
  seq=recipe(s,t);out[name]={'start':s,'end':t,'path':seq};print(name,len(seq),'verified')
 q=0;h=0;ones=set()
 for _ in range(6892):
  c=TAB[2*q+int(h in ones)];assert c!=24
  if c&2:ones.add(h)
  else:ones.discard(h)
  q=c>>2;h+=1 if c&1 else -1
 assert q==0 and h==38
 assert ones=={h-3*i+j for i in range(1,41) for j in range(3) if ((3 if i<40 else 2)>>j)&1}|{h+1}
 print('root verified; symbolic local rules',len(out))
 Path(__file__).with_name('raw14086-recipes.json').write_text(json.dumps(out,separators=(',',':')))
