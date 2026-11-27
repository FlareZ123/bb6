"""Paper-level candidate orbit, not a source proof.
All bank exponents even on the candidate invariant. Bank codes A/B/C,
suffix rank 0..5, n is the number of 115/644/322 triplets.
D(k,h) means DL(6^k4,4^h62). Terminal formulas still require composition.
"""
from collections import Counter

def drain(p,n,s):
 z=6*n+s;k=max(0,(z-1)//11);z-=11*k;return p+12*k,*divmod(z,6)
def D(k,h=8):
 h=k+h;n,s=divmod(k,6)
 if h%2:return 'B',2*h+2,n,s
 return 'B',2*h+11,n+(s==5)-2,(s+1)%6

def A0(p):return Ccounter(p,p-7,7,0)
def Ccounter(p,k,m,s):
 t=m+k;n,r=divmod(s+k+2,6)
 if t%2==0:return 'C',2*t+6,n,r
 return 'C',2*t+15,n+(r==5)-2,(r+1)%6

def BseedGeneral(k,u,v,s):
 p=k+v+1;n,s=divmod(k+s,6);n+=u+(s==5)-1;s=(s+1)%6
 if p%2:return 'A',2*p+6,n,s
 return 'A',2*p+15,n+(s==5)-2,(s+1)%6
def Bseed(p):return BseedGeneral(p-4,0,3,1)

def mixed_even(p):
 j=(p-8)//2;n,s=divmod(j+5,6)
 if p%4==2:return 'B',2*p+6,n,s
 return 'B',3*p+20,p//4-1,1

def step(c):
 b,p,*rest=c
 if b=='D':return D(p,*rest)
 if b=='A0':return A0(p)
 if b=='A2':return D(p-4)
 if b=='B0':return Bseed(p)
 n,s=rest
 p,n,s=drain(p,n,s)
 if b=='A':
  if n==0:
   if s==0:return Ccounter(p,p-2,0,2)
   if s==1:return 'D',p+3
   if s==2:return 'D',p+1
   if s==3:
    if p%2==0:return mixed_even(p)
    return 'unknown',b,p,n,s
   if s==4:return 'B0',p+11
   if s==5:return 'D',p+5
  if n==1:
   if s in (0,1):return 'A0',p+12
   if s==2:return 'B0',p+13
   if s==3:return Ccounter(p,p+4,10,0)
   if s==4:return 'A0',p+16
   if s==5:return 'A',p+12,0,0
 if b=='B':
  if n==0:
   if s==0:return BseedGeneral(p-4,0,6,1)
   if s==1:return 'B0',p+5
   if s==2:return BseedGeneral(p-2,1,0,1)
   if s==3:return 'A0',p+8
   if s==4:return 'A0',p+6
   if s==5 and p%2==0:
    if p%4==0:return 'C',3*p+18,p//4-1,1
    n,s=divmod(p//2+1,6);return 'C',2*p+4,n,s
  if n==1:
   if s==0:return 'D',p+5
   if s==1:return 'A0',p+10
   if s in (2,3):return 'B0',p+13
   if s==4:return 'D',p+7
   if s==5:return 'B',p+12,0,0
 if b=='C':
  if n==0:
   if s==0:return 'D',p-4,11
   if s==1:return 'A2',p+5
   if s==2:
    n,s=divmod(p+4,6)
    if p%2==0:return 'B',2*p+8,n,s
    return 'B',2*p+17,n+(s==5)-2,(s+1)%6
   if s==3:return 'B0',p+11
   if s==4:return 'B0',p+9
   if s==5 and p%2==0:
    if p%4==0:
     n,s=divmod(p//2,6);return 'A',2*p+10,n,s
    return 'A',3*p+38,p//4-2,0
  if n==1:
   if s==0:return 'A0',p+12
   if s==1:return 'B0',p+13
   if s in (2,3):return 'A2',p+13
   if s==4:return 'A0',p+14
   if s==5:return 'C',p+12,0,0
 return 'unknown',b,p,n,s
if __name__=='__main__':
 c=('A',12472,0,3);seen=Counter()
 for i in range(100000):
  if c[0]=='unknown':raise RuntimeError((i,c))
  if c[0] in 'ABC':
   p,n,s=drain(*c[1:]);assert p%2==0 and p>=20 and 0<=n<=1 and 0<=s<=5;seen[(c[0],n,s)]+=1
  c=step(c)
 print('candidate transitions',i+1,'terminal cases',len(seen),'minimum visits',min(seen.values()))
