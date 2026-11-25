T='1RB0RF_1RC0LB_0RD1LC_1LD1RE_1RA1LB_---0RB'
def trim(a):return tuple(a[:next((i for i in range(len(a),0,-1) if a[i-1]),0)])
def gaps(s):return trim([len(x) for x in s.split('0')])
def get(a,n):return a[n] if n<len(a) else 0
def step(L,R):
 a=get(L,0);b,c,d,e=[get(R,j) for j in range(4)]
 if b:return a+7,trim(L[1:]),trim((0,a+b)+R[1:])
 if not c:return a+7,trim(L[1:]),trim((0,)*(a+1)+(d+2,)+R[3:])
 if c>=2:return 5,trim((a+1,)+L[1:]),trim((0,c-1)+R[2:])
 if d==0:
  if e==0:return 5,trim((3,a+1)+L[1:]),trim(R[4:])
  return 9,trim((a+1,)+L[1:]),trim((0,0,0,0,e-1)+R[4:])
 if d==1:raise ValueError('hole')
 if d==2:return 6,trim((0,0,2,a+1)+L[1:]),trim(R[3:])
 return 7,trim((0,2,a+1)+L[1:]),trim((0,d-3)+R[3:])
if __name__=='__main__':
 p=[s[i:i+3] for s in T.split('_') for i in (0,3)]
 q=0;l=r='';L=(1,);R=();total=1;count=0
 for t in range(1000000):
  if q==1 and (not l or l[0]=='0'):
   assert t==total and (gaps(l[1:]),gaps(r))==(L,R)
   c,L,R=step(L,R);total+=c;count+=1
  w,d,nq=p[2*q+int(l[0] if l else '0')]
  if d=='R':l=(r[0] if r else '0')+w+l[1:];r=r[1:]
  else:l=l[1:];r=w+r
  q=ord(nq)-65
 print('verified',count,total)
