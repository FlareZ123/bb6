"""Exact particle-event acceleration. All counts are high-level returns."""
from dataclasses import dataclass
from collections import Counter
from typing import Optional

def word_step(R):
    i=0
    while i<len(R) and R[i] in (2,3):i+=1
    p=R[:i]
    def phi(p):return [y for x in p for y in ([2] if x==2 else [1,0])]
    def bump(q,d):return [q[0]+d,*q[1:]] if q else [d-1]
    if i==len(R):return [2,*phi(p)]
    d=R[i];q=R[i+1:]
    if d==1:return [2,*phi(p),*bump(q,1)]
    if d==0:return [3,2,*p[:-1],*bump(q,p[-1])] if p else [3,*bump(q,2)]
    return None

def sparse_step(n,ds):
    j=0
    while j<len(ds) and ds[j][1]==3:j+=1
    out=[]
    if j==len(ds):
        for i,(p,d) in enumerate(ds):out.extend([(p+i+1,1),(p+i+2,0)])
        return n+j+1,out
    k,d=ds[j]
    if d>=4:return None
    if d==1:
        for i,(p,d) in enumerate(ds[:j]):out.extend([(p+i+1,1),(p+i+2,0)])
        shift=j;inc=1
    else:
        out.append((0,3));last3=j>0 and ds[j-1][0]==k-1;inc=3 if last3 else 2;shift=0
        out.extend((p+2,3) for p,d in ds[:j-int(last3)])
    i=j+1
    if k+1<n:
        v=2
        if i<len(ds) and ds[i][0]==k+1:v=ds[i][1];i+=1
        if v+inc!=2:out.append((k+1+shift,v+inc))
        out.extend((p+shift,d) for p,d in ds[i:]);return n+shift,out
    if inc-1!=2:out.append((n+shift,inc-1))
    return n+shift+1,out

@dataclass
class State:
    g:list[int]
    s:list[int]
    b:Optional[int]
    t:int=0
    def encode(self):
        ds=[];pos=0
        for gap,phase in zip(self.g,self.s):
            pos+=gap
            if phase==2:ds.append((pos,3));pos+=1
            elif phase==1:ds.append((pos,1));pos+=1
            else:ds.extend([(pos,1),(pos+1,0)]);pos+=2
        pos+=self.g[-1]
        if self.b is not None:ds.append((pos,self.b));pos+=1
        return pos,ds
    def charges(self):
        return [(self.g[i+1]+self.s[i+1]+(self.s[i]==2))%3 for i in range(len(self.s)-1)]
    def event(self):
        m=len(self.s);pows=[1]
        for i in range(m):pows.append(pows[-1]*3)
        v=sum(a*p for a,p in zip(self.s,pows))
        vnext=None if self.b is None and m else pows[-1]-1;j=m
        for i in range(m):
            ci=(v+pows[i])//pows[i+1]
            target=(ci+self.g[i+1])*pows[i+1]+2*pows[i]-1
            assert target>=v
            if vnext is None or target<vnext:vnext=target;j=i
        delta=vnext-v
        if delta:
            self.g[0]+=delta
            for i in range(m):
                self.g[i+1]-=(vnext+pows[i])//pows[i+1]-(v+pows[i])//pows[i+1]
                assert self.g[i+1]>=0
                self.s[i]=(vnext//pows[i])%3
            self.t+=delta
        old=State(self.g.copy(),self.s.copy(),self.b,self.t)
        if j==m:
            assert all(x==2 for x in self.s)
            if self.b==0:
                if m==0:self.g=[0,self.g[0]];self.s=[2];self.b=1
                elif self.g[-1]>0:
                    self.g=[0,self.g[0]+1,*self.g[1:-1],self.g[-1]-1];self.s=[2,*self.s];self.b=1
                else:
                    self.g=[0,self.g[0]+1,*self.g[1:]]
                    self.g[-2]+=1;self.g.pop();self.b=None
                kind='birth'
            else:
                if m==0 and self.b is None:return old,'RUNAWAY'
                self.g[0]+=1;self.s=[0]*m
                if self.b==1:self.b=0
                kind='wrap'
        else:
            assert self.s[j]==1 and all(x==2 for x in self.s[:j]) and self.g[j+1]==0
            if j+1<m:
                nextphase=self.s[j+1]
                boundary=nextphase==0 and j+2==m and self.g[-1]==0 and self.b is None
                if nextphase!=1 and not boundary:return old,'HAZARD'
            self.g[0]+=1;self.s[:j]=[0]*j
            if j+1<m:
                if nextphase==1:
                    self.g[j]+=1+self.g[j+2];del self.g[j+1:j+3];del self.s[j:j+2];kind='collision'
                else:
                    self.g[j]+=1;del self.g[j+1:j+3];del self.s[j:j+2];self.b=0;kind='boundary collision'
            else:
                self.s.pop();self.g.pop()
                if self.b is None:self.b=0
                elif self.b==0:self.b=1
                else:self.b=None;self.g[-1]+=1
                kind='drain'
        self.t+=1
        return old,kind

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--events',type=int,default=200000);p.add_argument('--check-events',action='store_true');args=p.parse_args()
    st=State([0],[],0);counts=Counter()
    for i in range(1,args.events+1):
        old,kind=st.event();counts[kind]+=1
        if kind in ('RUNAWAY','HAZARD'):
            print(kind,i,old);break
        if args.check_events:assert sparse_step(*old.encode())==st.encode(),(i,old,st)
        if kind=='birth' and old.s and old.g[0]%3:
            print('BAD BIRTH',i,old.t,len(old.s),old.g[0]%3,flush=True)
        if i%10000==0:print(i,st.t,len(st.s),dict(counts),flush=True)
    print('exceptional charges',[(i,c) for i,c in enumerate(st.charges()) if c!=1])
    print('final',st.t,len(st.s),st.g[-1],st.b)
