"""Arbitrary-precision F421 pair-run macro and complete carry drain.
Uses the established frontier_map token table. No bounded machine integers.
"""
from collections import defaultdict
from frontier_map import RULES

def push(w,p,n=1):
    if not n:return
    assert n>0
    if w and w[-1][0]==p:w[-1]=(p,w[-1][1]+n)
    else:w.append((p,n))

def pack(s):
    if len(s)%2:s+='0'
    w=[]
    for i in range(0,len(s),2):push(w,s[i:i+2])
    if w and w[-1][0]=='00':w.pop()
    return w

def scanedge(pfx,p):
    for i,b in enumerate(p,1):
        pfx+=b
        if pfx in ('00','011','111'):return pfx,i,True
        if pfx in RULES:pfx=''
    return pfx,2,False

def scan(w):
    l=0;pfx=''
    for p,n in w+[('00',3)]:
        while n:
            s,i,done=scanedge(pfx,p)
            if done:return l+i,s
            if s==pfx:l+=2*n;break
            pfx=s;l+=2;n-=1
    raise AssertionError(w)

def edge(st,p):
    pfx,buf=st;out=''
    for i,b in enumerate(p):
        pfx+=b
        if pfx=='111':raise ValueError(st,p)
        if pfx in RULES:
            x=buf+RULES[pfx];pfx='';i2=len(x)//2*2
            for j in range(0,i2,2):
                q=x[j:j+2];assert q!='00';out+='00' if q=='11' else q
            buf=x[i2:]
        elif pfx in ('00','011'):
            assert len(buf)==(1 if pfx=='00' else 0)
            out+=('01' if pfx=='00' else '10')+p[i+1:]
            return None,out
    return (pfx,buf),out

class Output:
    def __init__(self):self.w=[];self.buf='';self.rep=False;self.leading=0;self.q=0
    def pair(self,p,n=1,count=True):
        if not n:return
        if count and p=='01':self.q+=n
        if not self.rep:
            if p=='10':self.leading+=n;push(self.w,p,n);return
            assert p=='00';push(self.w,'10');push(self.w,'01');self.rep=True;n-=1
        push(self.w,p,n)
    def emit(self,s):
        s=self.buf+s;i2=len(s)//2*2
        for j in range(0,i2,2):self.pair(s[j:j+2])
        self.buf=s[i2:]
    def tail(self,p,n):
        if not n:return
        if not self.buf:self.pair(p,n,False);return
        self.pair(self.buf+p[0],1,False);self.pair(p[::-1],n-1,False);self.buf=p[1]

def single(w):
    L,term=scan(w)
    if term=='111':raise RuntimeError('F1',L-1)
    odd=L%2;o=Output();o.pair('00' if odd else '10');st=('', '' if odd else '1')
    for p,n in w+[('00',3)]:
        if st is None:o.tail(p,n);continue
        while n:
            s,out=edge(st,p)
            if s==st:
                assert len(out) in (0,2) and not o.buf
                if out:o.pair(out,n)
                break
            o.emit(out);n-=1;st=s
            if st is None:o.tail(p,n);break
    assert st is None and o.rep
    if o.buf:o.tail('00',1)
    if o.w[-1][0]=='00':o.w.pop()
    b=o.q-(term=='00');L2=2*(o.leading+1);cost=L+2*(L//2)+4*b+2+2*L2+2
    return o.w,cost,odd,term

def cells(w):
    if len(w)<2 or w[0][0]!='10' or w[1][0]!='01' or w[1][1]<2:return 0,0,[],w
    a,b=w[0][1],w[1][1];pos=2;cs=[]
    while pos<len(w) and w[pos][0]=='10':
        j=pos+1;e=False
        if j<len(w) and w[j]==('00',1):e=True;j+=1
        if j==len(w) or w[j][0]!='01' or w[j][1]<2:break
        cs.append((w[pos][1],w[j][1],e));pos=j+1
    return a,b,cs,w[pos:]

def make(a,b,cs,tail):
    w=[];push(w,'10',a);push(w,'01',b)
    for p,q,e in cs:push(w,'10',p);push(w,'00',int(e));push(w,'01',q)
    for p,n in tail:push(w,p,n)
    return w

def carry(w,limit):
    a,b,cs,tail=cells(w);V=sum(e<<i for i,(_,_,e) in enumerate(cs))
    if not V:return w,0,0
    k=min(V,limit)
    for i,(p,q,e) in enumerate(cs):
        d=1<<i;k=min(k,V%d+(p-1)*d)
    if not k:return w,0,0
    W=V-k;cost=8*k*(a+b)+12*k*(k-1)+16*k;out=[]
    for i,(p,q,e) in enumerate(cs):
        A=V>>i;B=W>>i;n=A-B;t=(A+1)//2-(B+1)//2;s=n-t
        assert n<p;cost+=4*(n*p-n*(n-1)//2)+8*(s*q+s*(s-1)//2+(A%2)*s)
        out.append((p-n,q+t,B%2))
    return make(a+2*k,b+k,out,tail),k,cost

def drain(w):
    """Complete regular drain with terminal deletion; None on nonterminal deletion."""
    a,b,cs,tail=cells(w);H=cost=0;rows=[]
    for p,q,e in reversed(cs):
        e=int(e);cap=2*H+e;n=min(p,cap)
        if p<=cap and p%2!=e:return None
        t=(n+e)//2;s=n-t
        cost+=4*(n*p-n*(n-1)//2)+8*(s*q+s*(s-1)//2+e*s+(H-s)*(q+t))
        rows.append((p-n,q+t,False));H+=t
    K=H;cost+=8*K*(a+b)+12*K*(K-1)+16*K
    return make(a+2*K,b+K,reversed(rows),tail),K,cost

def tailcells(tail):
    if len(tail)<5 or tail[0][0]!='10' or tail[1]!=('00',1) or tail[2][0]!='10':return None
    x,y=tail[0][1],tail[2][1];cs=[];i=3
    while i<len(tail):
        j=i;e=tail[j]==('00',1);j+=e
        if j+1>=len(tail) or tail[j][0]!='01' or tail[j][1]<2 or tail[j+1][0]!='10' or tail[j+1][1]<2:break
        cs.append((tail[j][1],tail[j+1][1],e));i=j+2
    return x,y,cs,tail[i:]

def tailmake(x,y,cs,U):
    w=[];push(w,'10',x);push(w,'00');push(w,'10',y)
    for z,r,e in cs:push(w,'00',int(e));push(w,'01',z);push(w,'10',r)
    for p,n in U:push(w,p,n)
    return w

def twist(tail):
    w=[];b='0'
    for p,n in tail:
        push(w,b+p[0]);push(w,p[::-1],n-1);b=p[1]
    push(w,b+'0')
    if w[-1][0]=='00':w.pop()
    return w

def oddprefix(b,cs):
    out=[];prev=b
    for p,q,e in cs:
        assert not e
        out.append((prev,p-1,True));prev=q
    return out,prev

def cycle(w,check=False):
    """Conditional outer decrement: three boundary macros and three complete drains."""
    a,b,cs,tail=cells(w);C=tailcells(tail)
    if C is None or any(e or p<2 for p,q,e in cs):return None
    x,y,sc,U=C;S=sum(e<<i for i,(_,_,e) in enumerate(sc))
    if S==0 or x<4 or y<3:return None
    j=(S&-S).bit_length()-1
    if any(r<3 for z,r,e in sc[:j]):return None
    old=w;cost=8*(a+b)+4*(sum(p for p,q,e in cs)+x)+8*sum(q for p,q,e in cs)+16
    K=1;w=make(a+2,b+1,[(p-1,q,True) for p,q,e in cs], [('10',x-1),('01',1),('10',y)]+tail[3:])
    if check:assert single(old)==(w,cost,0,'00')
    d=drain(w)
    if d is None:return None
    w,k,c=d;K+=k;cost+=c
    a,b,cs,tailA=cells(w);assert tailA==[('10',x-1),('01',1),('10',y)]+tail[3:]
    if any(p<3 for p,q,e in cs):return None
    old=w;L=2*(a+b+sum(p+q for p,q,e in cs)+x)+1
    c=2*L+7+4*(a+sum(p-1 for p,q,e in cs)+x-2);cost+=c;K+=1
    marked,last=oddprefix(b,cs);marked.append((last,x-2,True));marked.append((1,y-1,False))
    w=make(1,a+1,marked,twist(tail[3:]))
    if check:assert single(old)==(w,c,1,'011')
    d=drain(w)
    if d is None:return None
    w,k,c=d;K+=k;cost+=c
    a,b,cs,tailB=cells(w);assert cs[-1]==(1,y-1,False) and cs[-2][1]==x-1
    if any(p<3 for p,q,e in cs[:-1]):return None
    old=w;L=2*(a+b+sum(p+q for p,q,e in cs)+sum(z+r for z,r,e in sc[:j]))+3
    c=2*L+7+4*(a+sum(p-1 for p,q,e in cs)+sum(z for z,r,e in sc[:j]));cost+=c;K+=1
    marked,last=oddprefix(b,cs[:-1]);assert last==x-1
    news=[(z,r-1,True) if i<j else (z+1,r,False) if i==j else (z,r,e) for i,(z,r,e) in enumerate(sc)]
    w=make(1,a+1,marked,tailmake(x-1,y-1,news,U))
    if check:assert single(old)==(w,c,1,'00')
    d=drain(w)
    if d is None:return None
    w,k,c=d;return w,K+k,cost+c

def baseline(w):
    k=c=0
    while True:
        a,b,cs,tail=cells(w);V=sum(e<<i for i,(_,_,e) in enumerate(cs))
        if not V:return w,k,c
        v,n,t=carry(w,V)
        if n:w=v;k+=n;c+=t;continue
        j=(V&-V).bit_length()-1
        if any(p==1 for p,q,e in cs[:j]):return None
        w,t,odd,term=single(w);assert not odd and term=='00';k+=1;c+=t

def test():
    import random
    rng=random.Random(41)
    for _ in range(10000):
        w=make(rng.randrange(1,9),rng.randrange(2,9),
            [(rng.randrange(1,50),rng.randrange(2,15),rng.randrange(2)) for j in range(rng.randrange(1,9))],
            [('10',3),('00',2),('10',2)])
        assert drain(w)==baseline(w)
    print('10000 drain comparisons passed')

def run(n,by_macros=False,use_cycle=False,check=False):
    import hashlib
    w=pack('10010101');i=od=0;tc=24;stats=defaultdict(int)
    while (i if by_macros else od)<n:
        a,b,cs,tail=cells(w);V=sum(e<<j for j,(_,_,e) in enumerate(cs))
        if use_cycle and not by_macros and not V and od+2<=n:
            d=cycle(w,check)
            if d is not None:w,k,c=d;i+=k;tc+=c;od+=2;stats['cycle']+=1;continue
        if V:
            d=None if by_macros else drain(w)
            if d is not None:w,k,c=d;i+=k;tc+=c;stats['drain']+=1;continue
            v,k,c=carry(w,min(V,n-i) if by_macros else V)
            if k:w=v;i+=k;tc+=c;stats['skip']+=1;continue
        try:w,c,odd,term=single(w)
        except RuntimeError as ex:
            if ex.args[0]!='F1':raise
            print('F1 at exact query step',tc+ex.args[1]);return
        i+=1;tc+=c;od+=odd;stats['single']+=1
    print('od',od,'macro bits',i.bit_length(),'time bits',tc.bit_length(),'stats',dict(stats))
    print('time sha256',hashlib.sha256(tc.to_bytes((tc.bit_length()+7)//8,'big')).hexdigest())
    if by_macros:print('macros',i,'steps',tc)

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('n',nargs='?',type=int,default=5000)
    p.add_argument('--macros',action='store_true');p.add_argument('--cycle',action='store_true')
    p.add_argument('--check',action='store_true');p.add_argument('--test',action='store_true')
    args=p.parse_args()
    if args.test:test()
    else:run(args.n,args.macros,args.cycle,args.check)
