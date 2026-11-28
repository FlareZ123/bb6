"""Exact F197 blank-root nonhalting certificate generator/checker (Agent 2).
All finite rules are checked on guarded prefixes. No cutoffs imply nonhalting.
Run without -O; Python integers are exact. Outputs optional Lean trace data JSON.
"""
import json, sys, time
from functools import lru_cache
from collections import deque
from pathlib import Path
if not __debug__: raise RuntimeError('Assertions are required')
D={'A':'10','T':'1100','J':'100','U':'11100','C':'110'}
P='AAT'; M='JTAATAAA'; K='TATAAT'; R='AATAAAT'; LB='AATAAATAUJTT'
H='111100011111000110'; U='1111000'; S='11111000'; X='10'; J='100'; XC='10110'
G='ATTJAUJ'; G2='ACAAATAUJTT'; V='1110'; V2='111111000110'
HEAD='JTAATAAATATAATAATAATAATAATTATAATAATAATTAATTAAATAUJTT'
END_N=2930368004349374329
E=['AAATATATATAAAT','AAATATAATAATATAAAT']
W=['AAATAATATAAATTAAAT','AAATATATAAATTAAAT']
RB=['1111000111100011100011100010111100011111000111110001111100011','11110001111000111100011111000111100010111100011']
OUT=[['AATAATJTAATAATAATAAATTAAATAUJTT','AATJTAATAATAATATAAATUJTTAATAAATAUJTT'],['TAATATJTJAATATAATAAATAUJTT','TAATAAATAATTAAATUJTTAATAAATAUJTT']]
BULK=[(76,9,38,4),(28,3,14,1)]
enc=lambda w: ''.join(D[c] for c in w)

def word(s):
    assert s.endswith('1'); z=s[:-1]; w=''
    while z:
        for c,b in D.items():
            # The next 1 (or end) identifies the boundary of a run codeword.
            if z.startswith(b) and (len(z)==len(b) or z[len(b)]=='1'):
                w+=c;z=z[len(b):];break
        else: raise ValueError(('unaligned',z[:40]))
    assert enc(w)+'1'==s;return w

def strip(w,p=P):
    n=0
    while w.startswith(p,n*len(p)):n+=1
    return n,w[n*len(p):]

TM=(((1,1,1),(0,1,4)),((1,1,2),(0,-1,4)),((0,1,3),(0,0,-1)),((0,1,4),(0,1,0)),((1,-1,5),(0,-1,1)),((1,-1,0),(1,-1,5)))
Q='ABCDEF'

def literal(q,l,r):
    assert r and r[0] in '01';b,d,n=TM[Q.index(q)][int(r[0])];assert n>=0
    b=str(b)
    if d==1:return Q[n],b+l,r[1:]
    assert l;return Q[n],l[1:],l[0]+b+r[1:]

def physical(p,l,r):
    if p=='D':return p,l,r
    assert l;return p,l[1:],l[0]+r

RULES=[('D','0','01',4,'D','010',''),('D','0','00',6,'B','','001'),('D','0','111',5,'D','0100',''),('D','0','110',9,'D','01','01'),('D','0','101',6,'D','010','0'),('D','0','1000',4,'D','01100',''),('B','0','0',2,'D','01',''),('B','11','0',2,'B','','000'),('B','10','0',2,'F','','100'),('F','1','',1,'F','','1'),('F','0','',1,'A','','1'),('A','0','1',3,'B','','00'),('A','1','1',4,'D','01','')]

def check_macro_table():
    for p,L,R,c,q,L2,R2 in RULES:
        for a in ('0','1'):
            for b in ('0','1'):
                state=physical(p,L+a,R+b)
                for _ in range(c):state=literal(*state)
                assert state==physical(q,L2+a,R2+b),(p,L,R,a,b,state)

def nextstep(p,l,r):
    for q,L,R,c,q2,L2,R2 in RULES:
        if q==p and l.startswith(L) and r.startswith(R):return c,q2,L2+l[len(L):],R2+r[len(R):]
    raise ValueError(('unknown/fatal',p,l[:80],r[:80]))

def finite(p,l,r,t):
    c=j=0
    try:
        while c<t:
            k,p,l,r=nextstep(p,l,r);c+=k;j+=1
        if c==t:return p,l,r,j
    except (ValueError,AssertionError):pass
    return None

def reset_path(l,r,maxsteps=100000):
    p='B';r='00'+r+'0'*1000;t=0
    for j in range(maxsteps):
        if j and p=='B' and r.rstrip('0')=='001':return t,j,l,1000-(len(r)-3)
        c,p,l,r=nextstep(p,l,r);t+=c
    raise ValueError('finite reset search cutoff')

def guard_check(L,R,L2,R2,c,j):
    assert finite('B',enc(L)+'1','00'+R+'1',c)==('B',enc(L2)+'1','00'+R2+'1',j),(L,R,L2,R2,c,j)

def blank_check(L,R,L2,c,j,pad):
    assert finite('B',enc(L)+'1','00'+R+'0'*pad,c)==('B',enc(L2)+'1','001',j),(L,L2,c,j,pad)

def check_families():
    check_macro_table()
    guard_check(P,'','',U+'1',36,13)
    guard_check('J',X+S,'J'+P,X,32,8)
    blank_check('J',X+'11',P,27,7,2)
    guard_check(M,U+S*2,'J'+M+K,X,321,95)
    blank_check(P*2+M,'1',M+K,388,120,2)
    for p,prefix,pad,c,j in [(0,M+K,21,1863,575),(1,P+M,17,887,281)]:
        assert finite('B',enc(prefix)+'1','001'+'0'*pad,c)==('B','1','00'+RB[p],j)
    guard_check(K,'','',H,82,29)
    guard_check('J',XC+H,'J'+R,XC,68,17)
    blank_check('J',XC+RB[0],P*4+E[0],375,97,2)
    blank_check('J',XC+RB[1],P+E[1],283,73,2)
    guard_check('TATJ',H,G+'T',V,112,30)
    guard_check(G,V+H,G2,V2,176,54)
    guard_check(G2,V2+H,G+LB,V,96,23)
    for p in range(2):
        for b,g,v,c,j,pad in [(0,G,V,[806,407][p],[235,115][p],[2,5][p]),(1,G2,V2,[698,599][p],[203,172][p],[2,5][p])]:
            blank_check(g,v+RB[p],OUT[p][b],c,j,pad)

def common_suffix(a,b):
    k=0
    while k<min(len(a),len(b)) and a[-k-1]==b[-k-1]:k+=1
    return k

def prefix_pair(a,b,nonempty=False):
    for k in range(common_suffix(a,b),0,-1):
        if a[-k]!='1':continue
        aa,bb=a[:-k],b[:-k]
        if nonempty and (not aa or not bb):continue
        try:x,y,z=word(aa+'1'),word(bb+'1'),word(a[-k:])
        except (ValueError,AssertionError):continue
        yield x,y,z

@lru_cache(None)
def uniform_cert(w):
    a=enc(w)+'1';l=a;r='001';p='B';t=0
    for j in range(100000):
        if j and p=='B' and l.startswith('1001') and r=='00101101':
            for src,dst,suffix in prefix_pair(a,l[3:]):
                f=finite('B',enc(src)+'1','001',t)
                if f and f[:3]==('B',J+enc(dst)+'1',r):return {'type':'terminal','src':src,'dst':dst,'steps':f[3],'cost':t},dst+suffix
            return None
        try:k,p,l,r=nextstep(p,l,r);t+=k
        except (ValueError,AssertionError):return None
    return None

@lru_cache(None)
def core_cert(w,k):
    a=enc(w)+'1';l=a;r='00'+U+S*k+'1';p='B';t=0
    for j in range(100000):
        if j and p=='B' and l.startswith('1001') and r.startswith('0010') and r.endswith('1'):
            z=r[4:-1];q=len(z)//len(S)
            if z==S*q:
                for src,dst,suffix in prefix_pair(a,l[3:],True):
                    f=finite('B',enc(src)+'1','00'+U+S*k+'1',t)
                    if f and f[:3]==('B',J+enc(dst)+'1','0010'+S*q+'1'):
                        d,dy=strip(dst);return {'type':'core','src':src,'dst':dy,'add':d,'k':k,'j':q,'steps':f[3],'cost':t},dst+suffix
                return None
        try:c,p,l,r=nextstep(p,l,r);t+=c
        except (ValueError,AssertionError):return None
    return None

@lru_cache(None)
def direct_cert(n,w):
    a=enc(P*n+w)+'1';t,j,b,pad=reset_path(a,'1');assert pad>=0
    n2,out=strip(word(b))
    for src,dst,suffix in prefix_pair(a,b):
        if not src.startswith(P*n) or not dst.startswith(P*n2):continue
        src=src[3*n:];dst=dst[3*n2:]
        f=finite('B',enc(P*n+src)+'1','001'+'0'*pad,t)
        if f and f[:3]==('B',enc(P*n2+dst)+'1','001'):
            return {'type':'direct','src':src,'dst':dst,'n':n,'n2':n2,'pad':pad,'steps':f[3],'cost':t},n2,out
    raise RuntimeError(('direct prefix extraction',n,w[:100]))

core_rules={};direct_rules={};terminal_rules={}
def clear():
    core_rules.clear();direct_rules.clear();terminal_rules.clear()
    for f in (core_cert,direct_cert,uniform_cert):f.cache_clear()

def validate_rule(r):
    assert r['cost']>0
    if r['type']=='core':
        assert r['src'] and (r['dst'] or r['add'])
        guard_check(r['src'],U+S*r['k'],'J'+P*r['add']+r['dst'],X+S*r['j'],r['cost'],r['steps'])
    elif r['type']=='direct':
        blank_check(P*r['n']+r['src'],'1',P*r['n2']+r['dst'],r['cost'],r['steps'],r['pad'])
    elif r['type']=='terminal':
        guard_check(r['src'],'','J'+r['dst'],XC,r['cost'],r['steps'])
    else:raise ValueError('unknown rule')

def local(n,w):
    for (src,k),r in core_rules.items():
        if n>=k+1 and w.startswith(src):return n-k+r['j']+r['add'],r['dst']+w[len(src):],r
    for k in [0,1,2,4,8,16,32,64,128]:
        if n<k+1:break
        a=core_cert(w,k)
        if a:
            r,out=a;src=r['src'];validate_rule(r);core_rules[src,k]=r
            y=r['dst']+w[len(src):];assert not y.startswith(P)
            return n-k+r['j']+r['add'],y,r
    if n>10000:raise RuntimeError(('no core',n,w[:100]))
    for (nn,src),r in direct_rules.items():
        if n==nn and w.startswith(src):return r['n2'],r['dst']+w[len(src):],r
    r,n2,out=direct_cert(n,w);validate_rule(r);direct_rules[n,r['src']]=r
    return n2,out,r

def verify_ops(n,w,ops):
    for r in ops:
        validate_rule(r);assert w.startswith(r['src'])
        if r['type']=='core':assert n>=r['k']+1;n=n-r['k']+r['j']+r['add']
        elif r['type']=='direct':assert n==r['n'];n=r['n2']
        else:raise ValueError('not a local op')
        w=r['dst']+w[len(r['src']):]
    return n,w

def fixed_schedule(n,w,count):
    n0,w0=n,w;rs=[]
    for _ in range(count):n,w,r=local(n,w);rs.append(r)
    assert all(r['type']=='core' for r in rs)
    assert verify_ops(n0,w0,rs)==(n,w)
    return n,w,rs

def check_bulk():
    data=[]
    for p,(a,u,d,n) in enumerate(BULK):
        z,w,ent=fixed_schedule(n,E[p]+R*u,a);assert (z,w)==(n+d,W[p])
        z,w,cyc=fixed_schedule(4,W[p]+R*4,36);assert (z,w)==(22,W[p])
        data.append((ent,cyc))
    return data

def epoch(n,w):
    assert w.startswith(M+'TA');a=uniform_cert(w[len(M):])
    if a is None:return None
    r,y=a;validate_rule(r);terminal_rules[r['src']]=r
    q,p=divmod(n,2);m=q-(p==0);_,entry,gain,base=BULK[p]
    if m<entry:return None
    q2,r0=divmod(m-entry,4)
    return base+gain+18*q2,W[p]+R*r0+y,r

def next_epoch(n,w,trace):
    for _ in range(10000):
        if n>=40 and w.startswith(M+'TA'):return n,w
        n2,w2,r=local(n,w);trace.append({'n':str(n),'w':w,'rule':r,'n2':str(n2),'w2':w2});n,w=n2,w2
    raise RuntimeError('next epoch cutoff')

def self_trace(k=80):
    clear();n,w=72,HEAD+LB*k;tr=[];rows=[]
    for i in range(48):
        rows.append((str(n),w));a=epoch(n,w)
        if a is None:assert i==47 and n==END_N and w.startswith(M+'TATJ');break
        n2,w2,r=a;tr.append({'n':str(n),'w':w,'rule':r,'n2':str(n2),'w2':w2});n,w=next_epoch(n2,w2,tr)
    assert n==END_N and w.startswith(M+'TATJ');Y=w[len(M+'TATJ'):]
    m=n//2;cycles=(m-2)//2;assert n%2==1 and m%2==0
    extra=k+10;assert cycles>=extra
    n0,w0=strip(OUT[1][1]+LB*extra);post=[];n1,w1=next_epoch(n0,w0,post)
    assert n1==72 and w1.startswith(HEAD+LB*k);rem=w1[len(HEAD+LB*k):]
    out={'k':k,'head':HEAD,'start':HEAD+LB*k,'pre_marker':{'n':str(n),'w':w,'Y':Y,'cycles':str(cycles)},'trace':tr,'post':post,'post_extra':extra,'post_suffix':rem,'post_end':w1,'rows':rows}
    print('SELF EMBEDDING',len(tr),len(post),'cycles',cycles,'inserted finite prefix',rem,'remaining blocks',cycles-extra,flush=True)
    return out

class Rope:
    def __init__(self):self.q=deque()
    def prepend(self,w,n=1):
        assert n>=0
        if w and n:self.q.appendleft((w,n))
    def pull(self,k):
        out=''
        while k>0 and self.q:
            w,n=self.q.popleft();m=min(n,k//len(w))
            if m:out+=w*m;k-=m*len(w);n-=m
            if n and k:out+=w[:k];self.prepend(w,n-1);self.prepend(w[k:]);k=0
            elif n:self.prepend(w,n)
        return out
    def length(self):return sum(len(w)*n for w,n in self.q)
    def data(self):return [(w,str(n)) for w,n in self.q]

GEN=[dict(src='TATAATAATAATATATATAATATTATTJTATAATAATTAA',dst='JJTAATAAATTTJTJTAAAATATAAATAATAATAAAT',g='J',block='AAATAAT',v=XC,h=0,a=1,ec=901,ej=286,cc=68,cj=17,pure=True),dict(src='TATUJTTJAA',dst='ATTJAUJAAATATAAT',g=G,block=LB,v=V,h=1,a=2,ec=414,ej=121,cc=272,cj=77,pure=False)]

def generic(n,w,rope):
    assert n%2==1 and w.startswith(M);Xw=w[len(M):]
    a=next(a for a in GEN if Xw.startswith(a['src']));m=n//2
    src,dst,g,block,v=(a[k] for k in ('src','dst','g','block','v'))
    guard_check(src,H*a['h'],dst,v,a['ec'],a['ej'])
    guard_check(g,v+H*a['a'],g+block,v,a['cc'],a['cj'])
    z=dst+Xw[len(src):];assert z.startswith(g);Y=z[len(g):]
    q,r=divmod(m-a['h'],a['a']);assert q>=0
    t,j,l,pad=reset_path(enc(g)+'1',v+H*r+RB[1]);out=word(l)
    blank_check(g,v+H*r+RB[1],out,t,j,pad);N,z=strip(out)
    info={'kind':'generic','family':a,'exit':{'cost':t,'steps':j,'pad':pad,'right':v+H*r+RB[1],'out':out},'q':str(q),'r':r}
    if a['pure']:
        n0,z0=N,z;N,Z,ent=fixed_schedule(N,z+block*2,28);assert N==n0+14 and Z=='AAATATATAAATT'
        n2,Z2,cyc=fixed_schedule(N,Z+block*4,36);assert n2==N+18 and Z2==Z
        k,rem=divmod(q-2,4);assert k>=0
        info['pure']={'ent':ent,'cyc':cyc,'k':str(k),'rem':rem,'base':n0,'prefix':z0,'W':Z}
        return N+18*k,Z+block*rem+Y,info
    rope.prepend(Y);rope.prepend(block,q);return N,z,info

def seed():
    tape=bytearray(12_000_000);h=6_000_000;lo=hi=h;q=0;t=5810803
    for _ in range(t):
        b,d,q2=TM[q][tape[h]];assert q2>=0;tape[h]=b;h+=d;q=q2
        if h<lo:lo=h
        if h>hi:hi=h
    l=''.join(map(str,tape[lo:h+1][::-1])).rstrip('0');r=''.join(map(str,tape[h+1:hi+1])).rstrip('0')
    assert q==1 and r=='001' and len(l)==3311
    n,w=strip(word(l));assert n==114 and w.startswith(M+'TA')
    return n,w,t

def root_trace():
    clear();n,w,cost=seed();rope=Rope();trace=[];rows=[];start=(n,w,cost)
    def refill(w):return w+rope.pull(1300-len(w)) if len(w)<1300 and rope.q else w
    for i in range(250):
        w=refill(w);rows.append({'i':i,'n':str(n),'w':w,'rope':rope.data()})
        if n==72 and w.startswith(HEAD+LB*80):break
        assert n>=40 and w.startswith(M+'TA');n0,w0=n,w;rope0=rope.data();a=epoch(n,w)
        if a is not None:n,w,r=a;info={'kind':'ordinary','rule':r}
        elif w.startswith(M+'TATJ'):
            m=n//2-(n%2==0);k,b=divmod(m-1,2);assert m>=1
            rope.prepend('T'+w[len(M+'TATJ'):]);rope.prepend(LB,k);n,w=strip(OUT[n%2][b]);info={'kind':'marker','cycles':str(k),'parity':n0%2,'half':b}
        elif n<10000:n,w,r=local(n,w);info={'kind':'local','rule':r}
        else:n,w,info=generic(n,w,rope)
        trace.append({'n':str(n0),'w':w0,'rope':rope0,'op':info,'n2':str(n),'w2':w,'rope2':rope.data()})
        for _ in range(10000):
            oldw=w;w=refill(w)
            if w!=oldw:trace.append({'kind':'refill','n':str(n),'before':oldw,'after':w,'rope2':rope.data()})
            if n>=40 and w.startswith(M+'TA'):break
            n2,w2,r=local(n,w);trace.append({'n':str(n),'w':w,'op':{'kind':'local','rule':r},'n2':str(n2),'w2':w2});n,w=n2,w2
        else:raise RuntimeError('next epoch cutoff')
    else:raise RuntimeError('root not reached')
    assert i==181 and n==72 and w.startswith(HEAD+LB*80)
    print('BLANK ROOT REACH',i,len(trace),'deep letters',rope.length(),flush=True)
    return {'seed':{'n':str(start[0]),'w':start[1],'cost':start[2]},'trace':trace,'epochs':rows,'end':{'n':str(n),'w':w,'rope':rope.data()}}

if __name__=='__main__':
    t=time.time();check_families();clear();bulk=check_bulk();a=self_trace();b=root_trace()
    if len(sys.argv)>1:
        p=Path(sys.argv[1]);p.mkdir(parents=True,exist_ok=True)
        for name,data in [('self_trace',a),('root_trace',b),('bulk_data',bulk)]:
            (p/(name+'.json')).write_text(json.dumps(data,separators=(',',':')))
    print('CERTIFICATE PASSED: positive suffix-parametric loop and literal blank-root reach; elapsed',time.time()-t)
