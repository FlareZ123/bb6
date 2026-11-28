"""Arithmetic accelerator for 1RB1LD1RC0RB1LA1RE1LC0LA0RF1RA---0LC.
The exact primitive count is a computational result, not a compiled root certificate.
"""
from dataclasses import dataclass
from hashlib import sha256
import argparse
D0='0101'; D1='0110'; TABLE='1RB1LD1RC0RB1LA1RE1LC0LA0RF1RA---0LC'
@dataclass(frozen=True)
class Level:
    w:int
    x:int
    delim:int
    tail:object
    def cap(self):
        if isinstance(self.tail,Level):
            h=self.tail.cap()>>self.delim
            return ((h+1)<<self.w)-1-self.x
        return ((2 if self.tail=='1' else 1)<<self.w)-1-self.x if self.w else 0
    def advance(self,n):
        assert 0<=n<=self.cap()
        q,r=divmod(self.x+n,1<<self.w)
        c=8*sum(((self.x+n)>>i)-(self.x>>i) for i in range(self.w))
        t=self.tail
        if isinstance(t,Level):
            t,high=t.advance(q<<self.delim)
            c+=high+q*6*((1<<self.delim)-1)
        elif q:
            assert q==1 and t=='1';t='011';c+=10
        return Level(self.w,r,self.delim,t),c
    def encode(self):
        s=''.join(D1 if (self.x>>i)&1 else D0 for i in range(self.w))
        return s+('1'*(3*self.delim)+self.tail.encode() if isinstance(self.tail,Level) else self.tail)
def parse(R):
    w=0;x=0
    while R[4*w:4*w+4] in (D0,D1):
        if R[4*w:4*w+4]==D1:x|=1<<w
        w+=1
    s=R[4*w:]
    r=len(s)-len(s.lstrip('1'))
    if w>0 and r>0 and r%3==0 and s[r:r+4] in (D0,D1):
        return Level(w,x,r//3,parse(s[r:]))
    return Level(w,x,0,s)
def primitive(q,L,R,table=TABLE):
    a=int((L or '0')[0]); instr=table[3*(2*q+a):3*(2*q+a+1)]
    if instr=='---':return None
    w,d,s=instr
    if d=='R':L,R=(R or '0')[0]+w+L[1:],R[1:]
    else:L,R=L[1:],w+R
    return ord(s)-65,L.rstrip('0'),R.rstrip('0')
def macro(L,R):
    if L.startswith('1'):
        l=(L+'00')[:3]
        if l.startswith('11'): return L[2:],'01'+R,2,'pair'
        if l=='100': return L[3:],'111'+R,3,'triple'
        return '111'+L[3:],R,4,'flip'
    k=len(R)-len(R.lstrip('1'));s=R[k:];v=(s+'0000')[:4]
    if v.startswith('00'):return '1'+'0'*k+'1'+L[1:],'1'+s[2:],k+3,'00'
    if v.startswith('011'):return v[3]+'111'+'0'*k+'1'+L[1:],s[4:],k+4,'011'
    if v=='0101':return '11'+'0'*k+'1'+L[1:],'10'+s[4:],k+6,'0101'
    assert v=='0100'
    q=0
    for _ in range(k+4):q,L,R=primitive(q,L,R)
    assert q==5 and not L.startswith('1')
    return L,R,k+4,'F0'
def run(limit=1000000,check_until=0,trace=None):
    L=R=''; raw=0; hashes=sha256(); counts={}
    for i in range(limit):
        prevL,prevR=L,R
        if not L.startswith('1'):
            k=len(R)-len(R.lstrip('1'));word=parse(R[k:]);cap=word.cap(); n=0;kind=''
            if k%3==0 and cap>=1<<(k//3):
                p=k//3;n=1<<p
                if not L:
                    R='1'*(k+3);kind='blank';over=6*n-3
                else:
                    L='1'+L[1:];R='1'*k;kind='fill';over=6*n-6
            elif k==0 and cap>0:
                z=len(L)-len(L.lstrip('0')) if L else 3*(cap+1).bit_length();a=min(z//3,(cap+1).bit_length()-1)
                if a:
                    L=L[3*a:];R='1'*(3*a);n=(1<<a)-1;kind='drain';over=6*(1<<a)-3*a-6
            if not n and cap>0:
                L='0'*k+'1'+L[1:];R='';n=1;kind='good';over=k
            if n:
                nxt,c=word.advance(n);R+=nxt.encode();cost=c+over
            else:L,R,cost,kind=macro(L,R)
        else:L,R,cost,kind=macro(L,R)
        L=L.rstrip('0');R=R.rstrip('0')
        if raw+cost<=check_until:
            z=(0,prevL,prevR)
            for _ in range(cost):
                z=primitive(*z)
                assert z is not None,(i,kind,cost)
            assert z==(5 if kind=='F0' else 0,L,R),(i,kind,cost,z,(L,R))
        raw+=cost;counts[kind]=counts.get(kind,0)+1
        row=f'{i}\t{kind}\t{cost}\t{raw}\t{L}\t{R}\n';hashes.update(row.encode())
        if trace is not None:trace.write(row)
        if kind=='F0':
            print('F0 assigned prefix',raw,'macro blocks',i+1,'trace sha256',hashes.hexdigest(),'counts',counts)
            print('F0 L',L,'R',R)
            return raw,L,R
    raise RuntimeError('limit')
if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--trace',default='hierarchy-trace.tsv')
    ap.add_argument('--check-until',type=int,default=3000000)
    args=ap.parse_args()
    with open(args.trace,'w') as f:run(check_until=args.check_until,trace=f)
