from dataclasses import dataclass

@dataclass(frozen=True)
class State:
    A: int = 2
    D: int = 1
    d: int = 0
    B: int = 1
    C: int = 6

    def child(self, lower):
        d = self.d + lower
        D = 3*self.D
        return State((self.A << lower) + 2*self.D, D, d,
                     self.B + D, self.C + D*(4-d))

    def numerator_mod(self, i, m):
        return (self.A*5*pow(2, i-self.d, m) - self.B*i-self.C)%m

    def literal(self, i):
        n = self.A*5*(1<<(i-self.d))-self.B*i-self.C
        assert n%self.D==0
        return n//self.D

    def children(self, r):
        m = 2*self.D
        for low in (0,1):
            s = self.child(low)
            rem = s.numerator_mod(r,s.D)
            assert rem%self.D==0
            lift = (-rem//self.D)%3
            yield s,r+lift*m

def inv(y):
    if y==5:return 1
    j=(y//5).bit_length()-1
    for i in (j,j-1):
        if i<0:continue
        p=5<<i;l=p-i-3
        if y==2*p:return l+p-2
        r,d=divmod(y-p-3,3)
        if d==0 and 0<=r<=p-4:return l+r

def depth(i, maxdepth=None):
    y=(10<<i)-i-6
    n=0
    while maxdepth is None or n<maxdepth:
        x=inv(y)
        if x is None:return n,y
        assert x<y
        y=x;n+=1
    return n,y

def symscan(i, s=State(), t=0):
    while i>=4*(t+1)+10:
        rem=s.numerator_mod(i,3*s.D)
        assert rem%s.D==0
        ymod=rem//s.D
        if ymod==0:return t
        pmod=2 if (i-s.d)%2==0 else 1
        s=s.child(int(ymod!=pmod)); t+=1
    return None

def verify():
    for t in range(11):
        if t==0: nodes=[(State(),0),(State(),1)]
        else: nodes=[c for s,r in nodes for c in s.children(r)]
        D=3**t;m=2*D
        assert len(nodes)==2**(t+1)==len({r for s,r in nodes})
        for s,r in nodes:
            i=r+((4*t+10-r+m-1)//m)*m
            assert i>=4*t+10
            if i>5000:continue
            n,y=depth(i,t)
            assert n==t and y==s.literal(i),(t,i,n,y,s.literal(i))
        print('depth',t,'classes',len(nodes),'modulus',m)
    for i in range(100,3000):
        d=symscan(i)
        if d is not None: assert depth(i)[0]==d,(i,d,depth(i))
    print('cross-check passed')
if __name__=='__main__':verify()
