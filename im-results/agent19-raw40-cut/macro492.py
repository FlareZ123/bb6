from dataclasses import dataclass
@dataclass
class Cfg:
    h:int
    # closed intervals of ones, ordered disjoint/nonadjacent
    runs:list
    cost:int=0
    def b(self,x): return any(a<=x<=b for a,b in self.runs)
    def set(self,l,r,val):
        if l>r:return
        new=[]
        if val:
            for a,b in self.runs:
                if b<l-1 or a>r+1:new.append((a,b))
                else:l=min(a,l);r=max(b,r)
            new.append((l,r));new.sort()
        else:
            for a,b in self.runs:
                if b<l or a>r:new.append((a,b))
                else:
                    if a<l:new.append((a,l-1))
                    if b>r:new.append((r+1,b))
        self.runs=new
    def leftone(self,x):return max((min(x,b) for a,b in self.runs if a<=x),default=None)
    def rlen(self,x):return next((b-x+1 for a,b in self.runs if a<=x<=b),0)
    def step(self):
        x=self.h
        if self.b(x):
            if self.b(x+1):
                self.set(x+1,x+1,0);self.h=x-1;self.cost+=3;return 'A11'
            self.set(x,x,0);y=x
            # D at x+2
            r=0
        else:
            r=self.rlen(x+1);y=x+r+1
            self.set(x,x,1);self.set(x+1,y-1,0)
            if r%2==0:
                self.set(y,y,1)
                if self.b(y+1):raise RuntimeError('halt')
            elif self.b(y+1):
                self.set(y,y,1);self.set(y+1,y+1,0);self.h=y-1;self.cost+=r+4;return 'A0odd1'
        z=self.leftone(y+2)
        if z is None:raise RuntimeError('infinite drift')
        self.set(z+1,y+2,1);self.h=z-1;self.cost+=(3 if y==x else r+4)+y+2-z
        return 'D'
    def accel(self):
        x=self.h; r=self.rlen(x+1)
        # A0, odd run, followed by at least two zeros (D may see next bit at y+2! need THREE zeros)
        # C0 follows F0; D at y+2, must blank too, and nearest 1 is x. preserve arbitrary tail.
        if not self.b(x) and r%2 and not self.b(x+r+2) and not self.b(x+r+3):
            # only safe to accelerate if enough right blanks to contain all growth
            z=self.leftone(x-1);a=next((a for a,b in self.runs if a>x+r),None)
            k=x-z if z is not None else 10**100
            if a is not None:k=min(k,(a-x-r-1)//3)
            if k==10**100:raise RuntimeError('infinite rightmost growth')
            if k>0:
                self.set(x-k+1,x+r+3*k,1);self.h=x-k;self.cost+=k*(2*r+7)+4*k*(k-1);return 'oddD',k
        # A0, single 1, gap one, then run. repeatedly shift into left and consume next run
        if not self.b(x) and r==1 and self.b(x+3):
            k=self.rlen(x+3)
            self.set(x,x+k-1,1);self.set(x+k,x+k,0);self.set(x+k+1,x+k+1,1);self.set(x+k+2,x+k+2,0)
            self.h=x+k;self.cost+=5*k;return 'transfer',k
        # A1 followed by one: walk left over same run. remove bits x+1 down to new head+2
        if self.b(x) and self.b(x+1):
            a=next(a for a,b in self.runs if a<=x<=b);k=x-a+1
            self.set(a+1,x+1,0);self.h=x-k;self.cost+=3*k;return 'leftA11',k
        return self.step(),1
    def norm(self):return tuple((a-self.h,b-self.h) for a,b in self.runs)
    def __repr__(self):return f'{self.cost}: h={self.h} {self.norm()}'
if __name__=='__main__':
    c=Cfg(0,[])
    for i in range(160):
        print(i,c)
        print('  ',c.accel())
