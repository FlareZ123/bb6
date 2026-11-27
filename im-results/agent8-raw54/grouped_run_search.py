"""Counted groups of completed run lengths: a deterministic stack abstraction.
The generated finite graph is independently checked by MaskBiDFA, not trusted.
Params per side: retained groups, run-length threshold/period, group width,
group-count threshold/period. Pending runs are kept until a group completes.
"""
from collections import defaultdict, deque

class GroupDFA:
    def __init__(self,k,t,p,g,tc,pc):
        self.k,self.t,self.p,self.g,self.tc,self.pc=k,t,p,g,tc,pc
        self.words=[()]
        self.ids={():0}
        self.delta=[[-1,-1]]
    @staticmethod
    def inc(n,t,p):
        return t if n+1>=t+p else n+1
    def push(self,s,b):
        if self.delta[s][b]>=0:return self.delta[s][b]
        key=self.words[s]
        if not key:new=(1,1,(),()) if b else ()
        else:
            bit,n,pending,groups=key
            if b==bit:new=(bit,self.inc(n,self.t,self.p),pending,groups)
            else:
                pending=(n,)+pending
                if len(pending)==self.g:
                    if groups and groups[0][0]==pending:
                        groups=((pending,self.inc(groups[0][1],self.tc,self.pc)),)+groups[1:]
                    else:groups=(((pending,1),)+groups)[:self.k]
                    pending=()
                new=(b,1,pending,groups)
        if new not in self.ids:
            self.ids[new]=len(self.words)
            self.words.append(new)
            self.delta.append([-1,-1])
        dest=self.ids[new];self.delta[s][b]=dest
        return dest
    def total(self):
        return [max(0,x) for row in self.delta for x in row]

def group_search(table,params,cap=300000):
    D=[GroupDFA(*params[:6]),GroupDFA(*params[6:])]
    T=table.replace("_","")
    T=[T[3*i:3*i+3] for i in range(12)]
    E=[defaultdict(set),defaultdict(set)]
    wait=[defaultdict(list),defaultdict(list)]
    seen={(0,0,0)};todo=deque(seen)
    for e in E:e[0].add((0,0))
    def add(s,l,r):
        x=(s,l,r)
        if x not in seen:seen.add(x);todo.append(x)
    def pop(st,b,prev):
        s,l,r=st;w,d,q=T[s];w=int(w);q=ord(q)-65
        if d=="R":add(2*q+b,D[0].push(l,w),prev)
        else:add(2*q+b,prev,D[1].push(r,w))
    while todo:
        if len(seen)>cap:return None,len(seen),"cap"
        st=todo.popleft();s,l,r=st;w,d,q=T[s]
        if w=="-":return None,len(seen),"hole"
        w=int(w);d=int(d=="R")
        src=l if d else r;dst=D[1-d].push(src,w);e=(w,src)
        if e not in E[1-d][dst]:
            E[1-d][dst].add(e)
            for v in wait[1-d][dst]:pop(v,*e)
        x=r if d else l;wait[d][x].append(st)
        for b,y in E[d][x]:pop(st,b,y)
    return [d.total() for d in D],len(seen),(E,seen)
