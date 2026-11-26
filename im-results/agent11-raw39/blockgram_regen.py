"""Lazy block-aware deterministic stack quotients."""
class BlockDFA:
    def __init__(self, params):
        self.p,self.k,self.c,self.m=params
        self.words=[((),0,0)]
        self.ids={self.words[0]:0}; self.delta=[[None,None]]
    def update(self,v,b):
        runs,partial,phase=v
        if not runs and not phase and not b:return v
        partial=2*partial+b;phase+=1
        if phase==self.p:
            runs=append(runs,partial,self.k,self.c,self.m)
            partial=phase=0
        return runs,partial,phase
    def push(self,idx,b):
        j=self.delta[idx][b]
        if j is not None:return j
        w=self.update(self.words[idx],b)
        if w not in self.ids:
            self.ids[w]=len(self.words);self.words.append(w);self.delta.append([None,None])
        j=self.ids[w];self.delta[idx][b]=j;return j
    def finish(self):return [0 if j is None else j for v in self.delta for j in v]

def append(runs,token,k,c,m):
    if runs and runs[0][0]==token:
        n=runs[0][1]+1
        if n==c+m:n=c
        return ((token,n),)+runs[1:]
    return (((token,1),)+runs)[:k]

class RunBlockDFA(BlockDFA):
    def __init__(self,params):
        self.p,self.k,self.c,self.m,self.h=params
        self.words=[((),0,0,0,0)]
        self.ids={self.words[0]:0};self.delta=[[None,None]]
    def update(self,v,b):
        runs,partial,phase,length,bit=v
        if not length:
            if not b:return v
            return runs,partial,phase,1,1
        if bit==b:return runs,partial,phase,min(self.h,length+1),bit
        partial=8*partial+length;phase+=1
        if phase==self.p:
            runs=append(runs,partial,self.k,self.c,self.m)
            partial=phase=0
        return runs,partial,phase,1,b
