"""Search exact one-sided arbitrary-suffix pumps in finite zipper semantics.
All outputs are candidates; a separate original-source proof must certify them.
"""
import base64,heapq,json,lzma,sys,time
from pathlib import Path

class Search:
    def __init__(self,k,side):
        self.k=k;self.side=side;self.mask=(1<<k)-1;self.d={};self.heap=[]
    def probe(self,t,q,L,R,nL,nR):
        if self.side=='L':active,n,other,no=L,nL,R,nR
        else:active,n,other,no=R,nR,L,nL
        while self.heap and -self.heap[0][0]>=n:
            _,i,key=heapq.heappop(self.heap)
            if self.d.get(key,(None,None))[0]==i:del self.d[key]
        if n<self.k or no>4096:return
        key=q,other,no,active&self.mask
        old=self.d.get(key)
        if old and n>=old[1]:
            return {'entry':old[0],'period':t-old[0],'prefix':self.k,'side':self.side,'growth':n-old[1]}
        if not old or n<old[1]:
            self.d[key]=(t,n)
            heapq.heappush(self.heap,(-(n-self.k),t,key))
        if len(self.heap)>3*len(self.d)+10000:
            self.heap=[(-(n-self.k),i,key) for key,(i,n) in self.d.items()]
            heapq.heapify(self.heap)

def search(table,limit,ks=(8,16,32,64,128,256),report=False):
    table=table.replace('_','');assert len(table)==36
    trans=[]
    for i in range(0,36,3):
        a=table[i:i+3]
        trans.append(None if a in ('---','HHH') else (int(a[0]),a[1]=='R',ord(a[2])-65))
    L=R=nL=nR=q=0
    probes=[Search(k,s) for k in ks for s in ['L','R']]
    start=time.perf_counter()
    for t in range(limit+1):
        for p in probes:
            out=p.probe(t,q,L,R,nL,nR)
            if out:return {'table':table,**out}
        if t==limit:break
        a=trans[2*q+(L&1)]
        if a is None:return {'table':table,'missing':t,'slot':2*q+(L&1)}
        w,d,q=a
        if d:
            L=(R&1)|(w<<1)|((L>>1)<<2);R>>=1
            nL=max(0,nL-1)+2;nR=max(0,nR-1)
        else:
            L>>=1;R=(R<<1)|w
            nL=max(0,nL-1);nR+=1
        if report and t%100000==0:
            print('progress',t,nL,nR,[len(p.d) for p in probes],time.perf_counter()-start,file=sys.stderr,flush=True)
    return {'table':table,'limit':limit,'left':nL,'right':nR}

def from_frontier(path,index):
    data=json.loads(lzma.decompress(base64.b64decode(Path(path).read_text())))
    rows=[r for r in data['residual'] if r[0]==index]
    assert len(rows)==1, rows
    row=rows[0]
    print("FROZEN ROW",row,flush=True)
    tables=[s for s in row if isinstance(s,str) and len(s.replace('_',''))==36]
    assert len(tables)==1, row
    return tables[0]

if __name__=='__main__':
    if len(sys.argv)==4:
        table=from_frontier(sys.argv[1],int(sys.argv[2]))
        limit=int(sys.argv[3])
    else:
        table=sys.argv[1];limit=int(sys.argv[2])
    print(json.dumps(search(table,limit,report=True)),flush=True)
