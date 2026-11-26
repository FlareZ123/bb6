"""Exact B-return reduction and counterexample-guided pushdown abstraction.
Experimental: safe output requires independent closure audit."""
from collections import defaultdict, deque
import argparse,json,time
TABLE="1RB1RD1RC0LD0LA0RE1LA1LB0RF---0LA1RA"
T=[TABLE[i:i+3] for i in range(0,len(TABLE),3)]
rules=[("","","00","11"),("","101","0100","0"),("","10011","01010",""),("","1001","010110","11"),("","1001","010111","11"),("00","1","1","10"),("01","","1","110"),("10","","1","010"),("11","","1","110")]
HALT_PREFIX="011"
def symbolic_returns():
    out=[]
    def go(q,h,orig,tape,n):
        if n and q==1:
            a,b=min(orig),max(orig)
            for bit in ([0,1] if h<a else [None]):
                before,after=dict(orig),dict(tape)
                if bit is not None:before[h]=after[h]=bit
                l=min(before)
                lp="".join(str(before[i]) for i in range(-1,l-1,-1))
                rp="".join(str(before[i]) for i in range(b+1))
                lw="".join(str(after[i]) for i in range(l,h))
                rw="".join(str(after[i]) for i in range(h,b+1))
                out.append(("return",(lp,lw,rp,rw),n))
            return
        assert n<=8
        for s in ([tape[h]] if h in tape else [0,1]):
            a,b=dict(orig),dict(tape)
            if h not in b:a[h]=b[h]=s
            tr=T[2*q+s]
            if tr=="---":
                out.append(("halt","".join(str(a[i]) for i in range(max(a)+1)),n))
                continue
            b[h]=int(tr[0])
            go(ord(tr[2])-65,h+(1 if tr[1]=="R" else -1),a,b,n+1)
    go(1,0,{},{},0)
    assert {x[1] for x in out if x[0]=="return"}==set(rules)
    assert [x for x in out if x[0]=="halt"]==[("halt",HALT_PREFIX,2)]
    return out

def pds_worklist(delta,maxentries=1000000,maxtasks=4000000,maxwitness=2000000):
    N=len(delta)
    trans=[];halt=N;nctrl=N+1
    def fresh():
        nonlocal nctrl
        i=nctrl;nctrl+=1;return i
    def rule(p,u,q,v,tag):
        for j,ch in enumerate(u):
            last=j==len(u)-1;dst=q if last else fresh();out=v if last else ""
            a=int(ch);w=tuple(map(int,out));m=tag if last else None
            trans.append((p,a,dst,w,m))
            if a==0:trans.append((p,2,dst,w+(2,),m))
            p=dst
    def push(l,w):
        for b in w:l=delta[l][int(b)]
        return l
    for ri,(lp,lw,rp,rw) in enumerate(rules):
        for base in range(N):
            p=push(base,lp[::-1]);q=push(base,lw)
            rule(p,rp,q,rw,(ri,base,p,q))
    for p in range(N):rule(p,"011",halt,"",("halt",p))
    final=nctrl
    edges=[];eid={};out=defaultdict(list)
    waiting=defaultdict(list);watchseen=set();queue=deque()
    def addedge(p,a,q,ti=-1,proof=()):
        key=(p,a,q)
        if key in eid:return
        i=len(edges);eid[key]=i;edges.append((p,a,q,ti,proof));out[p,a].append(i)
        queue.append((0,i))
    def addwatch(ti,pos,s,path):
        key=(ti,pos,s)
        if key in watchseen:return
        watchseen.add(key);queue.append((1,ti,pos,s,path))
    addedge(halt,0,halt);addedge(halt,1,halt);addedge(halt,2,final)
    for ti,(p,a,q,w,tag) in enumerate(trans):addwatch(ti,0,q,())
    initial=(delta[0][1],2,final);tasks=0;st=time.monotonic()
    while queue and initial not in eid:
        if len(edges)>maxentries or tasks>maxtasks:return {"status":"cap","entries":len(edges),"tasks":tasks,"controls":nctrl}
        event=queue.popleft();tasks+=1
        if event[0]==0:
            i=event[1];p,a,q,_,_=edges[i]
            for ti,pos,path in waiting[p,a]:addwatch(ti,pos+1,q,path+(i,))
        else:
            _,ti,pos,s,path=event;p,a,q,w,tag=trans[ti]
            if pos==len(w):addedge(p,a,s,ti,path)
            else:
                waiting[s,w[pos]].append((ti,pos,path))
                for i in out[s,w[pos]]:addwatch(ti,pos+1,edges[i][2],path+(i,))
    if initial not in eid:
        return {"status":"safe","entries":len(edges),"tasks":tasks,"controls":nctrl,"elapsed":time.monotonic()-st,"edges":edges,"final":final,"trans":trans}
    agenda=deque([eid[initial]]);tags=[];steps=0
    while agenda:
        i=agenda.popleft();p,a,q,ti,proof=edges[i]
        if ti<0:break
        tag=trans[ti][4]
        if tag is not None:tags.append(tag)
        agenda.extendleft(reversed(proof));steps+=1
        if steps>maxwitness:return {"status":"witness-cap","entries":len(edges),"tasks":tasks}
    l=initial[0];right="";path=[]
    for tag in tags:
        if tag[0]=="halt":
            assert tag[1]==l and (right+"000").startswith("011");break
        ri,base,p,q=tag;assert p==l
        lp,lw,rp,rw=rules[ri];rz=right+"000000";assert rz.startswith(rp)
        nr=(rw+rz[len(rp):]).rstrip("0")
        path.append(((p,right),ri,base,(q,nr)));l=q;right=nr
    assert tags[-1][0]=="halt"
    return {"status":"bad","entries":len(edges),"tasks":tasks,"controls":nctrl,"elapsed":time.monotonic()-st,"path":path}
def first_spurious(delta,path):
    L="1"
    def push(l,w):
        for b in w:l=delta[l][int(b)]
        return l
    for old,ri,base,new in path:
        lp,lw,rp,rw=rules[ri]
        a=push(0,L[::-1]);assert a==old[0]
        z=L+"0"*max(6,len(lp))
        if not z.startswith(lp):return a,lp,base
        L0=z[len(lp):].rstrip("0")
        if push(0,L0[::-1])!=base:return a,lp,base
        L=(lw[::-1]+L0).rstrip("0")
        assert push(0,L[::-1])==new[0]
    return None
def minimize_labeled(delta,labels):
    lab={};classes=[]
    for x in labels:
        if x not in lab:lab[x]=len(lab)
        classes.append(lab[x])
    while True:
        tab={};new=[]
        for i,(a,b) in enumerate(delta):
            key=(classes[i],classes[a],classes[b])
            if key not in tab:tab[key]=len(tab)
            new.append(tab[key])
        if len(tab)==len(set(classes)):
            classes=new;break
        classes=new
    rep={}
    for i,c in enumerate(classes):rep.setdefault(c,i)
    root=classes[0];ids={root:0};states=[root];out=[]
    for c in states:
        a,b=delta[rep[c]];row=[]
        for j in (classes[a],classes[b]):
            if j not in ids:ids[j]=len(ids);states.append(j)
            row.append(ids[j])
        out.append(row)
    return out
def refine_inverse(delta,collision,lp,chosen):
    k=len(lp);assert k>0
    mask=(1<<k)-1
    start=(0,0);states=[start];ids={start:0};d=[];labels=[]
    for base,bits in states:
        current=base
        for j in range(k-1,-1,-1):current=delta[current][(bits>>j)&1]
        pred=(base==chosen and bits==int(lp[::-1],2))
        labels.append((current,pred if current==collision else False))
        row=[]
        for b in [0,1]:
            z=(delta[base][(bits>>(k-1))&1],((bits<<1)|b)&mask)
            if z not in ids:ids[z]=len(ids);states.append(z)
            row.append(ids[z])
        d.append(row)
    return minimize_labeled(d,labels)
def run_inverse_cegar(rounds=100,seconds=15,delta=None):
    if delta is None:delta=[[0,0]]
    st=time.monotonic();hist=[]
    for j in range(rounds):
        x=pds_worklist(delta,maxentries=1000000,maxtasks=5000000)
        if x["status"]!="bad":return delta,hist,x
        split=first_spurious(delta,x["path"])
        if split is None:return delta,hist,{"status":"concrete-halt"}
        new=refine_inverse(delta,*split)
        assert len(new)>len(delta),(len(delta),len(new),split)
        hist.append((j,len(delta),len(new),len(x["path"]),x["entries"],split))
        delta=new
        if time.monotonic()-st>seconds:return delta,hist,{"status":"time","elapsed":time.monotonic()-st}
    return delta,hist,{"status":"rounds"}
if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--rounds",type=int,default=40)
    p.add_argument("--seconds",type=float,default=15)
    p.add_argument("--resume")
    p.add_argument("--output",default="held-cegar.json")
    a=p.parse_args()
    print(json.dumps(symbolic_returns()))
    start=None
    if a.resume:
        with open(a.resume) as f:start=json.load(f)["delta"]
    delta,history,result=run_inverse_cegar(a.rounds,a.seconds,start)
    with open(a.output,"w") as f:json.dump({"delta":delta,"history":history,"result":result},f)
    print(json.dumps({"states":len(delta),"rounds":len(history),"result":{k:v for k,v in result.items() if k not in ("edges","trans","path")}}))
