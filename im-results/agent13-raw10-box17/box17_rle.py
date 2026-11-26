import json,itertools,collections
def run(t,params,limit=15000):
    objs=[[(0,())],[(0,())]];ids=[{(0,()):0},{(0,()):0}];E=[{0:{(0,0)}},{0:{(0,0)}}];P=[{},{}];waiting=[collections.defaultdict(list),collections.defaultdict(list)];todo=[(0,0,0)];seen=set(todo)
    def push(d,i,w):
        key=(i,w)
        if key in P[d]:return P[d][key]
        mode,cap,mod,n=params[d];b,rs=objs[d][i];a=w^b if mode else w
        if not rs and a==0:rs2=()
        elif rs and rs[0][0]==a:
            k=rs[0][1];rs2=((a,cap+1 if k==cap+mod else k+1),)+rs[1:]
        else:rs2=(((a,1),)+rs)[:n]
        z=(w if mode else 0,rs2)
        j=ids[d].get(z)
        if j is None:j=len(objs[d]);ids[d][z]=j;objs[d].append(z)
        P[d][key]=j;return j
    def add(s,l,r):
        x=(s,l,r)
        if x in seen:return
        if t[s]<=0 or len(seen)>=limit:raise ValueError
        seen.add(x);todo.append(x)
    def succ(x,e):
        q,l,r=x;v=t[q]-1;w=v//2%2;b,i=e
        if v%2:add(2*(v//4)+b,push(0,l,w),i)
        else:add(2*(v//4)+b,i,push(1,r,w))
    try:
        for x in todo:
            s,l,r=x;v=t[s]-1
            if v<0:return None
            d=v%2;w=v//2%2;u,y=(l,r) if d else (r,l);j=push(1-d,u,w);es=E[1-d].setdefault(j,set());e=(w,u)
            if e not in es:
                es.add(e)
                for z in waiting[1-d][j]:succ(z,e)
            waiting[d][y].append(x)
            for e in E[d].get(y,()):succ(x,e)
    except ValueError:return None
    return {'params':params,'edges':[[sorted(E[d].get(i,())) for i in range(len(objs[d]))] for d in (0,1)],'pushes':[[[P[d].get((i,w),0) for w in (0,1)] for i in range(len(objs[d]))] for d in (0,1)],'states':sorted(seen)}
def main():
    ts=json.load(open('ngram.json'))['fail'];found=[];failed=[]
    options=sorted(itertools.product((0,1),range(1,5),range(1,5),range(1,9)),key=lambda x:(x[3]*(x[1]+x[2]),-x[0]))
    for i,t in enumerate(ts):
        if t==[8,9,11,6,17,13,11,-1,2,23,3,23]:continue
        for p in options:
            c=run(t,(p,p))
            if c is not None:
                found.append([t,c]);print(i,'SOLVED',p,len(c['states']),flush=True);break
        else:failed.append(t);print(i,'fail',flush=True)
        json.dump({'certs':found,'fail':failed,'next':i+1},open('rle.json','w'))
if __name__=='__main__':main()
