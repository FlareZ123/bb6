import json,itertools,collections
def run(t,params,limit=15000):
    objs=[[(0,())],[(0,())]];ids=[{(0,()):0},{(0,()):0}];E=[{0:{(0,0)}},{0:{(0,0)}}];P=[{},{}];waiting=[collections.defaultdict(list),collections.defaultdict(list)];todo=[(0,0,0)];seen=set(todo)
    def push(d,i,w):
        key=(i,w)
        if key in P[d]:return P[d][key]
        mode,cap,mod,n=params[d];b,rs=objs[d][i];a=w^((b>>(mode-1))&1) if mode else w
        if not rs and a==0:rs2=()
        elif rs and rs[0][0]==a:
            k=rs[0][1];rs2=((a,cap+1 if k==cap+mod else k+1),)+rs[1:]
        else:rs2=(((a,1),)+rs)[:n]
        z=(((b<<1)|w)&((1<<mode)-1),rs2)
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
# mode is a lag, zero meaning ordinary RLE. Invariant data retain actual pushed bits.
