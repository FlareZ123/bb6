from dataclasses import dataclass
def parse_table(table: str):
    s = table.replace('_', '')
    assert len(s) == 36
    return [None if s[i:i+3] == '---' else
            (int(s[i]), s[i+1] == 'R', ord(s[i+2])-65)
            for i in range(0, 36, 3)]

@dataclass(frozen=True)
class Rule:
    q:int; right:bool; lp:tuple; rp:tuple; inp:tuple; out:tuple; cost:int

def trace(table, steps):
    moves=parse_table(table); q=ll=lb=rl=rb=0; states=[(q,ll,lb,rl,rb)]; reads=[]
    for t in range(steps):
        i=2*q+(lb&1 if ll else 0); reads.append(i)
        w,right,q=moves[i]
        if right:
            ll=max(ll-1,0)+2;lb=(lb>>1)*4+2*w+(rb&1 if rl else 0);rl=max(rl-1,0);rb>>=1
        else:
            ll=max(ll-1,0);lb>>=1;rl+=1;rb=rb*2+w
        states.append((q,ll,lb,rl,rb))
    return moves,states,reads

def bits(x,n):return tuple((x>>i)&1 for i in range(n))
def value(x):return sum(b<<i for i,b in enumerate(x))
def symvalid(rule,moves):
    q=rule.q; L=list(rule.lp+(rule.inp if not rule.right else ()));R=list(rule.rp+(rule.inp if rule.right else ()))
    for _ in range(rule.cost):
        if not L:return False
        mv=moves[2*q+L[0]]
        if mv is None:return False
        w,right,q=mv
        if right:
            if not R:return False
            L=[R.pop(0),w]+L[1:]
        else:
            L=L[1:];R=[w]+R
    return q==rule.q and tuple(L)==rule.lp+(rule.out if rule.right else ()) and tuple(R)==rule.rp+(rule.out if not rule.right else ())

def derive(moves,a,b,k):
    q,ll,lb,rl,rb=a; qq,LL,LB,RR,RB=b
    if q!=qq or ll+rl!=LL+RR:return None
    d=LL-ll
    if not d:return None
    d0=abs(d)
    for total in range(17):
      for l in range(total+1):
        r=total-l
        if l>min(ll,LL) or r>min(rl,RR):continue
        lp=bits(lb,l);rp=bits(rb,r)
        if lp!=bits(LB,l) or rp!=bits(RB,r):continue
        if d>0:
            if LB>>(l+d)!=lb>>l or rb>>(r+d)!=RB>>r:continue
            rule=Rule(q,True,lp,rp,bits(rb>>r,d),bits(LB>>l,d),k)
        else:
            if lb>>(l+d0)!=LB>>l or RB>>(r+d0)!=rb>>r:continue
            rule=Rule(q,False,lp,rp,bits(lb>>l,d0),bits(RB>>r,d0),k)
        if symvalid(rule,moves):return rule
    return None

def rule_apply(r,a,n):
    q,ll,lb,rl,rb=a
    if q!=r.q:return None
    lp,rp=r.lp,r.rp
    il=lp+(() if r.right else r.inp*n);ir=rp+(r.inp*n if r.right else ())
    ol=lp+(r.out*n if r.right else ());orr=rp+(() if r.right else r.out*n)
    if len(il)>ll or len(ir)>rl or bits(lb,len(il))!=il or bits(rb,len(ir))!=ir:return None
    return (q,ll-len(il)+len(ol),value(ol)+((lb>>len(il))<<len(ol)),rl-len(ir)+len(orr),value(orr)+((rb>>len(ir))<<len(orr)))

def compress(table,steps):
    moves,states,reads=trace(table,steps);rules=[];actions=[];i=0;raw=0;cache={}
    while i<steps:
        best=None
        for k in range(1,min(24,(steps-i)//3)+1):
            seq=tuple(reads[i:i+k])
            if reads[i+k:i+2*k]!=list(seq) or reads[i+2*k:i+3*k]!=list(seq):continue
            if states[i][0]!=states[i+k][0]:continue
            n=3
            while reads[i+n*k:i+(n+1)*k]==list(seq):n+=1
            if best is not None and n*k<=best[0]:continue
            candidates=cache.get(seq,[])
            rule=next((r for r in candidates if rule_apply(r,states[i],n)==states[i+n*k]),None)
            if rule is None:
                rule=derive(moves,states[i],states[i+k],k)
                if rule is None:continue
                if rule not in candidates:cache.setdefault(seq,[]).append(rule)
                if rule_apply(rule,states[i],n)!=states[i+n*k]:continue
            best=(n*k,rule,n)
        if best is None:
            raw+=1;i+=1
            if raw==128:actions.append((None,raw,states[i]));raw=0
        else:
            if raw:actions.append((None,raw,states[i]));raw=0
            cost,rule,n=best
            if rule not in rules:rules.append(rule)
            i+=cost;actions.append((rules.index(rule),n,states[i]))
    if raw:actions.append((None,raw,states[i]))
    assert sum(n if r is None else rules[r].cost*n for r,n,_ in actions)==steps
    return rules,actions,states[-1]

