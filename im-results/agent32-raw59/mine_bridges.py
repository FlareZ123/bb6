from dataclasses import dataclass
from mine_packed_sweeps import compress, trace, bits

@dataclass(frozen=True)
class Bridge:
    q:int; next:int; li:tuple; ri:tuple; lo:tuple; ro:tuple; ls:bool; rs:bool; cost:int

def bridge(moves,states,reads,i,n):
    d=lo=hi=0
    for x in reads[i:i+n]:
        d+=1 if moves[x][1] else -1
        lo=min(lo,d);hi=max(hi,d)
    l=1-lo;r=hi
    q,ll,lb,rl,rb=states[i];qq,LL,LB,RR,RB=states[i+n]
    ls=l>ll;rs=r>rl
    l=min(l,ll);r=min(r,rl)
    ol=LL if ls else l+d;orr=RR if rs else r-d
    if ol<0 or orr<0 or ol>LL or orr>RR:return None
    if lb>>l!=LB>>ol or rb>>r!=RB>>orr:return None
    if ll-l!=LL-ol or rl-r!=RR-orr:return None
    b=Bridge(q,qq,bits(lb,l),bits(rb,r),bits(LB,ol),bits(RB,orr),ls,rs,n)
    L=list(b.li);R=list(b.ri)
    for _ in range(n):
        if not L and not ls:return None
        w,right,q=moves[2*q+(L[0] if L else 0)]
        if right:
            if not R and not rs:return None
            L=[R.pop(0) if R else 0,w]+L[1:]
        else:L=L[1:];R=[w]+R
    if q!=b.next or tuple(L)!=b.lo or tuple(R)!=b.ro:return None
    return b

def compress_bridges(table,steps):
    rules,actions,end=compress(table,steps)
    moves,states,reads=trace(table,steps)
    bridges=[];result=[];i=0
    for rule,n,z in actions:
        if rule is not None:
            result.append(('sweep',rule,n,z));i+=rules[rule].cost*n;continue
        j=i+n
        while i<j:
            b=None
            for k in range(j-i,1,-1):
                b=bridge(moves,states,reads,i,k)
                if b is not None:break
            if b is None:
                result.append(('raw',None,1,states[i+1]));i+=1
            else:
                if b not in bridges:bridges.append(b)
                i+=b.cost;result.append(('bridge',bridges.index(b),b.cost,states[i]))
    assert i==steps and result[-1][-1]==end
    return rules,bridges,result,end
